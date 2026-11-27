import EF1FPO.Prices
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Semantic invariants for deterministic leaf elimination and band merging. -/

set_option autoImplicit false

namespace EF1FPO.Instance

variable (I : Instance)

structure Roster where
  active : Finset I.Agent
  assigned : Finset I.Good
  owner : I.Allocation

namespace Roster

def take (s : I.Roster) (i : I.Agent) (g : I.Good) : I.Roster :=
  ⟨s.active, insert g s.assigned, Function.update s.owner g i⟩

def remove (s : I.Roster) (i : I.Agent) : I.Roster :=
  ⟨s.active.erase i, s.assigned, s.owner⟩

def isLive (w : I.Weights) (s : I.Roster) (i : I.Agent) (g : I.Good) : Prop :=
  i ∈ s.active ∧ g ∉ s.assigned ∧ I.IsHighestBidder w i g

def agentLeaf (w : I.Weights) (s : I.Roster) (i : I.Agent) (g : I.Good) : Prop :=
  s.isLive I w i g ∧ ∀ f : I.Good, s.isLive I w i f → f = g

noncomputable def spending (w : I.Weights) (s : I.Roster) (i : I.Agent) : ℝ := by
  classical
  exact I.bundlePrice w (s.assigned.filter (fun g => s.owner g = i))

def lowerInvariant (w : I.Weights) (s : I.Roster) : Prop :=
  ∃ C : I.Allocation, I.IsSupported w C ∧ I.LowerBand w C 1 ∧
    (∀ g ∈ s.assigned, C g = s.owner g) ∧
    ∀ g ∉ s.assigned, C g ∈ s.active

def shared (w : I.Weights) (g : I.Good) : Prop :=
  ∃ i j : I.Agent, i ≠ j ∧ I.IsHighestBidder w i g ∧ I.IsHighestBidder w j g

def upperInvariant (w : I.Weights) (s : I.Roster) : Prop :=
  (∀ g ∈ s.assigned, I.IsHighestBidder w (s.owner g) g) ∧
  (∀ g ∈ s.assigned, shared I w g → s.owner g ∉ s.active) ∧
  (∀ g ∈ s.assigned, ∀ f ∈ s.assigned, shared I w g → shared I w f →
    s.owner g = s.owner f → g = f) ∧
  ∀ g ∉ s.assigned, ∃ i j : I.Agent, i ≠ j ∧ s.isLive I w i g ∧ s.isLive I w j g

theorem exists_agent_leaf (w : I.Weights) (s : I.Roster) (hF : I.IsForest w)
    (hMissing : ∃ g, g ∉ s.assigned)
    (hTwo : ∀ g ∉ s.assigned, ∃ i j : I.Agent, i ≠ j ∧ s.isLive I w i g ∧ s.isLive I w j g) :
    ∃ i g, s.agentLeaf I w i g := by
  classical
  let live (z : I.Agent ⊕ I.Good) : Prop :=
    match z with
    | .inl i => i ∈ s.active
    | .inr g => g ∉ s.assigned
  let V := {z // live z}
  let G : SimpleGraph V := (I.highestBidderGraph w).induce {z | live z}
  obtain ⟨g, hg⟩ := hMissing
  obtain ⟨i, _, _, hi, _⟩ := hTwo g hg
  let startGood : V := ⟨Sum.inr g, hg⟩
  let startAgent : V := ⟨Sum.inl i, hi.1⟩
  have hStart : G.Adj startAgent startGood := by
    change (I.highestBidderGraph w).Adj (Sum.inl i) (Sum.inr g)
    simpa [Instance.highestBidderGraph] using hi.2.2
  let C := G.connectedComponentMk startGood
  have hgC : startGood ∈ C.supp := by simp [C]
  have hiC : startAgent ∈ C.supp := C.mem_supp_of_adj_mem_supp hgC hStart.symm
  letI : Nontrivial C := ⟨⟨⟨startGood, hgC⟩, ⟨startAgent, hiC⟩, by
    intro he
    have h := congrArg (fun v : C => v.val.val) he
    cases h⟩⟩
  have hAcyclic : G.IsAcyclic := hF.induce _
  obtain ⟨a, ha⟩ := (hAcyclic.isTree_connectedComponent C).exists_vert_degree_one_of_nontrivial
  obtain ⟨b, hab, hUniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp ha
  have allNbr (v : V) (he : G.Adj a.val v) : v.val = b.val.val := by
    have hv := C.mem_supp_of_adj_mem_supp a.property he
    exact congrArg (fun z : C => z.val.val) (hUniq ⟨v, hv⟩ he)
  have liveA : live a.val.val := a.val.property
  rcases hA : a.val.val with aI | aG <;> rw [hA] at liveA
  · have hab' : (I.highestBidderGraph w).Adj a.val.val b.val.val := hab
    rw [hA] at hab'
    have liveB : live b.val.val := b.val.property
    rcases hB : b.val.val with bI | bG <;> rw [hB] at hab' liveB
    · simp [Instance.highestBidderGraph] at hab'
    · have bidder : I.IsHighestBidder w aI bG := by
        simpa [Instance.highestBidderGraph] using hab'
      refine ⟨aI, bG, ⟨liveA, liveB, bidder⟩, ?_⟩
      intro f hf
      let endF : V := ⟨Sum.inr f, hf.2.1⟩
      have hadj : G.Adj a.val endF := by
        change (I.highestBidderGraph w).Adj a.val.val (Sum.inr f)
        rw [hA]
        simpa [Instance.highestBidderGraph] using hf.2.2
      exact Sum.inr.inj (α := I.Agent) ((allNbr endF hadj).trans hB)
  · obtain ⟨k, l, hkl, hk, hl⟩ := hTwo aG liveA
    have clash (i : I.Agent) (hi : s.isLive I w i aG) : Sum.inl i = b.val.val := by
      let endI : V := ⟨Sum.inl i, hi.1⟩
      have hadj : G.Adj endI a.val := by
        change (I.highestBidderGraph w).Adj (Sum.inl i) a.val.val
        rw [hA]
        simpa [Instance.highestBidderGraph] using hi.2.2
      exact allNbr endI hadj.symm
    exact (hkl (Sum.inl.inj (β := I.Good) ((clash k hk).trans (clash l hl).symm))).elim

theorem take_only_bidder (w : I.Weights) (s : I.Roster) (i : I.Agent) (g : I.Good)
    (hC : s.lowerInvariant I w) (he : s.isLive I w i g)
    (honly : ∀ j, s.isLive I w j g → j = i) :
    (s.take I i g).lowerInvariant I w := by
  obtain ⟨C, hS, hL, hAgree, hLive⟩ := hC
  have hOwn := honly (C g) ⟨hLive g he.2.1, he.2.1, hS g⟩
  refine ⟨C, hS, hL, ?_, ?_⟩
  · intro f hf
    change f ∈ insert g s.assigned at hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · simpa [take] using hOwn
    · have hne : f ≠ g := fun h => he.2.1 (h ▸ hf)
      simpa [take, Function.update_of_ne hne] using hAgree f hf
  · intro f hf
    exact hLive f (fun hf' => hf (Finset.mem_insert_of_mem hf'))

theorem take_deficient_leaf (w : I.Weights) (s : I.Roster) (i : I.Agent) (g : I.Good)
    (hC : s.lowerInvariant I w) (he : s.agentLeaf I w i g) (hSpend : s.spending I w i < 1) :
    ((s.take I i g).remove I i).lowerInvariant I w := by
  classical
  obtain ⟨C, hS, hL, hAgree, hLive⟩ := hC
  have hLeft (f : I.Good) (hf : f ∉ s.assigned) (hfOwner : C f = i) : f = g := by
    apply he.2
    have hF : s.isLive I w (C f) f := ⟨hLive f hf, hf, hS f⟩
    rwa [hfOwner] at hF
  have hOwn : C g = i := by
    by_contra hne
    have hBundle : FairDivision.bundle C i = s.assigned.filter (fun f => s.owner f = i) := by
      ext f
      simp only [FairDivision.bundle, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hOwn
        have hf : f ∈ s.assigned := by
          by_contra hf
          exact hne ((hLeft f hf hOwn) ▸ hOwn)
        exact ⟨hf, (hAgree f hf).symm.trans hOwn⟩
      · rintro ⟨hf, ho⟩
        exact (hAgree f hf).trans ho
    have h := hL i
    rw [hBundle] at h
    exact (not_lt_of_ge h) hSpend
  refine ⟨C, hS, hL, ?_, ?_⟩
  · intro f hf
    change f ∈ insert g s.assigned at hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · simpa [take, remove] using hOwn
    · have hne : f ≠ g := fun h => he.1.2.1 (h ▸ hf)
      simpa [take, remove, Function.update_of_ne hne] using hAgree f hf
  · intro f hf
    change f ∉ insert g s.assigned at hf
    change C f ∈ s.active.erase i
    have hPending : f ∉ s.assigned := fun hf' => hf (Finset.mem_insert_of_mem hf')
    exact Finset.mem_erase.mpr ⟨fun h => hf (Finset.mem_insert.mpr (Or.inl (hLeft f hPending h))),
      hLive f hPending⟩

theorem remove_satisfied_leaf (w : I.Weights) (s : I.Roster) (i j : I.Agent) (g : I.Good)
    (hw : I.Positive w) (hC : s.lowerInvariant I w) (he : s.agentLeaf I w i g)
    (hJ : s.isLive I w j g) (hne : j ≠ i) (hSpend : 1 ≤ s.spending I w i) :
    (s.remove I i).lowerInvariant I w := by
  classical
  obtain ⟨C, hS, hL, hAgree, hLive⟩ := hC
  have onlyLeft (f : I.Good) (hf : f ∉ s.assigned) (hfOwner : C f = i) : f = g := by
    apply he.2
    have hF : s.isLive I w (C f) f := ⟨hLive f hf, hf, hS f⟩
    rwa [hfOwner] at hF
  by_cases hOwn : C g = i
  · let D := Function.update C g j
    have orig (f : I.Good) (hf : f ≠ g) : D f = C f := Function.update_of_ne hf j C
    have hS' : I.IsSupported w D := by
      intro f
      by_cases hf : f = g
      · subst f
        simpa [D] using hJ.2.2
      · rw [orig f hf]
        exact hS f
    have hAgree' (f : I.Good) (hf : f ∈ s.assigned) : D f = s.owner f :=
      (orig f (fun eq => hJ.2.1 (eq ▸ hf))).trans (hAgree f hf)
    refine ⟨D, hS', ?_, hAgree', ?_⟩
    · intro k
      have price_mono {S T : Finset I.Good} (h : S ⊆ T) : I.bundlePrice w S ≤ I.bundlePrice w T :=
        Finset.sum_le_sum_of_subset_of_nonneg h (fun f _ _ => I.price_nonneg w hw f)
      by_cases hk : k = i
      · subst k
        apply hSpend.trans
        apply price_mono
        intro f hf
        obtain ⟨hDone, hfOwn⟩ := Finset.mem_filter.mp hf
        simpa [FairDivision.bundle] using (hAgree' f hDone).trans hfOwn
      · apply (hL k).trans
        apply price_mono
        intro f hf
        have hfC : C f = k := by simpa [FairDivision.bundle] using hf
        have hf' : f ≠ g := by
          rintro rfl
          exact hk (hfC.symm.trans hOwn)
        simpa [FairDivision.bundle, orig f hf'] using hfC
    · intro f hf
      change D f ∈ s.active.erase i
      by_cases hfg : f = g
      · subst f
        simpa [D, hne] using hJ.1
      · rw [orig f hfg]
        exact Finset.mem_erase.mpr ⟨fun ho => hfg (onlyLeft f hf ho), hLive f hf⟩
  · refine ⟨C, hS, hL, hAgree, ?_⟩
    intro f hf
    exact Finset.mem_erase.mpr ⟨fun ho => hOwn ((onlyLeft f hf ho) ▸ ho), hLive f hf⟩

theorem lower_complete (w : I.Weights) (s : I.Roster) (hC : s.lowerInvariant I w)
    (hAll : s.assigned = Finset.univ) :
    I.IsSupported w s.owner ∧ I.LowerBand w s.owner 1 := by
  obtain ⟨C, hS, hL, hAgree, _⟩ := hC
  have hEq : C = s.owner := funext (fun g => hAgree g (by simp [hAll]))
  exact hEq ▸ ⟨hS, hL⟩

theorem upper_start (w : I.Weights) (s : I.Roster) (hAll : s.active = Finset.univ)
    (hAssigned : ∀ g, g ∈ s.assigned ↔ ¬ shared I w g)
    (hGood : ∀ g ∈ s.assigned, I.IsHighestBidder w (s.owner g) g) :
    s.upperInvariant I w := by
  classical
  refine ⟨hGood, ?_, ?_, ?_⟩
  · intro g hg hs
    exact ((hAssigned g).mp hg hs).elim
  · intro g hg f hf hs
    exact ((hAssigned g).mp hg hs).elim
  · intro g hg
    have hs : shared I w g := by
      by_contra hn
      exact hg ((hAssigned g).mpr hn)
    obtain ⟨i, j, hne, hi, hj⟩ := hs
    exact ⟨i, j, hne, ⟨by simp [hAll], hg, hi⟩, ⟨by simp [hAll], hg, hj⟩⟩

theorem upper_take_leaf (w : I.Weights) (s : I.Roster) (i : I.Agent) (g : I.Good)
    (hU : s.upperInvariant I w) (he : s.agentLeaf I w i g) :
    ((s.take I i g).remove I i).upperInvariant I w := by
  let t := (s.take I i g).remove I i
  have hG : g ∉ s.assigned := he.1.2.1
  have insert_cases (f : I.Good) (hf : f ∈ t.assigned) : f = g ∨ f ∈ s.assigned :=
    Finset.mem_insert.mp hf
  have old (f : I.Good) (hf : f ∈ s.assigned) : t.owner f = s.owner f := by
    have hne : f ≠ g := fun h => hG (h ▸ hf)
    exact Function.update_of_ne hne i s.owner
  have hNew : t.owner g = i := by simp [t, take, remove]
  have noOld (f : I.Good) (hf : f ∈ s.assigned) (hs : shared I w f) : s.owner f ≠ i :=
    fun heq => hU.2.1 f hf hs (heq ▸ he.1.1)
  have inactive : i ∉ t.active := Finset.notMem_erase _ _
  change t.upperInvariant I w
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf
    rcases insert_cases f hf with rfl | hf
    · rw [hNew]
      exact he.1.2.2
    · rw [old f hf]
      exact hU.1 f hf
  · intro f hf hS
    rcases insert_cases f hf with rfl | hf
    · rwa [hNew]
    · rw [old f hf]
      exact fun h => hU.2.1 f hf hS (Finset.mem_of_mem_erase h)
  · intro a ha b hb hSa hSb heq
    rcases insert_cases a ha with haEq | haOld
    · subst a
      rcases insert_cases b hb with hbEq | hbOld
      · exact hbEq.symm
      · rw [hNew, old b hbOld] at heq
        exact ((noOld b hbOld hSb) heq.symm).elim
    · rcases insert_cases b hb with hbEq | hbOld
      · subst b
        rw [old a haOld, hNew] at heq
        exact ((noOld a haOld hSa) heq).elim
      · rw [old a haOld, old b hbOld] at heq
        exact hU.2.2.1 a haOld b hbOld hSa hSb heq
  · intro f hf
    change f ∉ insert g s.assigned at hf
    have hf' : f ∉ s.assigned := fun hm => hf (Finset.mem_insert_of_mem hm)
    have hfg : f ≠ g := fun hm => hf (Finset.mem_insert.mpr (Or.inl hm))
    obtain ⟨a, b, hne, ha, hb⟩ := hU.2.2.2 f hf'
    have lift (a : I.Agent) (ha : s.isLive I w a f) : t.isLive I w a f := by
      have hAi : a ≠ i := by
        rintro rfl
        exact hfg (he.2 f ha)
      exact ⟨Finset.mem_erase.mpr ⟨hAi, ha.1⟩, hf, ha.2.2⟩
    exact ⟨a, b, hne, lift a ha, lift b hb⟩

theorem upper_complete (w : I.Weights) (s : I.Roster) (hw : I.Positive w)
    (hForced : I.ForcedFeasible w) (hU : s.upperInvariant I w)
    (hAll : s.assigned = Finset.univ) :
    I.IsSupported w s.owner ∧ I.UpperBand w s.owner 1 := by
  classical
  have assigned (g : I.Good) : g ∈ s.assigned := by rw [hAll]; exact Finset.mem_univ g
  have hA : I.IsSupported w s.owner := fun g => hU.1 g (assigned g)
  refine ⟨hA, fun i => ?_⟩
  let S := FairDivision.bundle s.owner i
  have getOwner (g : I.Good) (hg : g ∈ S) : s.owner g = i := by
    simpa [S, FairDivision.bundle] using hg
  have eachForced (g : I.Good) (hg : g ∈ S) (hn : ¬ shared I w g) : g ∈ I.forcedGoods w i := by
    have hi : I.IsHighestBidder w i g := getOwner g hg ▸ hA g
    simp only [forcedGoods, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hji
    refine lt_of_le_of_ne (hi j) (fun heq => hn ?_)
    exact ⟨j, i, hji, fun k => (hi k).trans heq.ge, hi⟩
  have hsum {T : Finset I.Good} (hT : T ⊆ I.forcedGoods w i) : I.bundlePrice w T ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hT (fun g _ _ => I.price_nonneg w hw g)).trans (hForced i)
  by_cases ht : ∃ g ∈ S, shared I w g
  · obtain ⟨g, hg, hgshared⟩ := ht
    refine (I.trim_le_delete w S hg).trans (hsum ?_)
    intro f hf
    obtain ⟨hne, hfS⟩ := Finset.mem_erase.mp hf
    refine eachForced f hfS (fun hfshared => hne ?_)
    exact hU.2.2.1 f (assigned f) g (assigned g) hfshared hgshared
      ((getOwner f hfS).trans (getOwner g hg).symm)
  · by_cases hS : S.Nonempty
    · obtain ⟨g, hg⟩ := hS
      refine (I.trim_le_delete w S hg).trans (hsum (fun f hf => ?_))
      have hfS := Finset.mem_of_mem_erase hf
      exact eachForced f hfS (fun hs => ht ⟨f, hfS, hs⟩)
    · change I.trim w S ≤ 1
      simp [trim, hS]

theorem transfer_chosen (w : I.Weights) (C A : I.Allocation) (g : I.Good)
    (hw : I.Positive w) (hC : I.IsSupported w C) (hA : I.IsSupported w A)
    (hU : I.UpperBand w A 1) (hChange : A g ≠ C g)
    (hSpend : I.bundlePrice w (FairDivision.bundle A (C g)) < 1) :
    let A' := Function.update A g (C g)
    I.IsSupported w A' ∧ I.UpperBand w A' 1 ∧
      (I.disagreement A' C).card + 1 = (I.disagreement A C).card := by
  let i := C g
  have hcg : C g = i := rfl
  have hag : A g ≠ i := hChange
  let A' := Function.update A g (C g)
  change I.IsSupported w A' ∧ I.UpperBand w A' 1 ∧
    (I.disagreement A' C).card + 1 = (I.disagreement A C).card
  refine ⟨?_, ?_, ?_⟩
  · intro f
    by_cases hf : f = g
    · subst f
      simpa [A'] using hC g
    · simpa [A', Function.update_of_ne hf] using hA f
  · intro j
    by_cases hji : j = i
    · subst j
      have hmember : g ∈ FairDivision.bundle A' i := by simp [FairDivision.bundle, A', hcg]
      have herase : (FairDivision.bundle A' i).erase g = FairDivision.bundle A i := by
        ext f
        by_cases hf : f = g
        · subst f
          simp [FairDivision.bundle, hag]
        · simp [FairDivision.bundle, A', hf]
      have htrim := I.trim_le_delete w (FairDivision.bundle A' i) hmember
      rw [herase] at htrim
      exact htrim.trans hSpend.le
    · have hsub : FairDivision.bundle A' j ⊆ FairDivision.bundle A j := by
        intro f hf
        by_cases heq : f = g
        · subst f
          exact False.elim (hji (by simpa [FairDivision.bundle, A', hcg, eq_comm] using hf))
        · simpa [FairDivision.bundle, A', Function.update_of_ne heq] using hf
      exact (I.trim_mono w hw hsub).trans (hU j)
  · have herase : I.disagreement A' C = (I.disagreement A C).erase g := by
      ext f
      by_cases hf : f = g
      · subst f
        simp [disagreement, A']
      · simp [disagreement, A', hf]
    rw [herase]
    exact Finset.card_erase_add_one (by simp [disagreement, hcg, hag])

end Roster
end EF1FPO.Instance
