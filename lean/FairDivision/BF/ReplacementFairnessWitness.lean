import FairDivision.BF.ReplacementCompletionExtensions

/-!
# From the manuscript's extended EF[1,1] allocation to one replacement

Nondecreasing worst completions restore the deletion from the envious
bundle. Nonincreasing best completions restore the deletion from the rival
bundle. Original strict envy forces the other deletion to be a singleton.
An attained completion then supplies the replacement item, which cannot be
the deleted item. Only original q-item valuation inputs occur below.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.ReplacementFairness

open FairDivision
open scoped Classical

/-- Definition `replacement-fairness`: replacement changes the envied bundle
only. The original valuation has no inputs outside q-item bundles. -/
def IsEnviedReplacement {n m q : ℕ} (v : Fin n→QBundle m q→ℝ) (A : Allocation n m) : Prop :=
  ∃hSize : ∀i : Fin n,(bundle A i).card=q,
    ∀i j : Fin n,v i ⟨bundle A i,hSize i⟩<v i ⟨bundle A j,hSize j⟩→
      ∃b∈bundle A j,∃g : Fin m,g∉bundle A j ∧
        ∃T : QBundle m q,T.1=insert g ((bundle A j).erase b) ∧
          v i T≤v i ⟨bundle A i,hSize i⟩

/-- Definition `own-replacement-fairness`: replacement changes the envious
bundle only, leaving the rival's q-item comparison bundle unchanged. -/
def IsOwnReplacement {n m q : ℕ} (v : Fin n→QBundle m q→ℝ) (A : Allocation n m) : Prop :=
  ∃hSize : ∀i : Fin n,(bundle A i).card=q,
    ∀i j : Fin n,v i ⟨bundle A i,hSize i⟩<v i ⟨bundle A j,hSize j⟩→
      ∃a∈bundle A i,∃g : Fin m,g∉bundle A i ∧
        ∃T : QBundle m q,T.1=insert g ((bundle A i).erase a) ∧
          v i ⟨bundle A j,hSize j⟩≤v i T

/-- The literal one-item replacement as an input to the original q-item
valuation. Membership of the outgoing item and nonmembership of the incoming
item prove the cardinality; there is no extension of the original valuation
in this interpreting definition. -/
def replaceOne {m q : ℕ} (B : QBundle m q) (b : Fin m) (hb : b∈B.1)
    (g : Fin m) (hg : g∉B.1) : QBundle m q :=
  ⟨insert g (B.1.erase b),by
    have hgErase : g∉B.1.erase b := fun h=>hg ((Finset.erase_subset _ _) h)
    have hPositive : 0<q := by
      rw [←B.2]
      exact Finset.card_pos.mpr ⟨b,hb⟩
    rw [Finset.card_insert_of_notMem hgErase,Finset.card_erase_of_mem hb,B.2]
    omega⟩

@[simp] theorem replaceOne_val {m q : ℕ} (B : QBundle m q)
    (b : Fin m) (hb : b∈B.1) (g : Fin m) (hg : g∉B.1) :
    (replaceOne B b hb g hg).1=insert g (B.1.erase b) := rfl

/-- At q=1, replacement really compares the singleton incoming item. The
outgoing set is empty, so this boundary case requires no extra item in the
original bundle. -/
theorem replaceOne_one_val {m : ℕ} (B : QBundle m 1)
    (b : Fin m) (hb : b∈B.1) (g : Fin m) (hg : g∉B.1) :
    (replaceOne B b hb g hg).1={g} := by
  have hErase : B.1.erase b=∅ := by
    apply Finset.card_eq_zero.mp
    rw [Finset.card_erase_of_mem hb,B.2]
  change insert g (B.1.erase b)={g}
  simp only [hErase,Finset.insert_empty]

/-- Direct reading of the paper's q-item inequality. The existential bundle
in the public definition is uniquely the displayed size-preserving
replacement, including q=1. -/
theorem isEnviedReplacement_iff_replaceOne {n m q : ℕ}
    (v : Fin n→QBundle m q→ℝ) (A : Allocation n m)
    (hSize : ∀i : Fin n,(bundle A i).card=q) :
    IsEnviedReplacement v A ↔
      ∀i j : Fin n,v i ⟨bundle A i,hSize i⟩<v i ⟨bundle A j,hSize j⟩→
        ∃b,∃hb : b∈bundle A j,∃g,∃hg : g∉bundle A j,
          v i (replaceOne ⟨bundle A j,hSize j⟩ b hb g hg)≤
            v i ⟨bundle A i,hSize i⟩ := by
  constructor
  · rintro ⟨hSize',hFair⟩ i j hEnvy
    obtain ⟨b,hb,g,hg,T,hT,hValue⟩:=hFair i j hEnvy
    refine ⟨b,hb,g,hg,?_⟩
    have hEqual : T=replaceOne ⟨bundle A j,hSize j⟩ b hb g hg :=
      Subtype.ext hT
    rw [←hEqual]
    exact hValue
  · intro hFair
    refine ⟨hSize,?_⟩
    intro i j hEnvy
    obtain ⟨b,hb,g,hg,hValue⟩:=hFair i j hEnvy
    exact ⟨b,hb,g,hg,replaceOne ⟨bundle A j,hSize j⟩ b hb g hg,rfl,hValue⟩

/-- Direct reading of own-bundle replacement. Only the own q-bundle changes;
the rival bundle remains the original input to its valuation. -/
theorem isOwnReplacement_iff_replaceOne {n m q : ℕ}
    (v : Fin n→QBundle m q→ℝ) (A : Allocation n m)
    (hSize : ∀i : Fin n,(bundle A i).card=q) :
    IsOwnReplacement v A ↔
      ∀i j : Fin n,v i ⟨bundle A i,hSize i⟩<v i ⟨bundle A j,hSize j⟩→
        ∃a,∃ha : a∈bundle A i,∃g,∃hg : g∉bundle A i,
          v i ⟨bundle A j,hSize j⟩≤
            v i (replaceOne ⟨bundle A i,hSize i⟩ a ha g hg) := by
  constructor
  · rintro ⟨hSize',hFair⟩ i j hEnvy
    obtain ⟨a,ha,g,hg,T,hT,hValue⟩:=hFair i j hEnvy
    refine ⟨a,ha,g,hg,?_⟩
    have hEqual : T=replaceOne ⟨bundle A i,hSize i⟩ a ha g hg :=
      Subtype.ext hT
    rw [←hEqual]
    exact hValue
  · intro hFair
    refine ⟨hSize,?_⟩
    intro i j hEnvy
    obtain ⟨a,ha,g,hg,hValue⟩:=hFair i j hEnvy
    exact ⟨a,ha,g,hg,replaceOne ⟨bundle A i,hSize i⟩ a ha g hg,rfl,hValue⟩

/-- Completeness of the allocation identifies the actual owner of every
incoming item. It lies in a different bundle from the one being modified;
there is deliberately no assertion that it belongs to the other comparison
bundle. -/
theorem replacement_item_other_owner {n m : ℕ} (A : Allocation n m)
    (i : Fin n) (g : Fin m) (hg : g∉bundle A i) :
    A g≠i ∧ g∈bundle A (A g) := by
  constructor
  · intro hOwner
    exact hg (by simp only [bundle,Finset.mem_filter,Finset.mem_univ,true_and,hOwner])
  · simp only [bundle,Finset.mem_filter,Finset.mem_univ,true_and]

/-- The envied-bundle witness together with its actual incoming owner. This
spells out the manuscript's “any other agent's bundle” without replacing the
hypothetical comparison by a simultaneous exchange. -/
theorem enviedReplacement_witness_with_owner {n m q : ℕ}
    (v : Fin n→QBundle m q→ℝ) (A : Allocation n m)
    (hSize : ∀i : Fin n,(bundle A i).card=q) (hFair : IsEnviedReplacement v A)
    (i j : Fin n) (hEnvy : v i ⟨bundle A i,hSize i⟩<v i ⟨bundle A j,hSize j⟩) :
    ∃b,∃hb : b∈bundle A j,∃g,∃hg : g∉bundle A j,
      A g≠j ∧ g∈bundle A (A g) ∧
        v i (replaceOne ⟨bundle A j,hSize j⟩ b hb g hg)≤v i ⟨bundle A i,hSize i⟩ := by
  obtain ⟨b,hb,g,hg,hValue⟩:=(isEnviedReplacement_iff_replaceOne v A hSize).mp hFair i j hEnvy
  obtain ⟨hOwner,hBelongs⟩:=replacement_item_other_owner A j g hg
  exact ⟨b,hb,g,hg,hOwner,hBelongs,hValue⟩

/-- The own-bundle witness has an actual owner different from the envious
agent; that owner need not be the envied agent. The rival valuation input
remains unchanged even if it happens to own the incoming item. -/
theorem ownReplacement_witness_with_owner {n m q : ℕ}
    (v : Fin n→QBundle m q→ℝ) (A : Allocation n m)
    (hSize : ∀i : Fin n,(bundle A i).card=q) (hFair : IsOwnReplacement v A)
    (i j : Fin n) (hEnvy : v i ⟨bundle A i,hSize i⟩<v i ⟨bundle A j,hSize j⟩) :
    ∃a,∃ha : a∈bundle A i,∃g,∃hg : g∉bundle A i,
      A g≠i ∧ g∈bundle A (A g) ∧
        v i ⟨bundle A j,hSize j⟩≤v i (replaceOne ⟨bundle A i,hSize i⟩ a ha g hg) := by
  obtain ⟨a,ha,g,hg,hValue⟩:=(isOwnReplacement_iff_replaceOne v A hSize).mp hFair i j hEnvy
  obtain ⟨hOwner,hBelongs⟩:=replacement_item_other_owner A i g hg
  exact ⟨a,ha,g,hg,hOwner,hBelongs,hValue⟩

/-- Divisibility makes every balanced part exactly q, using the existing
floor-or-ceiling definition with no stronger balance notion. -/
theorem balanced_exact_size {n m q : ℕ} (hn : 0<n) (hm : m=n*q)
    {A : Allocation n m} (hA : IsBalanced A) : ∀i,(bundle A i).card=q := by
  have hFloor : m/n=q := by
    rw [hm]
    exact Nat.mul_div_cancel_left q hn
  have hDivides : n∣m := ⟨q,hm⟩
  have hRemainder : m%n=0 := Nat.mod_eq_zero_of_dvd hDivides
  have hUpper : upperSize n m=q := by
    unfold upperSize
    rw [hFloor,if_pos hRemainder,Nat.add_zero]
  intro i
  rcases hA i with hi|hi
  · exact hi.trans hFloor
  · exact hi.trans hUpper

private theorem nonempty_oneDeletion_singleton {m : ℕ} {D B : Finset (Fin m)}
    (hD : CanDeleteOne D B) (hNonempty : D.Nonempty) : ∃b∈B,D={b} := by
  have hCard : D.card=1 := by
    have hPositive:=Finset.card_pos.mpr hNonempty
    have hAtMost : D.card≤1:=hD.2
    omega
  obtain ⟨b,hb⟩:=Finset.card_eq_one.mp hCard
  have hbD : b∈D := by
    rw [hb]
    exact Finset.mem_singleton_self b
  exact ⟨b,hD.1 hbD,hb⟩

/-- EF[1,1] for the exact worst-completion valuations supplies precisely the
manuscript's replacement in the envied bundle. -/
theorem enviedReplacement_of_worst_ef11 {n m q : ℕ} (hqm : q ≤ m)
    (v : Fin n→QBundle m q→ℝ) (A : Allocation n m)
    (hSize : ∀i : Fin n,(bundle A i).card=q)
    (hFair : IsEF11 (fun i=>worstExtension hqm (v i)) A) : IsEnviedReplacement v A := by
  refine ⟨hSize,?_⟩
  intro i j hEnvy
  obtain ⟨C,D,hC,hD,hComparison⟩:=hFair i j
  let Bi : QBundle m q:=⟨bundle A i,hSize i⟩
  let Bj : QBundle m q:=⟨bundle A j,hSize j⟩
  change v i Bi<v i Bj at hEnvy
  have hFulli:=worstExtension_full hqm (v i) Bi
  have hFullj:=worstExtension_full hqm (v i) Bj
  have hRestore := worstExtension_monotone hqm (v i)
    (show bundle A i\C⊆bundle A i from Finset.sdiff_subset)
  have hBound : worstExtension hqm (v i) (bundle A j\D)≤v i Bi := by
    exact hComparison.trans (hRestore.trans hFulli.le)
  have hDNonempty : D.Nonempty := by
    by_contra hEmpty
    have hDZero : D=∅:=Finset.not_nonempty_iff_eq_empty.mp hEmpty
    have hContr : v i Bj≤v i Bi := by
      calc
        v i Bj=worstExtension hqm (v i) (bundle A j) := hFullj.symm
        _=worstExtension hqm (v i) (bundle A j\D) := by rw [hDZero,Finset.sdiff_empty]
        _≤v i Bi := hBound
    exact (not_le_of_gt hEnvy) hContr
  obtain ⟨b,hb,hDb⟩:=nonempty_oneDeletion_singleton hD hDNonempty
  have hErase : ((bundle A j).erase b).card≤q := by
    exact (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq (hSize j)
  obtain ⟨T,hSubset,hValue⟩:=worstExtension_attained hqm (v i) ((bundle A j).erase b) hErase
  obtain ⟨g,hg,hT⟩:=completion_of_erase Bj b hb T hSubset
  have hValueBound : v i T≤v i Bi := by
    calc
      v i T=worstExtension hqm (v i) ((bundle A j).erase b) := hValue.symm
      _=worstExtension hqm (v i) (bundle A j\D) := by
        rw [hDb,Finset.sdiff_singleton_eq_erase]
      _≤v i Bi := hBound
  have hgOutside : g∉bundle A j := by
    intro hgIn
    have hgb : g=b := by
      by_contra hgb
      exact hg (Finset.mem_erase.mpr ⟨hgb,hgIn⟩)
    have hTj : T=Bj := by
      apply Subtype.ext
      rw [←hT,hgb,Finset.insert_erase hb]
    rw [hTj] at hValueBound
    exact (not_le_of_gt hEnvy) hValueBound
  exact ⟨b,hb,g,hgOutside,T,hT.symm,hValueBound⟩

/-- The best-completion extension supplies the dual replacement in one's
OWN bundle. The rival bundle is restored using nonincreasingness. -/
theorem ownReplacement_of_best_ef11 {n m q : ℕ} (hqm : q ≤ m)
    (v : Fin n→QBundle m q→ℝ) (A : Allocation n m)
    (hSize : ∀i : Fin n,(bundle A i).card=q)
    (hFair : IsEF11 (fun i=>bestExtension hqm (v i)) A) : IsOwnReplacement v A := by
  refine ⟨hSize,?_⟩
  intro i j hEnvy
  obtain ⟨C,D,hC,hD,hComparison⟩:=hFair i j
  let Bi : QBundle m q:=⟨bundle A i,hSize i⟩
  let Bj : QBundle m q:=⟨bundle A j,hSize j⟩
  change v i Bi<v i Bj at hEnvy
  have hFulli:=bestExtension_full hqm (v i) Bi
  have hFullj:=bestExtension_full hqm (v i) Bj
  have hRestore := bestExtension_antitone hqm (v i)
    (show bundle A j\D⊆bundle A j from Finset.sdiff_subset)
  have hBound : v i Bj≤bestExtension hqm (v i) (bundle A i\C) := by
    exact hFullj.symm.le.trans (hRestore.trans hComparison)
  have hCNonempty : C.Nonempty := by
    by_contra hEmpty
    have hCZero : C=∅:=Finset.not_nonempty_iff_eq_empty.mp hEmpty
    have hContr : v i Bj≤v i Bi := by
      calc
        v i Bj≤bestExtension hqm (v i) (bundle A i\C) := hBound
        _=bestExtension hqm (v i) (bundle A i) := by rw [hCZero,Finset.sdiff_empty]
        _=v i Bi := hFulli
    exact (not_le_of_gt hEnvy) hContr
  obtain ⟨a,ha,hCa⟩:=nonempty_oneDeletion_singleton hC hCNonempty
  have hErase : ((bundle A i).erase a).card≤q := by
    exact (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq (hSize i)
  obtain ⟨T,hSubset,hValue⟩:=bestExtension_attained hqm (v i) ((bundle A i).erase a) hErase
  obtain ⟨g,hg,hT⟩:=completion_of_erase Bi a ha T hSubset
  have hValueBound : v i Bj≤v i T := by
    calc
      v i Bj≤bestExtension hqm (v i) (bundle A i\C) := hBound
      _=bestExtension hqm (v i) ((bundle A i).erase a) := by
        rw [hCa,Finset.sdiff_singleton_eq_erase]
      _=v i T := hValue
  have hgOutside : g∉bundle A i := by
    intro hgIn
    have hga : g=a := by
      by_contra hga
      exact hg (Finset.mem_erase.mpr ⟨hga,hgIn⟩)
    have hTi : T=Bi := by
      apply Subtype.ext
      rw [←hT,hga,Finset.insert_erase ha]
    rw [hTi] at hValueBound
    exact (not_le_of_gt hEnvy) hValueBound
  exact ⟨a,ha,g,hgOutside,T,hT.symm,hValueBound⟩

end FairDivision.BF.ReplacementFairness
