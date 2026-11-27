import EF1FPO.RoundData
import EF1FPO.ForestRoster
import OAI.Optimization.LinearProgramming.PriceGame.ControlRatListSum
import OAI.Optimization.LinearProgramming.PriceGame.LearningGroupingSort

/-! Deterministic whole-good elimination and transfer loops. -/

set_option autoImplicit false

namespace EF1FPO.RoundKernel

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame
open EF1FPO.RoundData
open EF1FPO.PreparationMatrixWire (readCell)

abbrev Roster := List Bool × List ℕ

def rosterCode : Roster → Word := prodCode (listCode boolCode) (listCode Nat.bits)

def owner (d : Packed) (owners : List ℕ) (g : ℕ) : ℕ := readCell d.agents owners g

def pending (d : Packed) (s : Roster) (g : ℕ) : Bool := decide (d.agents ≤ owner d s.2 g)

def bidders (d : Packed) (active : List Bool) (g : ℕ) : List ℕ :=
  (List.range d.agents).filter (fun i => readCell false active i && marked d i g)

def neighbors (d : Packed) (s : Roster) (i : ℕ) : List ℕ :=
  (List.range d.goods).filter (fun g => pending d s g && marked d i g)

def goodLeaves (d : Packed) (s : Roster) : List ℕ :=
  (List.range d.goods).filter (fun g => pending d s g && decide ((bidders d s.1 g).length = 1))

def agentLeaves (d : Packed) (s : Roster) : List ℕ :=
  (List.range d.agents).filter (fun i =>
    readCell false s.1 i && decide ((neighbors d s i).length = 1))

def spent (d : Packed) (owners : List ℕ) (i : ℕ) : ℚ :=
  ((List.range d.goods).map (fun g => if owner d owners g = i then price d g else 0)).sum

def start (upper : Bool) (d : Packed) : Roster :=
  let active := List.replicate d.agents true
  let owners := (List.range d.goods).map fun g =>
    let bs := bidders d active g
    if upper && decide (bs.length = 1) then bs.headD d.agents else d.agents
  (active, owners)

def leafStep (upper : Bool) (d : Packed) (s : Roster) : Roster :=
  let gl := goodLeaves d s
  let al := agentLeaves d s
  if !upper && !gl.isEmpty then
    let g := gl.headD 0
    let i := (bidders d s.1 g).headD 0
    (s.1, s.2.set g i)
  else if !al.isEmpty then
    let i := al.headD 0
    let g := (neighbors d s i).headD 0
    let remaining := s.1.set i false
    if upper || decide (spent d s.2 i < 1) then (remaining, s.2.set g i)
    else (remaining, s.2)
  else s

def Sized (d : Packed) (s : Roster) : Prop :=
  s.1.length = d.agents ∧ s.2.length = d.goods ∧ ∀ i ∈ s.2, i ≤ d.agents

private theorem head_le (xs : List ℕ) (fallback bound : ℕ) (hz : fallback ≤ bound)
    (h : ∀ i ∈ xs, i ≤ bound) : xs.headD fallback ≤ bound := by
  cases xs with
  | nil => exact hz
  | cons i xs => exact h i List.mem_cons_self

private theorem bidder_head_le (d : Packed) (flags : List Bool) (g fallback : ℕ)
    (hz : fallback ≤ d.agents) : (bidders d flags g).headD fallback ≤ d.agents := by
  apply head_le _ _ _ hz
  intro i hi
  exact (List.mem_range.mp (List.mem_filter.mp hi).1).le

private theorem agent_head_le (d : Packed) (s : Roster) : (agentLeaves d s).headD 0 ≤ d.agents := by
  apply head_le _ _ _ (Nat.zero_le _)
  intro i hi
  exact (List.mem_range.mp (List.mem_filter.mp hi).1).le

private theorem set_label {d : Packed} {active : List Bool} {owners : List ℕ}
    (h : Sized d (active, owners)) (g i : ℕ) (hi : i ≤ d.agents) : Sized d (active, owners.set g i) := by
  refine ⟨h.1, by simpa using h.2.1, ?_⟩
  intro j hj
  exact (List.mem_or_eq_of_mem_set hj).elim (h.2.2 j) (fun e => e ▸ hi)

private theorem clear_flag {d : Packed} {s : Roster} (h : Sized d s) (i : ℕ) :
    Sized d (s.1.set i false, s.2) :=
  ⟨by simpa using h.1, h.2⟩

theorem start_sized (upper : Bool) (d : Packed) : Sized d (start upper d) := by
  refine ⟨by simp [start], by simp [start], ?_⟩
  intro i hi
  obtain ⟨g, _, he⟩ := List.mem_map.mp hi
  rw [← he]
  dsimp only
  split
  · exact bidder_head_le d _ g _ le_rfl
  · exact le_rfl

theorem leaf_step_sized (upper : Bool) (d : Packed) (s : Roster) (hs : Sized d s) :
    Sized d (leafStep upper d s) := by
  dsimp only [leafStep]
  split
  · exact set_label hs _ _ (bidder_head_le d _ _ _ (Nat.zero_le _))
  · split
    · split
      · exact set_label (clear_flag hs _) _ _ (agent_head_le d s)
      · exact clear_flag hs _
    · exact hs

def leafOutput (upper : Bool) (d : Packed) : Roster :=
  ((leafStep upper d)^[d.agents + d.goods]) (start upper d)

def transferCandidates (d : Packed) (cover owners : List ℕ) : List ℕ :=
  (List.range d.goods).filter (fun g =>
    decide (owner d owners g ≠ owner d cover g) &&
      decide (spent d owners (owner d cover g) < 1))

def repairStep (d : Packed) (cover owners : List ℕ) : List ℕ :=
  let candidates := transferCandidates d cover owners
  if candidates.isEmpty then owners
  else
    let g := candidates.headD 0
    owners.set g (owner d cover g)

theorem repair_step_sized (d : Packed) (cover owners : List ℕ) (active : List Bool)
    (hc : Sized d (active, cover)) (hA : Sized d (active, owners)) :
    Sized d (active, repairStep d cover owners) := by
  dsimp only [repairStep]
  split
  · exact hA
  · apply set_label hA
    unfold owner readCell
    apply head_le _ _ _ le_rfl
    intro i hi
    exact hc.2.2 i (List.mem_of_mem_drop hi)

def roundOwners (d : Packed) : List ℕ :=
  ((repairStep d (leafOutput false d).2)^[d.goods]) (leafOutput true d).2

def emit (d : Packed) (owners : List ℕ) : Word :=
  encodeNat d.agents ++ encodeNat d.goods ++ owners.flatMap encodeNat

private def toRoster (p : Packet) (s : Roster) : p.inst.Roster :=
  ⟨Finset.univ.filter (fun i : p.inst.Agent => readCell false s.1 i.val = true),
    Finset.univ.filter (fun g : p.inst.Good => owner p.pack s.2 g.val < p.inst.n),
    fun g => ⟨owner p.pack s.2 g.val % p.inst.n, Nat.mod_lt _ p.inst.hn⟩⟩

private theorem active_at (p : Packet) (s : Roster) (i : p.inst.Agent) :
    i ∈ (toRoster p s).active ↔ readCell false s.1 i.val = true := by simp [toRoster]

private theorem pending_at (p : Packet) (s : Roster) (g : p.inst.Good) :
    g ∉ (toRoster p s).assigned ↔ pending p.pack s g.val = true := by
  simp [toRoster, pending, not_lt, Packet.pack, fromWeighed, Packet.weighed]

private theorem read_get {α : Type} (fallback : α) (xs : List α) (i : ℕ) (h : i < xs.length) :
    readCell fallback xs i = xs[i] := by
  rw [readCell, List.headD_eq_head?_getD, List.head?_drop, List.getElem?_eq_getElem h, Option.getD_some]

private theorem read_set {α : Type} (fallback : α) (xs : List α) (i j : ℕ)
    (value : α) (h : j < xs.length) :
    readCell fallback (xs.set i value) j = if i = j then value else readCell fallback xs j := by
  rw [read_get _ _ _ (by simpa using h), List.getElem_set, read_get _ _ _ h]

private theorem toRoster_take (p : Packet) (s : Roster) (h : Sized p.pack s)
    (i : p.inst.Agent) (g : p.inst.Good) :
    toRoster p (s.1, s.2.set g.val i.val) = (toRoster p s).take p.inst i g := by
  classical
  have read (f : p.inst.Good) :
      owner p.pack (s.2.set g.val i.val) f.val =
        if g = f then i.val else owner p.pack s.2 f.val := by
    unfold owner
    have hf : f.val < s.2.length := h.2.1.symm ▸ f.isLt
    rw [read_set _ _ _ _ _ hf]
    simp [Fin.val_inj]
  unfold toRoster Instance.Roster.take
  congr 1
  · ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    rw [read]
    by_cases hfg : f = g
    · subst f
      simp [i.isLt]
    · simp [hfg, Ne.symm hfg]
  · funext f
    apply Fin.ext
    simp only [Fin.val_mk]
    rw [read]
    by_cases hfg : f = g
    · subst f
      simp [Nat.mod_eq_of_lt i.isLt]
    · simp [hfg, Ne.symm hfg, Function.update_of_ne hfg]

private theorem toRoster_remove (p : Packet) (s : Roster) (h : Sized p.pack s)
    (i : p.inst.Agent) :
    toRoster p (s.1.set i.val false, s.2) = (toRoster p s).remove p.inst i := by
  classical
  unfold toRoster Instance.Roster.remove
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  have hj : j.val < s.1.length := h.1.symm ▸ j.isLt
  rw [read_set _ _ _ _ _ hj]
  by_cases he : i = j
  · subst j
    simp
  · simp [he, Ne.symm he, Fin.val_inj]

private theorem owner_valid (p : Packet) (s : Roster) (g : p.inst.Good)
    (h : g ∈ (toRoster p s).assigned) : ((toRoster p s).owner g).val = owner p.pack s.2 g.val :=
  Nat.mod_eq_of_lt ((Finset.mem_filter.mp h).2)

private theorem map_range_fin {α : Type} {n : ℕ} (f : ℕ → α) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]

private theorem spent_agrees (p : Packet) (s : Roster) (w : p.inst.Weights)
    (hp : ∀ g : p.inst.Good, (RoundData.price p.pack g.val : ℝ) = p.inst.price w g)
    (i : p.inst.Agent) :
    (spent p.pack s.2 i.val : ℝ) = (toRoster p s).spending p.inst w i := by
  classical
  let t := toRoster p s
  change (((List.range p.inst.m).map (fun g =>
    if owner p.pack s.2 g = i.val then RoundData.price p.pack g else 0)).sum : ℝ) =
      t.spending p.inst w i
  rw [Rat.cast_list_sum, List.map_map, map_range_fin, List.sum_ofFn]
  change (∑ g : p.inst.Good, ((if owner p.pack s.2 g.val = i.val then RoundData.price p.pack g.val else 0 : ℚ) : ℝ)) =
    p.inst.bundlePrice w (t.assigned.filter (fun g => t.owner g = i))
  unfold Instance.bundlePrice
  have hSet : (t.assigned.filter (fun g => t.owner g = i)) =
      Finset.univ.filter (fun g : p.inst.Good => owner p.pack s.2 g.val = i.val) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hg, hi⟩
      rw [← owner_valid p s g hg, hi]
    · intro hg
      have hOwn : g ∈ t.assigned := by
        simp only [t, toRoster, Finset.mem_filter, Finset.mem_univ, true_and, hg]
        exact i.isLt
      exact ⟨hOwn, Fin.ext ((owner_valid p s g hOwn).trans hg)⟩
  rw [hSet]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g hg
  by_cases he : owner p.pack s.2 g.val = i.val
  · simp [he, hp]
  · simp [he]

private theorem head_exists (xs : List ℕ) (h : xs.isEmpty = false) : xs.headD 0 ∈ xs := by
  cases xs with
  | nil => contradiction
  | cons x xs => exact List.mem_cons_self

private theorem mem_single_head {xs : List ℕ} (h : xs.length = 1) (fallback a : ℕ) :
    a ∈ xs ↔ a = xs.headD fallback := by
  cases xs with
  | nil => contradiction
  | cons x xs => cases xs <;> simp_all

private theorem bidders_at (p : Packet) (s : Roster)
    (w : p.inst.Weights)
    (hB : ∀ (i : p.inst.Agent) (g : p.inst.Good),
      marked p.pack i.val g.val = true ↔ p.inst.IsHighestBidder w i g)
    (i : p.inst.Agent) (g : p.inst.Good) :
    i.val ∈ bidders p.pack s.1 g.val ↔
      i ∈ (toRoster p s).active ∧ p.inst.IsHighestBidder w i g := by
  rw [bidders, List.mem_filter, List.mem_range, Bool.and_eq_true_iff, ← active_at, hB]
  exact ⟨fun hi => hi.2, fun hi => ⟨i.isLt, hi⟩⟩

private theorem neighbors_at (p : Packet) (s : Roster) (w : p.inst.Weights)
    (hB : ∀ (i : p.inst.Agent) (g : p.inst.Good),
      marked p.pack i.val g.val = true ↔ p.inst.IsHighestBidder w i g)
    (i : p.inst.Agent) (g : p.inst.Good) (hI : i ∈ (toRoster p s).active) :
    g.val ∈ neighbors p.pack s i.val ↔ (toRoster p s).isLive p.inst w i g := by
  rw [neighbors, List.mem_filter, List.mem_range, Bool.and_eq_true_iff, ← pending_at, hB]
  exact ⟨fun he => ⟨hI, he.2⟩, fun he => ⟨g.isLt, he.2⟩⟩

private theorem choose_agent (p : Packet) (s : Roster) (w : p.inst.Weights)
    (hB : ∀ (i : p.inst.Agent) (g : p.inst.Good),
      marked p.pack i.val g.val = true ↔ p.inst.IsHighestBidder w i g)
    (h : (agentLeaves p.pack s).isEmpty = false) :
    ∃ (i : p.inst.Agent) (g : p.inst.Good),
      i.val = (agentLeaves p.pack s).headD 0 ∧
      g.val = (neighbors p.pack s i.val).headD 0 ∧ (toRoster p s).agentLeaf p.inst w i g := by
  let k := (agentLeaves p.pack s).headD 0
  have hk := head_exists _ h
  obtain ⟨hn, ht⟩ := List.mem_filter.mp hk
  let i : p.inst.Agent := ⟨k, List.mem_range.mp hn⟩
  have hProps := Bool.and_eq_true_iff.mp ht
  have hI : i ∈ (toRoster p s).active := (active_at p s i).mpr hProps.1
  let ns := neighbors p.pack s i.val
  have hOne : ns.length = 1 := of_decide_eq_true hProps.2
  have hGM : ns.headD 0 ∈ ns := (mem_single_head hOne 0 _).mpr rfl
  let g : p.inst.Good := ⟨ns.headD 0, List.mem_range.mp (List.mem_filter.mp hGM).1⟩
  refine ⟨i, g, rfl, rfl, (neighbors_at p s w hB i g hI).mp hGM, ?_⟩
  intro f hf
  have hm := (neighbors_at p s w hB i f hI).mpr hf
  change f.val ∈ ns at hm
  have hfVal : f.val = ns.headD 0 := (mem_single_head hOne 0 _).mp hm
  exact Fin.ext hfVal

private theorem choose_good (p : Packet) (s : Roster) (w : p.inst.Weights)
    (hB : ∀ (i : p.inst.Agent) (g : p.inst.Good),
      marked p.pack i.val g.val = true ↔ p.inst.IsHighestBidder w i g)
    (h : (goodLeaves p.pack s).isEmpty = false) :
    ∃ (i : p.inst.Agent) (g : p.inst.Good),
      i.val = (bidders p.pack s.1 g.val).headD 0 ∧ g.val = (goodLeaves p.pack s).headD 0 ∧
      (toRoster p s).isLive p.inst w i g ∧ ∀ j, (toRoster p s).isLive p.inst w j g → j = i := by
  let k := (goodLeaves p.pack s).headD 0
  have hk := head_exists _ h
  obtain ⟨hm, ht⟩ := List.mem_filter.mp hk
  let g : p.inst.Good := ⟨k, List.mem_range.mp hm⟩
  have hProps := Bool.and_eq_true_iff.mp ht
  have hP := (pending_at p s g).mpr hProps.1
  let bs := bidders p.pack s.1 g.val
  have hOne : bs.length = 1 := of_decide_eq_true hProps.2
  have hIM : bs.headD 0 ∈ bs := (mem_single_head hOne 0 _).mpr rfl
  let i : p.inst.Agent := ⟨bs.headD 0, List.mem_range.mp (List.mem_filter.mp hIM).1⟩
  have hi := (bidders_at p s w hB i g).mp hIM
  refine ⟨i, g, rfl, rfl, ⟨hi.1, hP, hi.2⟩, ?_⟩
  intro j hj
  have hM := (bidders_at p s w hB j g).mpr ⟨hj.1, hj.2.2⟩
  change j.val ∈ bs at hM
  have he : j.val = bs.headD 0 := (mem_single_head hOne 0 _).mp hM
  exact Fin.ext he

private theorem lower_two (p : Packet) (s : Roster) (w : p.inst.Weights)
    (hB : ∀ (i : p.inst.Agent) (g : p.inst.Good),
      marked p.pack i.val g.val = true ↔ p.inst.IsHighestBidder w i g)
    (hC : (toRoster p s).lowerInvariant p.inst w)
    (hNone : (goodLeaves p.pack s).isEmpty = true) :
    ∀ g ∉ (toRoster p s).assigned, ∃ i j : p.inst.Agent, i ≠ j ∧
      (toRoster p s).isLive p.inst w i g ∧ (toRoster p s).isLive p.inst w j g := by
  intro g hg
  obtain ⟨C, hS, _, _, hLive⟩ := hC
  let bs := bidders p.pack s.1 g.val
  have hMem : (C g).val ∈ bs := (bidders_at p s w hB (C g) g).mpr ⟨hLive g hg, hS g⟩
  have hTwo : bs.length ≠ 1 := by
    intro hLen
    have hIn : g.val ∈ goodLeaves p.pack s :=
      List.mem_filter.mpr ⟨List.mem_range.mpr g.isLt,
        Bool.and_eq_true_iff.mpr ⟨(pending_at p s g).mp hg, decide_eq_true hLen⟩⟩
    simp [List.isEmpty_iff.mp hNone] at hIn
  have nodup : bs.Nodup := List.Nodup.filter _ List.nodup_range
  cases hBs : bs with
  | nil => simp [hBs] at hMem
  | cons a rest =>
    cases rest with
    | nil => simp [hBs] at hTwo
    | cons b rest =>
      have hA : a ∈ bs := by rw [hBs]; exact List.mem_cons_self
      have hB' : b ∈ bs := by rw [hBs]; exact List.mem_cons_of_mem _ List.mem_cons_self
      let i : p.inst.Agent := ⟨a, List.mem_range.mp (List.mem_filter.mp hA).1⟩
      let j : p.inst.Agent := ⟨b, List.mem_range.mp (List.mem_filter.mp hB').1⟩
      have hne : a ≠ b := by
        rw [hBs, List.nodup_cons] at nodup
        exact fun he => nodup.1 (he ▸ List.mem_cons_self)
      have heA := (bidders_at p s w hB i g).mp hA
      have heB := (bidders_at p s w hB j g).mp hB'
      exact ⟨i, j, fun e => hne (congrArg Fin.val e), ⟨heA.1, hg, heA.2⟩, ⟨heB.1, hg, heB.2⟩⟩

private theorem singleton_of_only (xs : List ℕ) (v : ℕ) (hN : xs.Nodup) (hm : v ∈ xs)
    (hOnly : ∀ a ∈ xs, a = v) : xs = [v] := by
  cases xs with
  | nil => contradiction
  | cons a rest =>
    have he : a = v := hOnly a List.mem_cons_self
    subst a
    cases rest with
    | nil => rfl
    | cons b rest =>
      have he : b = v := hOnly b (List.mem_cons_of_mem _ List.mem_cons_self)
      subst b
      exact ((List.nodup_cons.mp hN).1 List.mem_cons_self).elim

private theorem agent_exists (p : Packet) (s : Roster) (w : p.inst.Weights)
    (hB : ∀ (i : p.inst.Agent) (g : p.inst.Good),
      marked p.pack i.val g.val = true ↔ p.inst.IsHighestBidder w i g)
    (i : p.inst.Agent) (g : p.inst.Good) (h : (toRoster p s).agentLeaf p.inst w i g) :
    (agentLeaves p.pack s).isEmpty = false := by
  let ns := neighbors p.pack s i.val
  have hm := (neighbors_at p s w hB i g h.1.1).mpr h.1
  have hs : ns = [g.val] := by
    apply singleton_of_only ns g.val (List.Nodup.filter _ List.nodup_range) hm
    intro a ha
    let f : p.inst.Good := ⟨a, List.mem_range.mp (List.mem_filter.mp ha).1⟩
    exact congrArg Fin.val (h.2 f ((neighbors_at p s w hB i f h.1.1).mp ha))
  have hLen : ns.length = 1 := by simp [hs]
  have hMem : i.val ∈ agentLeaves p.pack s :=
    List.mem_filter.mpr ⟨List.mem_range.mpr i.isLt,
      Bool.and_eq_true_iff.mpr ⟨(active_at p s i).mp h.1.1, decide_eq_true hLen⟩⟩
  cases he : (agentLeaves p.pack s).isEmpty
  · rfl
  · simp [List.isEmpty_iff.mp he] at hMem

private theorem flag_start (p : Packet) (upper : Bool) :
    (toRoster p (start upper p.pack)).active = Finset.univ := by
  ext i
  rw [active_at]
  have h : i.val < (List.replicate p.inst.n true).length := by simpa using i.isLt
  change readCell false (List.replicate p.inst.n true) i.val = true ↔ _
  simp [read_get _ _ _ h]

private theorem lower_start (p : Packet) (w : p.inst.Weights) (hC : p.inst.Covers w) :
    (toRoster p (start false p.pack)).lowerInvariant p.inst w := by
  obtain ⟨C, hS, hL⟩ := hC
  refine ⟨C, hS, hL, ?_, ?_⟩
  · intro g hg
    change g ∈ (Finset.univ.filter fun a : p.inst.Good =>
      owner p.pack (start false p.pack).2 a.val < p.inst.n) at hg
    have ht := (Finset.mem_filter.mp hg).2
    change owner p.pack ((List.range p.inst.m).map (fun _ => p.inst.n)) g.val < p.inst.n at ht
    have hLen : g.val < ((List.range p.inst.m).map (fun _ => p.inst.n)).length := by simpa using g.isLt
    unfold owner at ht
    rw [read_get _ _ _ hLen, List.getElem_map] at ht
    exact (lt_irrefl _ ht).elim
  · intro g _
    rw [flag_start]
    exact Finset.mem_univ _

private theorem upper_start_raw (p : Packet) (w : p.inst.Weights)
    (hB : ∀ (i : p.inst.Agent) (g : p.inst.Good),
      marked p.pack i.val g.val = true ↔ p.inst.IsHighestBidder w i g) :
    (toRoster p (start true p.pack)).upperInvariant p.inst w := by
  let s := start true p.pack
  have active (i : p.inst.Agent) : i ∈ (toRoster p s).active := by
    rw [show (toRoster p s).active = Finset.univ from flag_start p true]
    exact Finset.mem_univ _
  have exact_mem (i : p.inst.Agent) (g : p.inst.Good) :
      i.val ∈ bidders p.pack s.1 g.val ↔ p.inst.IsHighestBidder w i g := by
    simp [bidders_at p s w hB, active]
  have single (g : p.inst.Good) :
      (bidders p.pack s.1 g.val).length = 1 ↔ ¬ Instance.Roster.shared p.inst w g := by
    let bs := bidders p.pack s.1 g.val
    constructor
    · intro h
      rintro ⟨i, j, hne, hi, hj⟩
      have hlen : bs.length = 1 := h
      have hi' := (exact_mem i g).mpr hi
      have hj' := (exact_mem j g).mpr hj
      change i.val ∈ bs at hi'
      change j.val ∈ bs at hj'
      have eI : i.val = bs.headD 0 := (mem_single_head hlen 0 _).mp hi'
      have eJ : j.val = bs.headD 0 := (mem_single_head hlen 0 _).mp hj'
      exact hne (Fin.ext (eI.trans eJ.symm))
    · intro h
      obtain ⟨i, hi⟩ := p.inst.exists_highest_bidder w g
      have hOne : bs = [i.val] := by
        apply singleton_of_only bs i.val (List.Nodup.filter _ List.nodup_range) ((exact_mem i g).mpr hi)
        intro a ha
        let j : p.inst.Agent := ⟨a, List.mem_range.mp (List.mem_filter.mp ha).1⟩
        have hj := (exact_mem j g).mp ha
        by_contra e
        exact h ⟨j, i, fun e' => e (congrArg Fin.val e'), hj, hi⟩
      change bs.length = 1
      simp [hOne]
  have by_value (g : p.inst.Good) :
      owner p.pack s.2 g.val =
        (if (bidders p.pack s.1 g.val).length = 1 then
          (bidders p.pack s.1 g.val).headD p.inst.n else p.inst.n) := by
    let f (g : ℕ) :=
      let bs := bidders p.pack (List.replicate p.inst.n true) g
      if true && decide (bs.length = 1) then bs.headD p.inst.n else p.inst.n
    have hLen : g.val < ((List.range p.inst.m).map f).length := by simpa using g.isLt
    unfold owner
    change readCell p.inst.n ((List.range p.inst.m).map f) g.val = _
    rw [read_get _ _ _ hLen, List.getElem_map, List.getElem_range]
    simp [f, s, start]
    rfl
  have valid_head (g : p.inst.Good) (h : (bidders p.pack s.1 g.val).length = 1) :
      (bidders p.pack s.1 g.val).headD p.inst.n ∈ bidders p.pack s.1 g.val := by
    let bs := bidders p.pack s.1 g.val
    change bs.headD p.inst.n ∈ bs
    cases hb : bs with
    | nil =>
      change bs.length = 1 at h
      simp [hb] at h
    | cons a as => exact List.mem_cons_self
  apply Instance.Roster.upper_start p.inst w (toRoster p s) (flag_start p true)
  · intro g
    simp only [toRoster, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [by_value]
    by_cases he : (bidders p.pack s.1 g.val).length = 1
    · have hI : (bidders p.pack s.1 g.val).headD p.inst.n < p.inst.n :=
        List.mem_range.mp (List.mem_filter.mp (valid_head g he)).1
      rw [if_pos he]
      exact ⟨fun _ => (single g).mp he, fun _ => hI⟩
    · have hNot : Instance.Roster.shared p.inst w g := by
        by_contra hf
        exact he ((single g).mpr hf)
      simp [he, hNot]
  · intro g hg
    have hlt : owner p.pack s.2 g.val < p.inst.n := (Finset.mem_filter.mp hg).2
    have he : (bidders p.pack s.1 g.val).length = 1 := by
      by_contra hh
      rw [by_value, if_neg hh] at hlt
      exact lt_irrefl _ hlt
    apply (exact_mem _ g).mp
    rw [owner_valid p s g hg, by_value, if_pos he]
    exact valid_head g he

private theorem bounded_descent {S : Type} (step : S → S) (inv done : S → Prop) (μ : S → ℕ)
    (closed : ∀ s, inv s → inv (step s)) (fixed : ∀ s, inv s → done s → step s = s)
    (decreases : ∀ s, inv s → ¬ done s → μ (step s) < μ s)
    (t : ℕ) (s : S) (hInv : inv s) (hTime : μ s ≤ t) :
    inv ((step^[t]) s) ∧ done ((step^[t]) s) := by
  classical
  induction t generalizing s with
  | zero =>
    refine ⟨hInv, ?_⟩
    by_contra hf
    have h := decreases s hInv hf
    omega
  | succ t ih =>
    by_cases hf : done s
    · rw [Function.iterate_fixed (fixed s hInv hf)]
      exact ⟨hInv, hf⟩
    · rw [Function.iterate_succ_apply]
      have h := decreases s hInv hf
      exact ih (step s) (closed s hInv) (by omega)

private def vertices {I : Instance} (s : I.Roster) : ℕ :=
  I.m - s.assigned.card + s.active.card

private theorem vertices_le {I : Instance} (s : I.Roster) :
    vertices s ≤ I.n + I.m := by
  have hn := Finset.card_le_univ s.active
  rw [Fintype.card_fin] at hn
  unfold vertices
  omega

private theorem vertices_take {I : Instance} (s : I.Roster) (i : I.Agent) (g : I.Good)
    (h : g ∉ s.assigned) : vertices (s.take I i g) < vertices s := by
  have hUp := Finset.card_le_univ (insert g s.assigned)
  rw [Fintype.card_fin, Finset.card_insert_of_notMem h] at hUp
  unfold vertices Instance.Roster.take
  simp only [Finset.card_insert_of_notMem h]
  omega

private theorem vertices_remove {I : Instance} (s : I.Roster) (i : I.Agent)
    (h : i ∈ s.active) : vertices (s.remove I i) < vertices s := by
  have hCount := Finset.card_erase_add_one h
  unfold vertices Instance.Roster.remove
  dsimp only
  omega

private def finished (p : Packet) (s : Roster) : Prop :=
  (toRoster p s).assigned = Finset.univ

private def invariant (p : Packet) (w : p.inst.Weights) (upper : Bool) (s : Roster) : Prop :=
  Sized p.pack s ∧ if upper then (toRoster p s).upperInvariant p.inst w
    else (toRoster p s).lowerInvariant p.inst w

set_option maxHeartbeats 1500000 in
private theorem leaf_moves (p : Packet) (w : p.inst.Weights)
    (hB : ∀ (i : p.inst.Agent) (g : p.inst.Good),
      marked p.pack i.val g.val = true ↔ p.inst.IsHighestBidder w i g)
    (hP : ∀ g : p.inst.Good, (RoundData.price p.pack g.val : ℝ) = p.inst.price w g)
    (hw : p.inst.Positive w) (hF : p.inst.IsForest w)
    (upper : Bool) (s : Roster) (hInv : invariant p w upper s) :
    (finished p s → leafStep upper p.pack s = s) ∧
      (¬ finished p s →
        invariant p w upper (leafStep upper p.pack s) ∧
        vertices (toRoster p (leafStep upper p.pack s)) < vertices (toRoster p s)) := by
  constructor
  · intro hall
    have no_good : (goodLeaves p.pack s).isEmpty = true := by
      cases hG : (goodLeaves p.pack s).isEmpty
      · obtain ⟨i, g, _, _, hLive, _⟩ := choose_good p s w hB hG
        exact (hLive.2.1 (by rw [show (toRoster p s).assigned = Finset.univ from hall]; simp)).elim
      · rfl
    have no_agent : (agentLeaves p.pack s).isEmpty = true := by
      cases hA : (agentLeaves p.pack s).isEmpty
      · obtain ⟨i, g, _, _, hLeaf⟩ := choose_agent p s w hB hA
        exact (hLeaf.1.2.1 (by rw [show (toRoster p s).assigned = Finset.univ from hall]; simp)).elim
      · rfl
    simp [leafStep, no_good, no_agent]
  · intro hNot
    let I := p.inst
    let d := p.pack
    let t := toRoster p s
    have missing : ∃ g, g ∉ t.assigned := by
      by_contra h
      push_neg at h
      apply hNot
      exact Finset.eq_univ_of_forall h
    have viaAgent (hForce : (!upper && !(goodLeaves d s).isEmpty) = false)
        (hTwo : ∀ g ∉ t.assigned, ∃ i j : I.Agent, i ≠ j ∧
          t.isLive I w i g ∧ t.isLive I w j g) :
        invariant p w upper (leafStep upper d s) ∧
          vertices (toRoster p (leafStep upper d s)) < vertices t := by
      obtain ⟨i, g, hl⟩ := t.exists_agent_leaf I w hF missing hTwo
      have nonempty := agent_exists p s w hB i g hl
      obtain ⟨a, b, ha, hb, leaf⟩ := choose_agent p s w hB nonempty
      have shapeNext := leaf_step_sized upper d s hInv.1
      have take_remove : toRoster p (s.1.set a.val false, s.2.set b.val a.val) =
          ((t.take I a b).remove I a) := by
        have hTemp : Sized d (s.1, s.2.set b.val a.val) := by
          refine ⟨hInv.1.1, by simpa using hInv.1.2.1, ?_⟩
          intro j hj
          exact (List.mem_or_eq_of_mem_set hj).elim (hInv.1.2.2 j) (fun e => e ▸ a.isLt.le)
        rw [toRoster_remove p (s.1, s.2.set b.val a.val) hTemp, toRoster_take p s hInv.1]
      have shorter : vertices ((t.take I a b).remove I a) < vertices t :=
        (vertices_remove (t.take I a b) a
          (show a ∈ (t.take I a b).active from leaf.1.1)).trans (vertices_take t a b leaf.1.2.1)
      have raw :
          leafStep upper d s = if upper || decide (spent d s.2 a.val < 1) then
            (s.1.set a.val false, s.2.set b.val a.val) else (s.1.set a.val false, s.2) := by
        dsimp only [leafStep]
        rw [hForce]
        simp only [Bool.false_eq_true, if_false, show (agentLeaves d s).isEmpty = false from nonempty,
          Bool.not_false, if_true]
        dsimp only [d]
        rw [← ha, ← hb]
      cases upper with
      | true =>
        have hMove : leafStep true d s = (s.1.set a.val false, s.2.set b.val a.val) := by simpa using raw
        have hU : t.upperInvariant I w := hInv.2
        refine ⟨⟨shapeNext, ?_⟩, ?_⟩
        · change (toRoster p (leafStep true d s)).upperInvariant I w
          rw [hMove, take_remove]
          exact t.upper_take_leaf I w a b hU leaf
        · rw [hMove, take_remove]
          exact shorter
      | false =>
        have hC : t.lowerInvariant I w := hInv.2
        by_cases hs : spent d s.2 a.val < 1
        · have hMove : leafStep false d s = (s.1.set a.val false, s.2.set b.val a.val) := by
            simpa [hs] using raw
          have hSpend : t.spending I w a < 1 := by
            rw [← spent_agrees p s w hP a]
            exact_mod_cast hs
          refine ⟨⟨shapeNext, ?_⟩, ?_⟩
          · change (toRoster p (leafStep false d s)).lowerInvariant I w
            rw [hMove, take_remove]
            exact t.take_deficient_leaf I w a b hC leaf hSpend
          · rw [hMove, take_remove]
            exact shorter
        · have hMove : leafStep false d s = (s.1.set a.val false, s.2) := by simpa [hs] using raw
          have hSpend : 1 ≤ t.spending I w a := by
            rw [← spent_agrees p s w hP a]
            exact_mod_cast le_of_not_gt hs
          obtain ⟨j, k, hne, jLive, kLive⟩ := hTwo b leaf.1.2.1
          have alternative : ∃ j, t.isLive I w j b ∧ j ≠ a := by
            by_cases hja : j = a
            · exact ⟨k, kLive, fun hka => hne (hja.trans hka.symm)⟩
            · exact ⟨j, jLive, hja⟩
          obtain ⟨j, hLive, hOther⟩ := alternative
          refine ⟨⟨shapeNext, ?_⟩, ?_⟩
          · change (toRoster p (leafStep false d s)).lowerInvariant I w
            rw [hMove, toRoster_remove p s hInv.1]
            exact t.remove_satisfied_leaf I w a j b hw hC leaf hLive hOther hSpend
          · rw [hMove, toRoster_remove p s hInv.1]
            exact vertices_remove t a leaf.1.1
    cases upper with
    | true =>
      have hU : t.upperInvariant I w := hInv.2
      exact viaAgent rfl hU.2.2.2
    | false =>
      have hC : t.lowerInvariant I w := hInv.2
      cases hG : (goodLeaves d s).isEmpty with
      | true => exact viaAgent (by simp [hG]) (lower_two p s w hB hC hG)
      | false =>
        obtain ⟨i, g, hi, hg, hLive, hOnly⟩ := choose_good p s w hB hG
        have hStep : leafStep false d s = (s.1, s.2.set g.val i.val) := by
          dsimp only [leafStep]
          simp only [hG, Bool.not_false, Bool.and_self, if_true]
          dsimp only [d]
          rw [← hg, ← hi]
        refine ⟨⟨leaf_step_sized false d s hInv.1, ?_⟩, ?_⟩
        · change (toRoster p (leafStep false d s)).lowerInvariant I w
          rw [hStep, toRoster_take p s hInv.1]
          exact t.take_only_bidder I w i g hC hLive hOnly
        · rw [hStep, toRoster_take p s hInv.1]
          exact vertices_take t i g hLive.2.1

private theorem leaf_done (p : Packet) (w : p.inst.Weights)
    (hB : ∀ (i : p.inst.Agent) (g : p.inst.Good),
      marked p.pack i.val g.val = true ↔ p.inst.IsHighestBidder w i g)
    (hP : ∀ g : p.inst.Good, (RoundData.price p.pack g.val : ℝ) = p.inst.price w g)
    (hw : p.inst.Positive w) (hF : p.inst.IsForest w) (hC : p.inst.Covers w) (upper : Bool) :
    invariant p w upper (leafOutput upper p.pack) ∧ finished p (leafOutput upper p.pack) := by
  have invStart : invariant p w upper (start upper p.pack) := by
    refine ⟨start_sized upper _, ?_⟩
    cases upper
    · exact lower_start p w hC
    · exact upper_start_raw p w hB
  have preserves (s : Roster) (hs : invariant p w upper s) :
      invariant p w upper (leafStep upper p.pack s) := by
    by_cases hDone : finished p s
    · rwa [(leaf_moves p w hB hP hw hF upper s hs).1 hDone]
    · exact ((leaf_moves p w hB hP hw hF upper s hs).2 hDone).1
  exact bounded_descent (leafStep upper p.pack) (invariant p w upper) (finished p)
    (fun s => vertices (toRoster p s)) preserves
    (fun s hs => (leaf_moves p w hB hP hw hF upper s hs).1)
    (fun s hs hn => ((leaf_moves p w hB hP hw hF upper s hs).2 hn).2)
    (p.inst.n + p.inst.m) (start upper p.pack) invStart (vertices_le _)

set_option maxHeartbeats 2000000 in
theorem round_correct (p : Packet) (hw : p.inst.Positive (fun i => (p.weights i : ℝ)))
    (hF : p.inst.IsForest (fun i => (p.weights i : ℝ)))
    (hC : p.inst.Covers (fun i => (p.weights i : ℝ)))
    (hU : p.inst.ForcedFeasible (fun i => (p.weights i : ℝ))) :
    ∃ A : p.inst.Allocation,
      p.inst.IsSupported (fun i => (p.weights i : ℝ)) A ∧
      p.inst.Bands (fun i => (p.weights i : ℝ)) A 1 ∧ emit p.pack (roundOwners p.pack) = encodeAllocation A := by
  classical
  let I := p.inst
  let w : I.Weights := fun i => (p.weights i : ℝ)
  let d := p.pack
  obtain ⟨hp, hB⟩ := packet_agrees p hw
  let low := leafOutput false d
  let up := leafOutput true d
  have hLow := leaf_done p w hB hp hw hF hC false
  have hUp := leaf_done p w hB hp hw hF hC true
  let C := (toRoster p low).owner
  let A := (toRoster p up).owner
  have hLF : (toRoster p low).assigned = Finset.univ := hLow.2
  have hUF : (toRoster p up).assigned = Finset.univ := hUp.2
  have hCover : I.IsSupported w C ∧ I.LowerBand w C 1 :=
    (toRoster p low).lower_complete I w hLow.1.2 hLF
  have hAbove : I.IsSupported w A ∧ I.UpperBand w A 1 :=
    (toRoster p up).upper_complete I w hw hU hUp.1.2 hUF
  let read (xs : List ℕ) := toRoster p (up.1, xs)
  let allocation (xs : List ℕ) := (read xs).owner
  let good (xs : List ℕ) := I.LowerBand w (allocation xs) 1
  let inv (xs : List ℕ) : Prop := Sized d (up.1, xs) ∧ (read xs).assigned = Finset.univ ∧
    I.IsSupported w (allocation xs) ∧ I.UpperBand w (allocation xs) 1
  let μ (xs : List ℕ) := (I.disagreement (allocation xs) C).card
  let step := repairStep d low.2
  have invStart : inv up.2 := ⟨hUp.1.1, hUF, hAbove.1, hAbove.2⟩
  have hLowSized : Sized d (up.1, low.2) := ⟨hUp.1.1.1, hLow.1.1.2⟩
  have rawCover (g : I.Good) : owner d low.2 g.val = (C g).val := by
    symm
    exact owner_valid p low g (by rw [hLF]; exact Finset.mem_univ _)
  have via_spending (xs : List ℕ) (hx : inv xs) (i : I.Agent) :
      (spent d xs i.val : ℝ) = I.bundlePrice w (FairDivision.bundle (allocation xs) i) := by
    calc
      _ = (read xs).spending I w i := spent_agrees p (up.1, xs) w hp i
      _ = _ := by
        rw [Instance.Roster.spending, hx.2.1]
        rfl
  have eligible (xs : List ℕ) (hx : inv xs) (g : I.Good) :
      g.val ∈ transferCandidates d low.2 xs ↔
        allocation xs g ≠ C g ∧ I.bundlePrice w (FairDivision.bundle (allocation xs) (C g)) < 1 := by
    have rawCurrent : owner d xs g.val = (allocation xs g).val := by
      symm
      exact owner_valid p (up.1, xs) g (by change g ∈ (read xs).assigned; rw [hx.2.1]; exact Finset.mem_univ _)
    unfold transferCandidates
    rw [List.mem_filter, List.mem_range, Bool.and_eq_true_iff, decide_eq_true_eq, decide_eq_true_eq,
      rawCover, rawCurrent]
    rw [← via_spending xs hx (C g)]
    constructor
    · rintro ⟨_, hne, h⟩
      refine ⟨fun he => hne (congrArg Fin.val he), ?_⟩
      exact_mod_cast h
    · rintro ⟨hne, h⟩
      refine ⟨g.isLt, fun he => hne (Fin.ext he), ?_⟩
      exact_mod_cast h
  have fixed (xs : List ℕ) (hx : inv xs) (hGood : good xs) : step xs = xs := by
    let candidates := transferCandidates d low.2 xs
    have empty : candidates.isEmpty = true := by
      cases he : candidates.isEmpty
      · obtain ⟨u, hu⟩ := List.isEmpty_eq_false_iff_exists_mem.mp he
        let g : I.Good := ⟨u, List.mem_range.mp (List.mem_filter.mp hu).1⟩
        have hTake := (eligible xs hx g).mp hu
        exact (not_lt_of_ge (hGood (C g)) hTake.2).elim
      · rfl
    simp [step, repairStep, show (transferCandidates d low.2 xs).isEmpty = true from empty]
  have moves (xs : List ℕ) (hx : inv xs) (hg : ¬ good xs) :
      inv (step xs) ∧ μ (step xs) < μ xs := by
    have hWrong : ∃ i, I.bundlePrice w (FairDivision.bundle (allocation xs) i) < 1 := by
      simp only [good, Instance.LowerBand, not_forall, not_le] at hg
      exact hg
    obtain ⟨i, hSpend⟩ := hWrong
    obtain ⟨g, hgC, hgA, _⟩ := I.transfer_toward_cover w C (allocation xs) 1 i hw hCover.1 hCover.2
      hx.2.2.1 hx.2.2.2 hSpend
    let candidates := transferCandidates d low.2 xs
    have want : g.val ∈ candidates := (eligible xs hx g).mpr
      ⟨fun e => hgA (e.trans hgC), hgC ▸ hSpend⟩
    have hNE : candidates.isEmpty = false :=
      List.isEmpty_eq_false_iff_exists_mem.mpr ⟨g.val, want⟩
    let selected := candidates.headD 0
    have hMem : selected ∈ candidates := head_exists _ hNE
    let a : I.Good := ⟨selected, List.mem_range.mp (List.mem_filter.mp hMem).1⟩
    have hCandidate := (eligible xs hx a).mp hMem
    have hRaw : step xs = xs.set a.val (C a).val := by
      dsimp only [step, repairStep]
      change (if candidates.isEmpty then xs else xs.set selected (owner d low.2 selected)) = _
      simp only [hNE, Bool.false_eq_true, if_false]
      exact congrArg (xs.set selected) (rawCover a)
    have changed : read (step xs) = (read xs).take I (C a) a := by
      rw [hRaw]
      exact toRoster_take p (up.1, xs) hx.1 (C a) a
    have hYes := Instance.Roster.transfer_chosen I w C (allocation xs) a hw hCover.1
      hx.2.2.1 hx.2.2.2 hCandidate.1 hCandidate.2
    have ownerEq : allocation (step xs) = Function.update (allocation xs) a (C a) := by
      change (read (step xs)).owner = _
      rw [changed]
      rfl
    refine ⟨⟨repair_step_sized d low.2 xs up.1 hLowSized hx.1, ?_, ?_⟩, ?_⟩
    · rw [changed]
      simp [Instance.Roster.take, hx.2.1]
    · rw [ownerEq]
      exact ⟨hYes.1, hYes.2.1⟩
    · have hCard := hYes.2.2
      unfold μ
      rw [ownerEq]
      omega
  have preserves (xs : List ℕ) (hx : inv xs) : inv (step xs) := by
    by_cases hxG : good xs
    · rwa [fixed xs hx hxG]
    · exact (moves xs hx hxG).1
  have clock : μ up.2 ≤ I.m := by
    simpa [μ] using Finset.card_le_univ (I.disagreement (allocation up.2) C)
  have final := bounded_descent step inv good μ preserves fixed (fun xs hInv hNot => (moves xs hInv hNot).2)
    I.m up.2 invStart clock
  let owners := roundOwners d
  have hFinal : inv owners ∧ good owners := final
  refine ⟨allocation owners, hFinal.1.2.2.1, ⟨hFinal.2, hFinal.1.2.2.2⟩, ?_⟩
  have hOwners : owners = List.ofFn (fun g : I.Good => (allocation owners g).val) := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using (show owners.length = I.m from hFinal.1.1.2.1)
    · intro j hj hk
      let g : I.Good := ⟨j, by simpa using hk⟩
      have assigned : g ∈ (read owners).assigned := by rw [hFinal.1.2.1]; exact Finset.mem_univ _
      have hVal : (allocation owners g).val = owner d owners j :=
        owner_valid p (up.1, owners) g assigned
      rw [List.getElem_ofFn, ← read_get d.agents owners j hj]
      exact hVal.symm
  change encodeNat d.agents ++ encodeNat d.goods ++ owners.flatMap encodeNat =
    encodeAllocation (allocation owners)
  exact congrArg (fun xs : List ℕ => encodeNat d.agents ++ encodeNat d.goods ++ xs.flatMap encodeNat) hOwners

private abbrev natList := listCode Nat.bits
private abbrev boolList := listCode boolCode
private abbrev slices := prodCode (listCode boolList) (listCode ratCode)
private abbrev fields := prodCode unaryCode slices
private abbrev withRoster := prodCode packedCode rosterCode

private noncomputable def expose : Procedure packedCode (prodCode unaryCode fields)
    (fun d => (d.agents, d.goods, d.bidders, d.prices)) :=
  (identity _).precompose (fun d : Packed => (d.agents, d.goods, d.bidders, d.prices))

private noncomputable def countAgents : Procedure packedCode unaryCode Packed.agents :=
  (first unaryCode fields).comp expose

private noncomputable def countGoods : Procedure packedCode unaryCode Packed.goods :=
  (first unaryCode slices).comp ((second unaryCode fields).comp expose)

private noncomputable def clipped {α : Type} (ea : α → Word) (fallback : α) :
    Procedure (prodCode Nat.bits (prodCode ea (listCode ea))) (listCode ea)
      (fun p => p.2.2.set p.1 p.2.1) := by
  let context := prodCode Nat.bits (prodCode ea (listCode ea))
  let vals := (second ea (listCode ea)).comp (second Nat.bits (prodCode ea (listCode ea)))
  let current := unaryToBits.comp (first unaryCode context)
  let row := second unaryCode context
  let index := (first Nat.bits (prodCode ea (listCode ea))).comp row
  let replacement := ((first ea (listCode ea)).comp (second Nat.bits (prodCode ea (listCode ea)))).comp row
  let previous := (listGet ea fallback).comp (current.pair (vals.comp row))
  let matched := Control.Native.natEqP.comp (index.pair current)
  let cell : Procedure (prodCode unaryCode context) ea
      (fun p => if p.2.1 = p.1 then p.2.2.1 else readCell fallback p.2.2.2 p.1) :=
    (conditional matched replacement previous).congrFun (by intro p; simp [Function.comp_apply, readCell])
  let tab := Procedure.tabulate (ea := context)
    (f := fun p i => if p.1 = i then p.2.1 else readCell fallback p.2.2 i) fallback cell
  let count := (Control.Native.rowSizeP ea fallback).comp vals
  exact (tab.comp (count.pair (identity context))).congrFun (by
    intro p
    change (List.range p.2.2.length).map
      (fun j => if p.1 = j then p.2.1 else readCell fallback p.2.2 j) = p.2.2.set p.1 p.2.1
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      have hLen : j < p.2.2.length := by simpa using hj'
      simp only [List.getElem_map, List.getElem_range, List.getElem_set]
      by_cases hIndex : p.1 = j
      · simp [hIndex]
      · simp only [if_neg hIndex, readCell, List.headD_eq_head?_getD, List.head?_drop,
          List.getElem?_eq_getElem hLen, Option.getD_some])

private noncomputable def filterRange {α : Type} {e : α → Word} {n : α → ℕ}
    {predicate : α × ℕ → Bool} (count : Procedure e unaryCode n)
    (test : Procedure (prodCode e Nat.bits) boolCode predicate) :
    Procedure e natList (fun x => (List.range (n x)).filter fun k => predicate (x, k)) :=
  (Learning.BitMachine.filterWithP 0 test).comp
    ((Control.Native.addressRangeP.comp count).pair (identity e))

private noncomputable def lengthOne : Procedure natList boolCode (fun xs => decide (xs.length = 1)) :=
  Control.Native.natEqP.comp ((listLength Nat.bits 0).pair (constant natList Nat.bits 1))

private noncomputable def testMark :
    Procedure (prodCode packedCode (prodCode Nat.bits Nat.bits)) boolCode
      (fun p => marked p.1 p.2.1 p.2.2) := by
  let pair := prodCode Nat.bits Nat.bits
  let d := first packedCode pair
  let ij := second packedCode pair
  let agents := (first Nat.bits Nat.bits).comp ij
  let goods := (second Nat.bits Nat.bits).comp ij
  let grid := ((first (listCode boolList) (listCode ratCode)).comp
    ((second unaryCode slices).comp ((second unaryCode fields).comp expose))).comp d
  let col := (listGet boolList []).comp (goods.pair grid)
  exact ((listGet boolCode false).comp (agents.pair col)).congrFun (by intro p; rfl)

private noncomputable def testPrice :
    Procedure (prodCode packedCode Nat.bits) ratCode (fun p => price p.1 p.2) := by
  let d := first packedCode Nat.bits
  let g := second packedCode Nat.bits
  let prices := ((second (listCode boolList) (listCode ratCode)).comp
    ((second unaryCode slices).comp ((second unaryCode fields).comp expose))).comp d
  exact ((listGet ratCode 0).comp (g.pair prices)).congrFun (by intro p; rfl)

private noncomputable def readOwner :
    Procedure (prodCode (prodCode packedCode natList) Nat.bits) Nat.bits
      (fun p => owner p.1.1 p.1.2 p.2) := by
  let d := first packedCode natList
  let s := second packedCode natList
  let context := prodCode packedCode natList
  let input := prodCode context Nat.bits
  let xy := first context Nat.bits
  let idx := second context Nat.bits
  -- Use a constant fallback in the native lookup and choose the sentinel only beyond length.
  let owners := s.comp xy
  let length := (listLength Nat.bits 0).comp owners
  let outside := binaryLe.comp (length.pair idx)
  let fallback := (unaryToBits.comp countAgents).comp (d.comp xy)
  let actual := (listGet Nat.bits 0).comp (idx.pair owners)
  exact (conditional outside fallback actual).congrFun (by
    intro p
    simp only [Function.comp_apply, decide_eq_true_eq, id_eq]
    change (if p.1.2.length ≤ p.2 then p.1.1.agents else readCell 0 p.1.2 p.2) = owner p.1.1 p.1.2 p.2
    by_cases hp : p.1.2.length ≤ p.2
    · simp [hp, owner, readCell, List.drop_eq_nil_of_le hp]
    · have hi : p.2 < p.1.2.length := lt_of_not_ge hp
      simp only [if_neg hp, owner, readCell, List.headD_eq_head?_getD, List.head?_drop,
        List.getElem?_eq_getElem hi, Option.getD_some])

private noncomputable def testPending : Procedure (prodCode withRoster Nat.bits) boolCode
    (fun p => pending p.1.1 p.1.2 p.2) := by
  let out := first withRoster Nat.bits
  let position := second withRoster Nat.bits
  let d := (first packedCode rosterCode).comp out
  let owners := ((second boolList natList).comp (second packedCode rosterCode)).comp out
  let currentOwner := readOwner.comp ((d.pair owners).pair position)
  let n := (unaryToBits.comp countAgents).comp d
  exact (binaryLe.comp (n.pair currentOwner)).congrFun (by intro p; rfl)

private noncomputable def listBidders :
    Procedure (prodCode (prodCode packedCode boolList) Nat.bits) natList
      (fun p => bidders p.1.1 p.1.2 p.2) := by
  let primary := prodCode packedCode boolList
  let ctx := prodCode primary Nat.bits
  let whole := first ctx Nat.bits
  let i := second ctx Nat.bits
  let market := ((first packedCode boolList).comp (first primary Nat.bits)).comp whole
  let flags := ((second packedCode boolList).comp (first primary Nat.bits)).comp whole
  let g := (second primary Nat.bits).comp whole
  let active := (listGet boolCode false).comp (i.pair flags)
  let m := testMark.comp (market.pair (i.pair g))
  let count := (countAgents.comp (first packedCode boolList)).comp (first primary Nat.bits)
  exact (filterRange count (boolAnd.comp (active.pair m))).congrFun (by intro p; rfl)

private noncomputable def listNeighbors :
    Procedure (prodCode withRoster Nat.bits) natList
      (fun p => neighbors p.1.1 p.1.2 p.2) := by
  let ctx := prodCode withRoster Nat.bits
  let whole := first ctx Nat.bits
  let g := second ctx Nat.bits
  let i := (second withRoster Nat.bits).comp whole
  let d := (first withRoster Nat.bits).comp whole
  let market := (first packedCode rosterCode).comp d
  let wait := testPending.comp (d.pair g)
  let m := testMark.comp (market.pair (i.pair g))
  let count := (countGoods.comp (first packedCode rosterCode)).comp (first withRoster Nat.bits)
  exact (filterRange count (boolAnd.comp (wait.pair m))).congrFun (by intro p; rfl)

private noncomputable def scanGood : Procedure withRoster natList
    (fun p => goodLeaves p.1 p.2) := by
  let d := first packedCode rosterCode
  let state := second packedCode rosterCode
  let p := first withRoster Nat.bits
  let j := second withRoster Nat.bits
  let data := (d.pair ((first boolList natList).comp state)).comp p
  let degree := lengthOne.comp (listBidders.comp (data.pair j))
  exact (filterRange (countGoods.comp d) (boolAnd.comp (testPending.pair degree))).congrFun (by intro p; rfl)

private noncomputable def scanAgent : Procedure withRoster natList
    (fun p => agentLeaves p.1 p.2) := by
  let p := first withRoster Nat.bits
  let i := second withRoster Nat.bits
  let flags := ((first boolList natList).comp (second packedCode rosterCode)).comp p
  let active := (listGet boolCode false).comp (i.pair flags)
  let degree := lengthOne.comp listNeighbors
  let count := countAgents.comp (first packedCode rosterCode)
  exact (filterRange count (boolAnd.comp (active.pair degree))).congrFun (by intro p; rfl)

private noncomputable def spend :
    Procedure (prodCode (prodCode packedCode natList) Nat.bits) ratCode
      (fun p => spent p.1.1 p.1.2 p.2) := by
  let context := prodCode packedCode natList
  let query := prodCode context Nat.bits
  let input := prodCode unaryCode query
  let state := second unaryCode query
  let marketData := (first context Nat.bits).comp state
  let market := (first packedCode natList).comp marketData
  let i := (second context Nat.bits).comp state
  let g := unaryToBits.comp (first unaryCode query)
  let who := readOwner.comp (marketData.pair g)
  let matched := Control.Native.natEqP.comp (who.pair i)
  let value := testPrice.comp (market.pair g)
  let entry : Procedure input ratCode
      (fun p => if owner p.2.1.1 p.2.1.2 p.1 = p.2.2 then price p.2.1.1 p.1 else 0) :=
    (conditional matched value (constant input ratCode 0)).congrFun (by intro p; simp [Function.comp_apply])
  let all := Procedure.tabulate (ea := query)
    (f := fun p g => if owner p.1.1 p.1.2 g = p.2 then price p.1.1 g else 0) 0 entry
  let count := countGoods.comp ((first packedCode natList).comp (first context Nat.bits))
  exact (Control.Native.ratListSumP.comp (all.comp (count.pair (identity query)))).congrFun (by intro p; rfl)

noncomputable def startProcedure (upper : Bool) :
    Procedure packedCode rosterCode (start upper) := by
  let flag : Procedure (prodCode unaryCode emptyCode) boolCode (fun _ => true) :=
    constant _ _ true
  let flags := Procedure.tabulate (ea := emptyCode) (f := fun _ _ => true) false flag
  let n := countAgents
  let active := flags.comp (n.pair (constant packedCode emptyCode ()))
  have active_is (p : Packed) : (List.range p.agents).map (fun _ => true) = List.replicate p.agents true := by
    simp
  let asFlags : Procedure packedCode boolList (fun d => List.replicate d.agents true) :=
    active.congrFun active_is
  let data := prodCode packedCode boolList
  let field := prodCode unaryCode data
  let j := unaryToBits.comp (first unaryCode data)
  let extra := second unaryCode data
  let d := (first packedCode boolList).comp extra
  let bs := listBidders.comp (extra.pair j)
  let a := (unaryToBits.comp countAgents).comp d
  let firstVal := (Procedure.listHead (ea := Nat.bits) 0).comp bs
  let test := boolAnd.comp ((constant field boolCode upper).pair (lengthOne.comp bs))
  let one : Procedure field Nat.bits
      (fun p => let row := bidders p.2.1 p.2.2 p.1;
        if upper && decide (row.length = 1) then row.headD p.2.1.agents else p.2.1.agents) :=
    (conditional test firstVal a).congrFun (by
      intro p
      let row := bidders p.2.1 p.2.2 p.1
      change (if upper && decide (row.length = 1) then row.headD 0 else p.2.1.agents) =
        (if upper && decide (row.length = 1) then row.headD p.2.1.agents else p.2.1.agents)
      by_cases h : (upper && decide (row.length = 1)) = true
      · have hLen : row.length = 1 := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
        cases he : row with
        | nil => simp [he] at hLen
        | cons a as => simp [he]
      · simp [h])
  let all := Procedure.tabulate (ea := data)
    (f := fun p g => let row := bidders p.1 p.2 g;
      if upper && decide (row.length = 1) then row.headD p.1.agents else p.1.agents) 0 one
  let owners := all.comp (countGoods.pair ((identity packedCode).pair asFlags))
  exact (asFlags.pair owners).congrFun (by intro p; rfl)

noncomputable def leafStepProcedure (upper : Bool) :
    Procedure (prodCode packedCode rosterCode) rosterCode (fun p => leafStep upper p.1 p.2) := by
  let d := first packedCode rosterCode
  let s := second packedCode rosterCode
  let active := (first boolList natList).comp s
  let owners := (second boolList natList).comp s
  let chosenG := (Procedure.listHead (ea := Nat.bits) 0).comp scanGood
  let chosenI := (Procedure.listHead (ea := Nat.bits) 0).comp scanAgent
  let B := listBidders.comp ((d.pair active).pair chosenG)
  let N := listNeighbors.comp ((identity withRoster).pair chosenI)
  let forceI := (Procedure.listHead (ea := Nat.bits) 0).comp B
  let loneG := (Procedure.listHead (ea := Nat.bits) 0).comp N
  let combine := clipped Nat.bits 0
  let giveForced := active.pair (combine.comp (chosenG.pair (forceI.pair owners)))
  let inactive := (clipped boolCode false).comp (chosenI.pair ((constant withRoster boolCode false).pair active))
  let giveLone := combine.comp (loneG.pair (chosenI.pair owners))
  let iMoney := spend.comp ((d.pair owners).pair chosenI)
  let deficient := Arithmetic.ratLt.comp (iMoney.pair (constant withRoster ratCode 1))
  let useGood := boolOr.comp ((constant withRoster boolCode upper).pair deficient)
  let viaAgent := inactive.pair (conditional useGood giveLone owners)
  let foundAgent := boolNot.comp ((listEmpty (ea := Nat.bits)).comp scanAgent)
  let foundGood := boolNot.comp ((listEmpty (ea := Nat.bits)).comp scanGood)
  let useForced := boolAnd.comp ((constant withRoster boolCode (!upper)).pair foundGood)
  let result := conditional useForced giveForced (conditional foundAgent viaAgent s)
  have pair_if (flags : List Bool) (yes no : List ℕ) (c : Prop) [Decidable c] :
      (flags, if c then yes else no) = (if c then (flags, yes) else (flags, no)) := by
    split <;> rfl
  exact result.congrFun (by
    intro p
    cases upper <;> simp [Function.comp_apply, leafStep, pair_if])

private theorem raw_dimensions (d : Packed) : d.agents + d.goods ≤ (packedCode d).length := by
  simp only [packedCode, prodCode, pairBits_length, unaryCode, List.length_replicate]
  omega

private theorem roster_code_bound (d : Packed) (s : Roster) (h : Sized d s)
    (N : ℕ) (hN : d.agents + d.goods ≤ N) :
    (rosterCode s).length ≤ 32 * (N + 1)^2 := by
  let n := d.agents
  let m := d.goods
  have hLabel (i : ℕ) (hi : i ∈ s.2) : i.bits.length ≤ n + 1 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    exact (Nat.lt_succ_of_le (h.2.2 i hi)).trans
      (show n + 1 < 2 ^ (n + 1) from Nat.lt_two_pow_self)
  have flags : (listCode boolCode s.1).length ≤ n * 4 + 1 := by
    have hf := listCode_length_map_bound boolCode id s.1 1 (by intro x hx; rfl)
    simpa only [List.map_id, h.1, show 2 * 1 + 2 = 4 by decide] using hf
  have labels : (listCode Nat.bits s.2).length ≤ m * (2 * (n + 1) + 2) + 1 := by
    simpa only [List.map_id, h.2.1] using listCode_length_map_bound Nat.bits id s.2 (n + 1) hLabel
  have hn : n ≤ N := (Nat.le_add_right _ _).trans hN
  have hm : m ≤ N := (Nat.le_add_left _ _).trans hN
  have hQuadratic : m * (2 * (n + 1) + 2) ≤ N * (2 * (N + 1) + 2) := by
    apply Nat.mul_le_mul hm
    omega
  simp only [rosterCode, prodCode, pairBits_length]
  calc
    _ ≤ 2 * (n * 4 + 1) + (m * (2 * (n + 1) + 2) + 1) + 1 := by omega
    _ ≤ 2 * (N * 4 + 1) + (N * (2 * (N + 1) + 2) + 1) + 1 := by omega
    _ ≤ _ := by nlinarith

private noncomputable def iterateRoster {C : Type} (code : C → Word) (data : C → Packed)
    (count : C → ℕ) (startRoster : C → Roster) (next : C → Roster → Roster)
    (clock : Procedure code unaryCode count) (bootstrap : Procedure code rosterCode startRoster)
    (advance : Procedure (prodCode code rosterCode) rosterCode (fun p => next p.1 p.2))
    (hStart : ∀ c, Sized (data c) (startRoster c))
    (hNext : ∀ c s, Sized (data c) s → Sized (data c) (next c s))
    (hDims : ∀ c, (data c).agents + (data c).goods ≤ (code c).length)
    (hWidth : ∀ d s, Sized d s → ∀ N : ℕ, d.agents + d.goods ≤ N →
      (rosterCode s).length ≤ 32 * (N + 1)^2) :
    Procedure code rosterCode (fun c => ((next c)^[count c]) (startRoster c)) := by
  let Valid := {p : C × Roster // Sized (data p.1) p.2}
  let encode (p : Valid) := prodCode code rosterCode p.val
  let step (p : Valid) : Valid := ⟨(p.val.1, next p.val.1 p.val.2), hNext _ _ p.property⟩
  let init (c : C) : Valid := ⟨(c, startRoster c), hStart c⟩
  let progress : Procedure encode encode step :=
    (((first code rosterCode).pair advance).precompose (fun p : Valid => p.val)).result (by intro p; rfl)
  let begin : Procedure code encode init :=
    ((identity code).pair bootstrap).result (by intro c; rfl)
  have static (t : ℕ) (p : Valid) : ((step^[t]) p).val.1 = p.val.1 := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ih
  have mutable (t : ℕ) (p : Valid) : ((step^[t]) p).val.2 = ((next p.val.1)^[t]) p.val.2 := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change next ((step^[t]) p).val.1 ((step^[t]) p).val.2 = _
      rw [static, ih]
  let width : Polynomial ℕ := Polynomial.C 64 * (Polynomial.X + 1)^2
  let run := progress.iterate width (by
    intro time p t _
    let N := time + (encode p).length
    let out := (step^[t]) p
    have hCode : (code p.val.1).length ≤ N := by
      simp only [N, encode, prodCode, pairBits_length]
      omega
    have hDim := (hDims p.val.1).trans hCode
    have hRoster : (rosterCode out.val.2).length ≤ 32 * (N + 1)^2 := by
      apply hWidth (data out.val.1) out.val.2 out.property
      rwa [show out.val.1 = p.val.1 from static t p]
    have hSquare : N + 1 ≤ (N + 1)^2 := by
      simpa only [pow_one] using
        (Nat.pow_le_pow_right (show 0 < N + 1 by omega) (show 1 ≤ 2 by decide))
    change (encode out).length ≤ width.eval N
    simp only [encode, prodCode, pairBits_length, width, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    rw [show out.val.1 = p.val.1 from static t p]
    omega)
  let obtainRoster := (second code rosterCode).precompose (fun p : Valid => p.val)
  exact (obtainRoster.comp (run.comp (clock.pair begin))).congrFun (by
    intro c
    exact mutable (count c) (init c))

noncomputable def leafProcedure (upper : Bool) :
    Procedure packedCode rosterCode (leafOutput upper) := by
  let clock : Procedure packedCode unaryCode (fun d => d.agents + d.goods) :=
    unaryAdd.comp (countAgents.pair countGoods)
  exact iterateRoster packedCode id (fun d => d.agents + d.goods) (start upper) (leafStep upper)
    clock (startProcedure upper) (leafStepProcedure upper) (start_sized upper) (leaf_step_sized upper)
    raw_dimensions roster_code_bound

private abbrev repairCode := prodCode packedCode (prodCode natList natList)

noncomputable def repairStepProcedure :
    Procedure (prodCode packedCode (prodCode (listCode Nat.bits) (listCode Nat.bits)))
      (listCode Nat.bits) (fun p => repairStep p.1 p.2.1 p.2.2) := by
  let d := first packedCode (prodCode natList natList)
  let vectors := second packedCode (prodCode natList natList)
  let cover := (first natList natList).comp vectors
  let current := (second natList natList).comp vectors
  let source := first repairCode Nat.bits
  let g := second repairCode Nat.bits
  let claimed := readOwner.comp (((d.pair cover).comp source).pair g)
  let existing := readOwner.comp (((d.pair current).comp source).pair g)
  let notSame := boolNot.comp (Control.Native.natEqP.comp (existing.pair claimed))
  let spending := spend.comp (((d.pair current).comp source).pair claimed)
  let deficient := Arithmetic.ratLt.comp (spending.pair (constant (prodCode repairCode Nat.bits) ratCode 1))
  let candidates : Procedure repairCode natList (fun p => transferCandidates p.1 p.2.1 p.2.2) :=
    (filterRange (countGoods.comp d) (boolAnd.comp (notSame.pair deficient))).congrFun (by
      intro p
      simp [Function.comp_apply, transferCandidates])
  let selected := (Procedure.listHead (ea := Nat.bits) 0).comp candidates
  let recipient := readOwner.comp ((d.pair cover).pair selected)
  let changed := (clipped Nat.bits 0).comp (selected.pair (recipient.pair current))
  exact (conditional ((listEmpty (ea := Nat.bits)).comp candidates) current changed).congrFun
    (by intro p; rfl)

private theorem leafOutput_sized (upper : Bool) (d : Packed) : Sized d (leafOutput upper d) := by
  have each (t : ℕ) : Sized d (((leafStep upper d)^[t]) (start upper d)) := by
    induction t with
    | zero => exact start_sized upper d
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact leaf_step_sized upper d _ ih
  exact each (d.agents + d.goods)

private noncomputable def emitOwnerFields :
    Procedure (prodCode unaryCode (prodCode unaryCode (listCode Nat.bits))) id
      (fun p => encodeNat p.1 ++ encodeNat p.2.1 ++ p.2.2.flatMap encodeNat) := by
  let labels := listCode Nat.bits
  let write := Wire.writeNat.comp unaryToBits
  let n := write.comp (first unaryCode (prodCode unaryCode labels))
  let other := second unaryCode (prodCode unaryCode labels)
  let m := (write.comp (first unaryCode labels)).comp other
  let words := (Procedure.listMap (0 : ℕ) ([] : Word) Wire.writeNat).comp ((second unaryCode labels).comp other)
  let owners := Wire.flatten.comp words
  let result := Procedure.append.comp (n.pair (Procedure.append.comp (m.pair owners)))
  have flatten_map (xs : List ℕ) : (xs.map encodeNat).flatten = xs.flatMap encodeNat := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]
  exact result.congrFun (by
    intro p
    simp only [Function.comp_apply, id_eq, Prod.fst, Prod.snd, flatten_map, List.append_assoc])

noncomputable def roundProcedure :
    Procedure packedCode id (fun p => emit p (roundOwners p)) := by
  let pairs := prodCode rosterCode rosterCode
  let initialCode := prodCode packedCode pairs
  let Static := {s : Packed × Roster × Roster // Sized s.1 s.2.1 ∧ Sized s.1 s.2.2}
  let staticCode (s : Static) := initialCode s.val
  let initial (d : Packed) : Static :=
    ⟨(d, leafOutput false d, leafOutput true d), leafOutput_sized false d, leafOutput_sized true d⟩
  let setup : Procedure packedCode staticCode initial :=
    ((identity packedCode).pair ((leafProcedure false).pair (leafProcedure true))).result (by intro d; rfl)
  let exposeStatic := (identity initialCode).precompose (fun p : Static => p.val)
  let data := (first packedCode pairs).comp exposeStatic
  let cover := ((second boolList natList).comp ((first rosterCode rosterCode).comp
    (second packedCode pairs))).comp exposeStatic
  let initialRoster := ((second rosterCode rosterCode).comp (second packedCode pairs)).comp exposeStatic
  let clock := countGoods.comp data
  let saved := first staticCode rosterCode
  let live := second staticCode rosterCode
  let flags := (first boolList natList).comp live
  let owners := (second boolList natList).comp live
  let repaired := repairStepProcedure.comp ((data.comp saved).pair ((cover.comp saved).pair owners))
  let next (p : Static) (s : Roster) : Roster := (s.1, repairStep p.val.1 p.val.2.1.2 s.2)
  let actualStep : Procedure (prodCode staticCode rosterCode) rosterCode (fun p => next p.1 p.2) :=
    (flags.pair repaired).congrFun (by intro p; rfl)
  have dims (p : Static) : p.val.1.agents + p.val.1.goods ≤ (staticCode p).length := by
    have h := raw_dimensions p.val.1
    simp only [staticCode, initialCode, prodCode, pairBits_length]
    omega
  have next_sized (p : Static) (s : Roster) (hs : Sized p.val.1 s) : Sized p.val.1 (next p s) :=
    repair_step_sized p.val.1 _ _ _ ⟨hs.1, p.property.1.2⟩ hs
  let merged := iterateRoster staticCode (fun p => p.val.1) (fun p => p.val.1.goods)
    (fun p => p.val.2.2) next clock initialRoster actualStep (fun p => p.property.2)
    next_sized dims roster_code_bound
  have readout (p : Static) (s : Roster) (t : ℕ) :
      ((next p)^[t] s).2 = ((repairStep p.val.1 p.val.2.1.2)^[t]) s.2 := by
    induction t with
    | zero => rfl
    | succ k ih =>
      simp only [Function.iterate_succ_apply']
      change repairStep p.val.1 p.val.2.1.2 (((next p)^[k]) s).2 = _
      rw [ih]
  let result := ((second boolList natList).comp merged).comp setup
  let serialized := emitOwnerFields.comp (countAgents.pair (countGoods.pair result))
  exact serialized.congrFun (by
    intro d
    change emit d (((next (initial d))^[d.goods]) (leafOutput true d)).2 = emit d (roundOwners d)
    rw [readout (initial d) (leafOutput true d) d.goods] <;> rfl)


end EF1FPO.RoundKernel
