import FairDivision.Topology.UnlabeledDummyComplex

/-!
# Basic facts about an unlabeled-dummy vertex

A profile is realized by a valid partial allocation.  Consequently its real
bundle avoids the dummy set, its real cardinality plus dummy count is the
required bundle size, and its dummy count obeys the per-position cap.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- The real part of an auxiliary vertex contains no dummy items. -/
theorem unlabeledProfile_real_disjoint_dummy {k m r c : ℕ}
    {D : Finset (Fin m)} (p : UnlabeledDummyVertex k m r c D)
    (i : Fin k) : Disjoint (p.1 i).1 D := by
  obtain ⟨X, hX⟩ := p.2
  rw [← congrArg Prod.fst (congrFun hX i)]
  exact Finset.sdiff_disjoint

/-- The real cardinality and the dummy count add to the required size. -/
theorem unlabeledProfile_card {k m r c : ℕ}
    {D : Finset (Fin m)} (p : UnlabeledDummyVertex k m r c D)
    (i : Fin k) : (p.1 i).1.card + (p.1 i).2 = r := by
  obtain ⟨X, hX⟩ := p.2
  rw [← congrArg Prod.fst (congrFun hX i),
      ← congrArg Prod.snd (congrFun hX i)]
  exact (Finset.card_sdiff_add_card_inter _ _).trans (X.2 i).1

/-- The dummy count at a vertex respects the cap. -/
theorem unlabeledProfile_dummy_le_cap {k m r c : ℕ}
    {D : Finset (Fin m)} (p : UnlabeledDummyVertex k m r c D)
    (i : Fin k) : (p.1 i).2 ≤ c := by
  obtain ⟨X, hX⟩ := p.2
  rw [← congrArg Prod.snd (congrFun hX i)]
  exact (X.2 i).2

end FairDivision.Topology
