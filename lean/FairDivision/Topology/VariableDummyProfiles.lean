import FairDivision.Topology.VariableDummyComplex

/-!
# Profile facts for variable-size auxiliary vertices

These are the position-dependent versions needed in the connectivity
induction. They follow from a labeled representative of each profile.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- A profile's real part avoids dummy items. -/
theorem variableProfile_real_disjoint_dummy {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (p : VariableUnlabeledVertex k m D r c) (i : Fin k) :
    Disjoint (p.1 i).1 D := by
  obtain ⟨X, hX⟩ := p.2
  rw [← congrArg Prod.fst (congrFun hX i)]
  exact Finset.sdiff_disjoint

/-- Real count plus dummy count equals this position's requirement. -/
theorem variableProfile_card {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (p : VariableUnlabeledVertex k m D r c) (i : Fin k) :
    (p.1 i).1.card + (p.1 i).2 = r i := by
  obtain ⟨X, hX⟩ := p.2
  rw [← congrArg Prod.fst (congrFun hX i),
      ← congrArg Prod.snd (congrFun hX i)]
  exact (Finset.card_sdiff_add_card_inter _ _).trans (X.2 i).1

/-- The dummy count respects this position's cap. -/
theorem variableProfile_dummy_le_cap {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (p : VariableUnlabeledVertex k m D r c) (i : Fin k) :
    (p.1 i).2 ≤ c i := by
  obtain ⟨X, hX⟩ := p.2
  rw [← congrArg Prod.snd (congrFun hX i)]
  exact (X.2 i).2

end FairDivision.Topology
