import FairDivision.Topology.NerveConnectivity.FiniteConeComplex

/-!
# Intersections of cone pieces

The base of one cone meets a subcone exactly in the base of that
subcone. These identities turn the two-stage cone filling into ordinary
finite closed-subcomplex pasting.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u

/-- A nonempty face with no apex has a nonempty old-vertex face. -/
theorem coneBaseFace_nonempty_of_no_apex {V : Type u} [Fintype V]
    {S : Finset (Option V)} (hS : S.Nonempty) (hno : none ∉ S) :
    (coneBaseFace S).Nonempty := by
  rcases hS with ⟨w, hw⟩
  cases w with
  | none => exact (hno hw).elim
  | some v => exact ⟨v, mem_coneBaseFace.mpr hw⟩

/-- Inclusion of base complexes follows inclusion of their old complexes. -/
theorem finiteConeBaseComplex_mono {V : Type u} [Fintype V]
    {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L) :
    finiteConeBaseComplex K ≤ finiteConeBaseComplex L := by
  intro S hS
  exact ⟨hS.1, hS.2.1, hKL hS.2.2⟩


/-- The base-copy construction preserves binary unions. -/
theorem finiteConeBaseComplex_sup {V : Type u} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) :
    finiteConeBaseComplex (K ⊔ L) =
      finiteConeBaseComplex K ⊔ finiteConeBaseComplex L := by
  ext S
  constructor
  · intro hS
    rcases hS.2.2 with hK | hL
    · exact Or.inl ⟨hS.1, hS.2.1, hK⟩
    · exact Or.inr ⟨hS.1, hS.2.1, hL⟩
  · rintro (hK | hL)
    · exact ⟨hK.1, hK.2.1, Or.inl hK.2.2⟩
    · exact ⟨hL.1, hL.2.1, Or.inr hL.2.2⟩

/-- The base-copy construction preserves binary intersections. -/
theorem finiteConeBaseComplex_inf {V : Type u} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) :
    finiteConeBaseComplex (K ⊓ L) =
      finiteConeBaseComplex K ⊓ finiteConeBaseComplex L := by
  ext S
  constructor
  · intro hS
    exact ⟨⟨hS.1, hS.2.1, hS.2.2.1⟩,
      ⟨hS.1, hS.2.1, hS.2.2.2⟩⟩
  · intro hS
    exact ⟨hS.1.1, hS.1.2.1, ⟨hS.1.2.2, hS.2.2.2⟩⟩

/-- The base of a subcone is the intersection of that cone with the
base of the larger cone. -/
theorem finiteConeBase_inf_cone {V : Type u} [Fintype V]
    {I K : PreAbstractSimplicialComplex V} (hIK : I ≤ K) :
    finiteConeBaseComplex K ⊓ finiteConeComplex I =
      finiteConeBaseComplex I := by
  ext S
  constructor
  · intro hS
    have hbase := coneBaseFace_nonempty_of_no_apex hS.1.1 hS.1.2.1
    exact ⟨hS.1.1, hS.1.2.1, hS.2.2 hbase⟩
  · intro hS
    exact ⟨finiteConeBaseComplex_mono hIK hS,
      finiteConeBaseComplex_le I hS⟩

/-- The base-plus-subcone partial domain belongs to the larger cone. -/
theorem finiteConeBase_sup_cone_le {V : Type u} [Fintype V]
    {I K : PreAbstractSimplicialComplex V} (hIK : I ≤ K) :
    finiteConeBaseComplex K ⊔ finiteConeComplex I ≤
      finiteConeComplex K := by
  exact sup_le (finiteConeBaseComplex_le K)
    (finiteConeComplex_mono hIK)

end FairDivision.Topology.NerveConnectivity
