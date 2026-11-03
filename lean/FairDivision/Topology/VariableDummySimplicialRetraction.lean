import FairDivision.Topology.VariableDummySimplicialHomotopy
import FairDivision.Topology.NerveConnectivity.NullHomotopy
import FairDivision.Topology.NerveConnectivity.RealizationEquiv

/-!
# Deformation retractions from contiguous vertex maps

A contiguous vertex map that lands in a subcomplex and fixes every vertex
there is a retraction after geometric realization. This packages the common
final step of the manuscript's dummy-saturation and forced-item arguments.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology

open NerveConnectivity

/-- Inclusion of a realized subcomplex into its ambient complex. -/
def variableRealizationInclusion {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (K L : PreAbstractSimplicialComplex
      (VariableUnlabeledVertex k m D r c))
    (hLK : L ≤ K) : C(simplicialRealization L, simplicialRealization K) where
  toFun x := ⟨x.1, hLK x.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

/-- A contiguous vertex map with image in `L` realizes as a continuous
retraction candidate from `K` to `L`. -/
noncomputable def variableRealizationRetraction {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (K L : PreAbstractSimplicialComplex
      (VariableUnlabeledVertex k m D r c))
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D r c)
    (hImage : ∀ S : Finset (VariableUnlabeledVertex k m D r c),
      S ∈ K → S.image f ∈ L) :
    C(simplicialRealization K, simplicialRealization L) where
  toFun x := ⟨stdSimplex.map f x.1, by
    change variableLotterySupport (stdSimplex.map f x.1) ∈ L
    have hx : variableLotterySupport x.1 ∈ K := x.2
    exact (L.isRelLowerSet_faces
      (hImage (variableLotterySupport x.1) hx)).2
        (variableLotterySupport_map_subset f x.1)
        (variableLotterySupport_nonempty _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (stdSimplex.continuous_map f).comp continuous_subtype_val

/-- The realized retraction is left-inverse to subcomplex inclusion when
`f` fixes every vertex of `L`. -/
theorem variableRealizationRetraction_comp_inclusion {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (K L : PreAbstractSimplicialComplex
      (VariableUnlabeledVertex k m D r c))
    (hLK : L ≤ K)
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D r c)
    (hImage : ∀ S : Finset (VariableUnlabeledVertex k m D r c),
      S ∈ K → S.image f ∈ L)
    (hFixed : ∀ S : Finset (VariableUnlabeledVertex k m D r c),
      S ∈ L → ∀ v ∈ S, f v = v) :
    (variableRealizationRetraction K L f hImage).comp
      (variableRealizationInclusion K L hLK) =
        ContinuousMap.id (simplicialRealization L) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact finiteSimplexMap_eq_self_of_support_fixed f x.1
    (hFixed (finiteSimplexSupport x.1) x.2)

/-- A contiguous vertex map whose image lies in a fixed subcomplex is a
homotopy equivalence with that subcomplex after realization. -/
noncomputable def variableRealizationRetraction_homotopyEquiv {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (K L : PreAbstractSimplicialComplex
      (VariableUnlabeledVertex k m D r c))
    (hLK : L ≤ K)
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D r c)
    (hContig : ∀ S : Finset (VariableUnlabeledVertex k m D r c),
      S ∈ K → S ∪ S.image f ∈ K)
    (hImage : ∀ S : Finset (VariableUnlabeledVertex k m D r c),
      S ∈ K → S.image f ∈ L)
    (hFixed : ∀ S : Finset (VariableUnlabeledVertex k m D r c),
      S ∈ L → ∀ v ∈ S, f v = v) :
    ContinuousMap.HomotopyEquiv
      (simplicialRealization K) (simplicialRealization L) := by
  let retr := variableRealizationRetraction K L f hImage
  let incl := variableRealizationInclusion K L hLK
  apply homotopyEquivOfRetraction retr incl
  · exact variableRealizationRetraction_comp_inclusion
      K L hLK f hImage hFixed
  · have hEq : incl.comp retr =
        variableRealizationMapOfContiguity K f hContig := by
      ext x
      rfl
    rw [hEq]
    exact (variableRealizationMapOfContiguity_homotopic_id
      K f hContig).symm

end FairDivision.Topology
