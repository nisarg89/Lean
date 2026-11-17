import FairDivision.Topology.NerveConnectivity.FiniteConeComplex
import FairDivision.Topology.NerveConnectivity.RealizationEquiv

/-!
# The base of a finite cone

The Option-vertex base copy is homeomorphic to the original finite
simplicial realization. This isolates the coordinate bookkeeping from
later cone fillings and open-cover gluing.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u

/-- The base copy of a finite complex has the original realization. -/
noncomputable def finiteConeBaseRealizationHomeomorph
    {V : Type u} [Fintype V] [Nonempty V]
    (K : PreAbstractSimplicialComplex V) :
    simplicialRealization K ≃ₜ
      simplicialRealization (finiteConeBaseComplex K) := by
  classical
  let v₀ : V := Classical.choice ‹Nonempty V›
  let back : Option V → V := fun w => w.getD v₀
  apply realizationHomeomorphOfVertexMaps K
    (finiteConeBaseComplex K) some back
  · intro S hS
    exact (mem_finiteConeBaseComplex_image_some_iff K S).2 hS
  · intro T hT
    have hface := finiteConeBaseComplex_face_image K hT
    have hEq : T.image back = coneBaseFace T := by
      rw [hface]
      ext v
      simp [back]
    rw [hEq]
    exact hT.2.2
  · intro S hS v hv
    rfl
  · intro T hT w hw
    cases w with
    | none => exact (hT.2.1 hw).elim
    | some v => rfl

/-- Inclusion of the cone base into the whole cone. -/
def finiteConeBaseInclusion {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    C(simplicialRealization (finiteConeBaseComplex K),
      simplicialRealization (finiteConeComplex K)) :=
  ContinuousMap.inclusion (simplicialRealization_mono
    (finiteConeBaseComplex_le K))

/-- The original realization as the base of its cone. -/
noncomputable def finiteConeBaseMap {V : Type u} [Fintype V] [Nonempty V]
    (K : PreAbstractSimplicialComplex V) :
    C(simplicialRealization K,
      simplicialRealization (finiteConeComplex K)) :=
  (finiteConeBaseInclusion K).comp
    (finiteConeBaseRealizationHomeomorph K : C(simplicialRealization K,
      simplicialRealization (finiteConeBaseComplex K)))

end FairDivision.Topology.NerveConnectivity
