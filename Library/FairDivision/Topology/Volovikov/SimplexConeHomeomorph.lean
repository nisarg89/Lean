import FairDivision.Topology.Volovikov.SimplexConeSurjective
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# A finite simplex is the cone on its attaching boundary

The radial cone map is continuous, one-to-one, and onto. Compactness of
the finite simplex boundary makes the cone compact, so this map is a
homeomorphism. The result converts a cone filling from operational
connectivity into a continuous filling on the simplex cell.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped unitInterval

private theorem finiteSimplexBoundary_isClosed (j : ℕ) :
    IsClosed {x : stdSimplex ℝ (Fin (j + 2)) |
      ∃ i : Fin (j + 2), x.1 i = 0} := by
  have hset : {x : stdSimplex ℝ (Fin (j + 2)) |
      ∃ i : Fin (j + 2), x.1 i = 0} =
      ⋃ i : Fin (j + 2), {x | x.1 i = 0} := by
    ext x
    simp
  rw [hset]
  apply isClosed_iUnion_of_finite
  intro i
  exact isClosed_eq
    ((continuous_apply i).comp continuous_subtype_val)
    continuous_const

/-- The radial map from the boundary cone is a homeomorphism onto the
finite simplex. -/
noncomputable def finiteSimplexConeHomeomorph (j : ℕ) :
    TopologicalCone (finiteStandardSimplexBoundary j) ≃ₜ
      stdSimplex ℝ (Fin (j + 2)) := by
  letI : CompactSpace (finiteStandardSimplexBoundary j) :=
    isCompact_iff_compactSpace.mp (finiteSimplexBoundary_isClosed j).isCompact
  have h : IsHomeomorph (finiteSimplexConeMap j) := by
    rw [isHomeomorph_iff_continuous_bijective]
    exact ⟨(finiteSimplexConeMap j).continuous,
      finiteSimplexConeMap_injective j,
      finiteSimplexConeMap_surjective j⟩
  exact IsHomeomorph.homeomorph (finiteSimplexConeMap j) h

/-- A map defined on the attaching boundary extends continuously to the
simplex whenever the target satisfies the operational connectivity
condition in the boundary dimension. -/
theorem exists_finiteSimplex_cellFilling
    {X : Type*} [TopologicalSpace X] {k j : ℕ}
    (hX : NullConnectedSpace k X) (hj : j ≤ k)
    (f : C(finiteStandardSimplexBoundary j, X)) :
    ∃ F : C(stdSimplex ℝ (Fin (j + 2)), X),
      F.comp (⟨Subtype.val, continuous_subtype_val⟩ :
        C(finiteStandardSimplexBoundary j,
          stdSimplex ℝ (Fin (j + 2)))) = f := by
  obtain ⟨F, hF⟩ := exists_simplexBoundary_coneFilling hX hj f
  let e := finiteSimplexConeHomeomorph j
  let E : C(stdSimplex ℝ (Fin (j + 2)), X) :=
    F.comp ⟨e.symm, e.symm.continuous⟩
  refine ⟨E, ?_⟩
  apply ContinuousMap.ext
  intro b
  have hbase : e (coneBase (finiteStandardSimplexBoundary j) b) = b.1 := by
    have h := congrArg (fun g : C(finiteStandardSimplexBoundary j,
        stdSimplex ℝ (Fin (j + 2))) => g b)
      (finiteSimplexConeMap_base j)
    simpa [e, finiteSimplexConeHomeomorph] using h
  have hinv : e.symm b.1 = coneBase (finiteStandardSimplexBoundary j) b := by
    calc
      e.symm b.1 = e.symm (e (coneBase (finiteStandardSimplexBoundary j) b)) := by
        rw [hbase]
      _ = coneBase (finiteStandardSimplexBoundary j) b := e.symm_apply_apply _
  have hfb := congrArg (fun g : C(finiteStandardSimplexBoundary j, X) => g b) hF
  change F (e.symm b.1) = f b
  rw [hinv]
  simpa using hfb

end FairDivision.Topology.Volovikov
