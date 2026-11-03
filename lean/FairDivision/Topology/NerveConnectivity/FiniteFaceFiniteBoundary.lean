import FairDivision.Topology.NerveConnectivity.FiniteFaceBoundary
import FairDivision.Topology.FiniteSimplexCubeBoundary
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite-face boundary in the standard dimension index

A finite vertex set with `j + 2` elements is reindexed by `Fin (j + 2)`.
The coordinate relabeling carries zero-coordinate boundaries to one another,
which connects arbitrary face attachments to the compiled simplex filling
result.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Relabel probability-simplex coordinates along an equivalence. -/
noncomputable def simplexIndexHomeomorph {A : Type u} {B : Type v}
    [Fintype A] [Fintype B] (e : A ≃ B) :
    stdSimplex ℝ A ≃ₜ stdSimplex ℝ B where
  toFun w := stdSimplex.map e w
  invFun w := stdSimplex.map e.symm w
  left_inv w := by
    calc
      stdSimplex.map e.symm (stdSimplex.map e w) =
          stdSimplex.map (e.symm ∘ e) w :=
        stdSimplex.map_comp_apply e e.symm w
      _ = stdSimplex.map id w := by
        congr 1
        funext a
        exact e.symm_apply_apply a
      _ = w := stdSimplex.map_id_apply w
  right_inv w := by
    calc
      stdSimplex.map e (stdSimplex.map e.symm w) =
          stdSimplex.map (e ∘ e.symm) w :=
        stdSimplex.map_comp_apply e.symm e w
      _ = stdSimplex.map id w := by
        congr 1
        funext b
        exact e.apply_symm_apply b
      _ = w := stdSimplex.map_id_apply w
  continuous_toFun := stdSimplex.continuous_map e
  continuous_invFun := stdSimplex.continuous_map e.symm

/-- A coordinate is unchanged by relabeling when read at its new index. -/
theorem simplexIndexHomeomorph_weight {A : Type u} {B : Type v}
    [Fintype A] [Fintype B] (e : A ≃ B)
    (w : stdSimplex ℝ A) (a : A) :
    (simplexIndexHomeomorph e w).1 (e a) = w.1 a := by
  classical
  change (FunOnFinite.linearMap ℝ ℝ e w.1) (e a) = _
  rw [FunOnFinite.linearMap_apply_apply]
  have hfilter : Finset.univ.filter (fun x : A => e x = e a) = {a} := by
    ext x
    simp [e.injective.eq_iff]
  rw [hfilter]
  simp

/-- Coordinate relabeling preserves the condition of having a zero weight. -/
theorem simplexIndexHomeomorph_boundary_iff {A : Type u} {B : Type v}
    [Fintype A] [Fintype B] (e : A ≃ B)
    (w : stdSimplex ℝ A) :
    (∃ a : A, w.1 a = 0) ↔
      (∃ b : B, (simplexIndexHomeomorph e w).1 b = 0) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨e a, (simplexIndexHomeomorph_weight e w a).trans ha⟩
  · rintro ⟨b, hb⟩
    refine ⟨e.symm b, ?_⟩
    have h := simplexIndexHomeomorph_weight e w (e.symm b)
    rw [e.apply_symm_apply] at h
    exact h.symm.trans hb

/-- The `Fin` indexing of the vertices of a face of known cardinality. -/
noncomputable def faceVertexFinEquiv {V : Type v} (F : Finset V)
    (j : ℕ) (hcard : F.card = j + 2) :
    FaceVertex F ≃ Fin (j + 2) := by
  classical
  exact Fintype.equivFinOfCardEq
    ((Fintype.card_coe F).trans hcard)

/-- The arbitrary finite-face boundary has the standard finite dimension
index used by the simplex filling theorem. -/
noncomputable def finiteFaceBoundaryFinHomeomorph {V : Type v}
    (F : Finset V) (j : ℕ) (hcard : F.card = j + 2) :
    finiteFaceStandardSimplexBoundary F ≃ₜ
      FairDivision.Topology.finiteStandardSimplexBoundary j := by
  let e := faceVertexFinEquiv F j hcard
  exact (simplexIndexHomeomorph e).subtype
    (simplexIndexHomeomorph_boundary_iff e)

end FairDivision.Topology.NerveConnectivity
