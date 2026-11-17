import FairDivision.Topology.NerveConnectivity.FiniteCellAttachment
import FairDivision.Topology.NerveConnectivity.RealizationEquiv
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# A finite face as a standard simplex

A full face in a finite probability-simplex realization is canonically
homeomorphic to the standard simplex indexed by its own vertices. This is the
coordinate bridge for transferring simplex cell fillings to arbitrary finite
subcomplexes.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe v

/-- A finite set of vertices is a finite type in its own right. -/
abbrev FaceVertex {V : Type v} (F : Finset V) := {v : V // v ∈ F}

/-- An arbitrary ambient vertex is sent to itself when it belongs to `F`,
and to a chosen vertex of `F` otherwise. -/
noncomputable def faceVertexRetract {V : Type v} (F : Finset V)
    (hF : F.Nonempty) (v : V) : FaceVertex F := by
  classical
  exact if h : v ∈ F then ⟨v, h⟩ else ⟨hF.choose, hF.choose_spec⟩

@[simp] theorem faceVertexRetract_val {V : Type v} (F : Finset V)
    (hF : F.Nonempty) {v : V} (hv : v ∈ F) :
    (faceVertexRetract F hF v).1 = v := by
  simp [faceVertexRetract, hv]

/-- All points of a standard simplex lie in the realization of the top
complex. -/
theorem simplicialRealization_top_eq_univ {V : Type v} [Fintype V] :
    simplicialRealization (⊤ : PreAbstractSimplicialComplex V) = Set.univ := by
  ext w
  constructor
  · intro _
    trivial
  · intro _
    exact FairDivision.Topology.finiteSimplexSupport_nonempty w

/-- The realization of a full nonempty face is the standard simplex on its
own vertices. -/
noncomputable def fullFaceRealizationHomeomorph {V : Type v}
    [Fintype V] (F : Finset V) (hF : F.Nonempty) :
    simplicialRealization (fullFaceComplex F) ≃ₜ
      stdSimplex ℝ (FaceVertex F) := by
  classical
  let g : V → FaceVertex F := faceVertexRetract F hF
  let e := realizationHomeomorphOfVertexMaps
    (⊤ : PreAbstractSimplicialComplex (FaceVertex F))
    (fullFaceComplex F) (fun v : FaceVertex F => v.1) g
    (by
      intro S hS
      have hSne : S.Nonempty := hS
      refine ⟨hSne.image _, ?_⟩
      intro v hv
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
      exact u.2)
    (by
      intro T hT
      exact hT.1.image g)
    (by
      intro S _ v _
      apply Subtype.ext
      simp [g])
    (by
      intro T hT v hv
      exact faceVertexRetract_val F hF (hT.2 hv))
  let t : simplicialRealization
      (⊤ : PreAbstractSimplicialComplex (FaceVertex F)) ≃ₜ
      stdSimplex ℝ (FaceVertex F) :=
    (Homeomorph.setCongr simplicialRealization_top_eq_univ).trans
      (Homeomorph.Set.univ _)
  exact e.symm.trans t

/-- The forward coordinate map collects ambient weights at their face
vertices. -/
theorem fullFaceRealizationHomeomorph_apply {V : Type v} [Fintype V]
    (F : Finset V) (hF : F.Nonempty)
    (w : simplicialRealization (fullFaceComplex F)) :
    fullFaceRealizationHomeomorph F hF w =
      stdSimplex.map (faceVertexRetract F hF) w.1 := rfl

/-- The inverse coordinate map extends a face probability vector by zero. -/
theorem fullFaceRealizationHomeomorph_symm_apply {V : Type v} [Fintype V]
    (F : Finset V) (hF : F.Nonempty)
    (w : stdSimplex ℝ (FaceVertex F)) :
    ((fullFaceRealizationHomeomorph F hF).symm w).1 =
      stdSimplex.map (fun v : FaceVertex F => v.1) w := rfl

end FairDivision.Topology.NerveConnectivity
