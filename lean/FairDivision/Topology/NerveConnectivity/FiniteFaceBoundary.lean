import FairDivision.Topology.NerveConnectivity.FiniteFaceGeometry

/-!
# The boundary of a finite face as a standard-simplex boundary

The full-face homeomorphism preserves every coordinate at a face vertex.
Consequently, its restriction identifies the proper-face boundary with the
zero-coordinate boundary of the standard simplex on those vertices.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe v

/-- The full-face homeomorphism preserves weights at face vertices. -/
theorem fullFaceRealizationHomeomorph_weight {V : Type v}
    [Fintype V] (F : Finset V) (hF : F.Nonempty)
    (w : simplicialRealization (fullFaceComplex F))
    (v : FaceVertex F) :
    (fullFaceRealizationHomeomorph F hF w).1 v = w.1.1 v.1 := by
  classical
  rw [fullFaceRealizationHomeomorph_apply]
  change (FunOnFinite.linearMap ℝ ℝ (faceVertexRetract F hF) w.1.1) v = _
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_single v.1
  · intro u hu hne
    have hgu : faceVertexRetract F hF u = v :=
      (Finset.mem_filter.mp hu).2
    have huNotF : u ∉ F := by
      intro huF
      have hval := congrArg Subtype.val hgu
      rw [faceVertexRetract_val F hF huF] at hval
      exact hne hval
    have huNotSupp : u ∉ FairDivision.Topology.finiteSimplexSupport w.1 :=
      fun hu => huNotF (w.2.2 hu)
    have hnotpos : ¬ 0 < w.1.1 u := by
      intro hp
      exact huNotSupp ((FairDivision.Topology.mem_finiteSimplexSupport_iff w.1 u).2 hp)
    exact le_antisymm (le_of_not_gt hnotpos) (w.1.2.1 u)
  · intro hnot
    exfalso
    apply hnot
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact faceVertexRetract_val F hF v.2

/-- The boundary of a standard simplex indexed by the vertices of `F`. -/
abbrev finiteFaceStandardSimplexBoundary {V : Type v}
    (F : Finset V) :=
  {w : stdSimplex ℝ (FaceVertex F) // ∃ v : FaceVertex F, w.1 v = 0}

/-- The realized boundary, viewed as a subtype of the realized full face. -/
noncomputable def boundaryFaceInFullHomeomorph {V : Type v}
    [Fintype V] (F : Finset V) :
    simplicialRealization (boundaryFaceComplex F) ≃ₜ
      {w : simplicialRealization (fullFaceComplex F) //
        w.1 ∈ simplicialRealization (boundaryFaceComplex F)} where
  toFun w := ⟨⟨w.1,
    (simplicialRealization_mono (boundaryFaceComplex_le_fullFaceComplex F)) w.2⟩,
    w.2⟩
  invFun w := ⟨w.1.1, w.2⟩
  left_inv w := by
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

/-- The realized boundary of an arbitrary nonempty finite face is the
zero-coordinate boundary of the corresponding standard simplex. -/
noncomputable def boundaryFaceRealizationHomeomorph {V : Type v}
    [Fintype V] (F : Finset V) (hF : F.Nonempty) :
    simplicialRealization (boundaryFaceComplex F) ≃ₜ
      finiteFaceStandardSimplexBoundary F := by
  let e := fullFaceRealizationHomeomorph F hF
  have hiff (w : simplicialRealization (fullFaceComplex F)) :
      w.1 ∈ simplicialRealization (boundaryFaceComplex F) ↔
        ∃ v : FaceVertex F, (e w).1 v = 0 := by
    rw [mem_boundaryFaceRealization_iff]
    constructor
    · rintro ⟨_, v, hvF, hvzero⟩
      exact ⟨⟨v, hvF⟩, by
        rw [show e w = fullFaceRealizationHomeomorph F hF w from rfl,
          fullFaceRealizationHomeomorph_weight]
        exact hvzero⟩
    · rintro ⟨v, hvzero⟩
      refine ⟨w.2, v.1, v.2, ?_⟩
      rw [show e w = fullFaceRealizationHomeomorph F hF w from rfl,
        fullFaceRealizationHomeomorph_weight] at hvzero
      exact hvzero
  exact (boundaryFaceInFullHomeomorph F).trans (e.subtype hiff)

end FairDivision.Topology.NerveConnectivity
