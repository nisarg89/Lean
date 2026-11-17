import FairDivision.Topology.NerveConnectivity.BarycentricRealizationMap
import Mathlib.Topology.Order.Lattice

/-!
# Candidate inverse coordinates for barycentric subdivision

For a nonempty face `F`, its candidate subdivision weight at `x` is
`|F| * max 0 (min_{v∈F} x_v - max_{v∉F} x_v)`. The outside maximum is
zero when `F` contains every vertex. These coordinates vary continuously.
The simplex and inverse laws are separate obligations.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe v

/-- Minimum coordinate over a face, with zero assigned to the empty face. -/
noncomputable def faceInsideMin {V : Type v} [Fintype V]
    (F : Finset V) (x : stdSimplex ℝ V) : ℝ :=
  if hF : F.Nonempty then F.inf' hF (fun v => x.1 v) else 0

/-- Maximum coordinate outside a face, with zero for an empty complement. -/
noncomputable def faceOutsideMax {V : Type v} [Fintype V]
    (F : Finset V) (x : stdSimplex ℝ V) : ℝ :=
  let G := Finset.univ \ F
  if hG : G.Nonempty then G.sup' hG (fun v => x.1 v) else 0

/-- Continuous candidate for the barycentric subdivision weight of `F`. -/
noncomputable def faceInverseWeight {V : Type v} [Fintype V]
    (F : Finset V) (x : stdSimplex ℝ V) : ℝ :=
  (F.card : ℝ) * max 0 (faceInsideMin F x - faceOutsideMax F x)

/-- A fixed face's minimum coordinate varies continuously. -/
theorem faceInsideMin_continuous {V : Type v} [Fintype V]
    (F : Finset V) : Continuous (faceInsideMin F : stdSimplex ℝ V → ℝ) := by
  classical
  unfold faceInsideMin
  split_ifs with hF
  · apply Continuous.finset_inf'_apply hF
    intro v _
    exact (continuous_apply v).comp continuous_subtype_val
  · exact continuous_const

/-- A fixed face's outside maximum coordinate varies continuously. -/
theorem faceOutsideMax_continuous {V : Type v} [Fintype V]
    (F : Finset V) : Continuous (faceOutsideMax F : stdSimplex ℝ V → ℝ) := by
  classical
  unfold faceOutsideMax
  dsimp
  split_ifs with hG
  · apply Continuous.finset_sup'_apply hG
    intro v _
    exact (continuous_apply v).comp continuous_subtype_val
  · exact continuous_const

/-- The candidate inverse coordinates vary continuously. -/
theorem faceInverseWeight_continuous {V : Type v} [Fintype V]
    (F : Finset V) : Continuous (faceInverseWeight F : stdSimplex ℝ V → ℝ) := by
  unfold faceInverseWeight
  exact continuous_const.mul
    (continuous_const.max
      ((faceInsideMin_continuous F).sub (faceOutsideMax_continuous F)))

/-- Candidate inverse coordinates are nonnegative. -/
theorem faceInverseWeight_nonneg {V : Type v} [Fintype V]
    (F : Finset V) (x : stdSimplex ℝ V) : 0 ≤ faceInverseWeight F x := by
  unfold faceInverseWeight
  positivity

/-- The empty face has zero candidate inverse weight. -/
@[simp] theorem faceInverseWeight_empty {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) : faceInverseWeight (∅ : Finset V) x = 0 := by
  simp [faceInverseWeight]

/-- The minimum on a nonempty face is at most each face coordinate. -/
theorem faceInsideMin_le {V : Type v} [Fintype V]
    (F : Finset V) (x : stdSimplex ℝ V) {v : V} (hv : v ∈ F) :
    faceInsideMin F x ≤ x.1 v := by
  have hF : F.Nonempty := ⟨v, hv⟩
  simp only [faceInsideMin, dif_pos hF]
  exact Finset.inf'_le (fun w => x.1 w) hv

/-- Every coordinate outside a face is at most its outside maximum. -/
theorem le_faceOutsideMax {V : Type v} [Fintype V]
    (F : Finset V) (x : stdSimplex ℝ V) {v : V} (hv : v ∉ F) :
    x.1 v ≤ faceOutsideMax F x := by
  let G := Finset.univ \ F
  have hvG : v ∈ G := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩
  have hG : G.Nonempty := ⟨v, hvG⟩
  change x.1 v ≤ (if h : G.Nonempty then G.sup' h (fun w => x.1 w) else 0)
  rw [dif_pos hG]
  exact Finset.le_sup' (fun w => x.1 w) hvG

/-- A nonempty face has positive candidate weight precisely when its
smallest internal coordinate exceeds its largest external coordinate. -/
theorem faceInverseWeight_pos_iff {V : Type v} [Fintype V]
    (F : Finset V) (hF : F.Nonempty) (x : stdSimplex ℝ V) :
    0 < faceInverseWeight F x ↔
      faceOutsideMax F x < faceInsideMin F x := by
  have hc : 0 < (F.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hF
  simp only [faceInverseWeight, mul_pos_iff_of_pos_left hc,
    lt_max_iff, lt_irrefl, false_or, sub_pos]

/-- Distinct positive candidate faces are nested: their internal
coordinates dominate every coordinate outside them. -/
theorem faceInverseWeight_positive_comparable {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (F G : Finset V)
    (hF : 0 < faceInverseWeight F x)
    (hG : 0 < faceInverseWeight G x) : F ⊆ G ∨ G ⊆ F := by
  have hFn : F.Nonempty := by
    by_contra h
    have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst F
    simp at hF
  have hGn : G.Nonempty := by
    by_contra h
    have he : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst G
    simp at hG
  have hFg := (faceInverseWeight_pos_iff F hFn x).mp hF
  have hGg := (faceInverseWeight_pos_iff G hGn x).mp hG
  by_contra hcomp
  push_neg at hcomp
  obtain ⟨v, hvF, hvG⟩ := Finset.not_subset.mp hcomp.1
  obtain ⟨w, hwG, hwF⟩ := Finset.not_subset.mp hcomp.2
  have hvw : x.1 w < x.1 v :=
    lt_of_le_of_lt (le_faceOutsideMax F x hwF)
      (lt_of_lt_of_le hFg (faceInsideMin_le F x hvF))
  have hwv : x.1 v < x.1 w :=
    lt_of_le_of_lt (le_faceOutsideMax G x hvG)
      (lt_of_lt_of_le hGg (faceInsideMin_le G x hwG))
  exact (lt_asymm hvw hwv).elim

/-- Outside maxima are nonnegative because simplex coordinates are. -/
theorem faceOutsideMax_nonneg {V : Type v} [Fintype V]
    (F : Finset V) (x : stdSimplex ℝ V) : 0 ≤ faceOutsideMax F x := by
  classical
  let G := Finset.univ \ F
  by_cases hG : G.Nonempty
  · obtain ⟨v, hv⟩ := hG
    have hGn : G.Nonempty := ⟨v, hv⟩
    have hvle : x.1 v ≤ G.sup' hGn (fun w => x.1 w) :=
      Finset.le_sup' (fun w => x.1 w) hv
    have hcoord : 0 ≤ x.1 v := x.2.1 v
    exact le_trans hcoord (by simpa [faceOutsideMax, G, hGn] using hvle)
  · simp [faceOutsideMax, G, hG]

/-- Every vertex of a face of positive candidate weight has positive
original coordinate. -/
theorem faceInverseWeight_pos_mem_support {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (F : Finset V)
    (hF : 0 < faceInverseWeight F x) {v : V} (hv : v ∈ F) :
    v ∈ FairDivision.Topology.finiteSimplexSupport x := by
  have hFn : F.Nonempty := ⟨v, hv⟩
  have hgap := (faceInverseWeight_pos_iff F hFn x).mp hF
  have hpos : 0 < x.1 v :=
    lt_of_le_of_lt (faceOutsideMax_nonneg F x)
      (lt_of_lt_of_le hgap (faceInsideMin_le F x hv))
  exact (FairDivision.Topology.mem_finiteSimplexSupport_iff x v).2 hpos

/-- Every positive candidate face belongs to the original complex. -/
theorem faceInverseWeight_pos_mem_complex {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V)
    (x : simplicialRealization K) (F : Finset V)
    (hF : 0 < faceInverseWeight F x.1) : F ∈ K := by
  have hFn : F.Nonempty := by
    by_contra h
    have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst F
    simp at hF
  apply (K.isRelLowerSet_faces x.2).2
  · intro v hv
    exact faceInverseWeight_pos_mem_support x.1 F hF hv
  · exact hFn

/-- The set of faces with positive inverse weight is linearly ordered
by inclusion. -/
theorem faceInverseWeight_positive_chain {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) :
    IsChain (· ⊆ ·)
      {F : Finset V | 0 < faceInverseWeight F x} := by
  intro F hF G hG _
  exact faceInverseWeight_positive_comparable x F G hF hG

/-- All coordinates outside the positive support vanish. -/
theorem faceOutsideMax_support_eq_zero {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) :
    faceOutsideMax (FairDivision.Topology.finiteSimplexSupport x) x = 0 := by
  classical
  let F := FairDivision.Topology.finiteSimplexSupport x
  let G := Finset.univ \ F
  by_cases hG : G.Nonempty
  · have hle : G.sup' hG (fun v => x.1 v) ≤ 0 := by
      apply (Finset.sup'_le_iff hG (fun v => x.1 v)).2
      intro v hv
      have hvF : v ∉ F := (Finset.mem_sdiff.mp hv).2
      have hnot : ¬ 0 < x.1 v := by
        intro hpos
        exact hvF ((FairDivision.Topology.mem_finiteSimplexSupport_iff x v).2 hpos)
      exact le_of_not_gt hnot
    have hnonneg : 0 ≤ G.sup' hG (fun v => x.1 v) := by
      obtain ⟨v, hv⟩ := hG
      exact (x.2.1 v).trans (Finset.le_sup' (fun w => x.1 w) hv)
    change (if h : G.Nonempty then G.sup' h (fun v => x.1 v) else 0) = 0
    rw [dif_pos hG]
    exact le_antisymm hle hnonneg
  · change (if h : G.Nonempty then G.sup' h (fun v => x.1 v) else 0) = 0
    simp [hG]

/-- The full positive support receives positive candidate weight. -/
theorem faceInverseWeight_support_pos {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) :
    0 < faceInverseWeight (FairDivision.Topology.finiteSimplexSupport x) x := by
  let F := FairDivision.Topology.finiteSimplexSupport x
  have hF : F.Nonempty := FairDivision.Topology.finiteSimplexSupport_nonempty x
  apply (faceInverseWeight_pos_iff F hF x).2
  rw [faceOutsideMax_support_eq_zero]
  change 0 < (if h : F.Nonempty then F.inf' h (fun v => x.1 v) else 0)
  rw [dif_pos hF]
  apply (Finset.lt_inf'_iff hF).2
  intro v hv
  exact (FairDivision.Topology.mem_finiteSimplexSupport_iff x v).1 hv

/-- Faces receiving positive candidate inverse weight. -/
noncomputable def faceInverseSupport {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun F => 0 < faceInverseWeight F x)

@[simp] theorem mem_faceInverseSupport_iff {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (F : Finset V) :
    F ∈ faceInverseSupport x ↔ 0 < faceInverseWeight F x := by
  classical
  simp [faceInverseSupport]

/-- The inverse support is nonempty, since it contains the full original
positive support. -/
theorem faceInverseSupport_nonempty {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) : (faceInverseSupport x).Nonempty := by
  exact ⟨FairDivision.Topology.finiteSimplexSupport x,
    (mem_faceInverseSupport_iff x _).2 (faceInverseWeight_support_pos x)⟩

/-- The candidate inverse support is a chain of original faces. -/
theorem faceInverseSupport_chain {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) :
    IsChain (· ⊆ ·) ((faceInverseSupport x : Finset (Finset V)) :
      Set (Finset V)) := by
  intro F hF G hG _
  exact faceInverseWeight_positive_comparable x F G
    ((mem_faceInverseSupport_iff x F).1 hF)
    ((mem_faceInverseSupport_iff x G).1 hG)

/-- For a point in `|K|`, each face in the inverse support belongs to `K`. -/
theorem faceInverseSupport_mem_complex {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V)
    (x : simplicialRealization K) (F : Finset V)
    (hF : F ∈ faceInverseSupport x.1) : F ∈ K :=
  faceInverseWeight_pos_mem_complex K x F
    ((mem_faceInverseSupport_iff x.1 F).1 hF)

end FairDivision.Topology.NerveConnectivity
