import FairDivision.Topology.NerveConnectivity.FiniteLevelTelescoping

/-!
# Upper coordinate faces and barycentric layers

A face can receive positive inverse weight only if it consists of all
vertices whose original coordinate is at least its internal minimum.
This identifies candidate subdivision vertices with coordinate levels.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe v

/-- Vertices at or above a given coordinate level. -/
noncomputable def upperCoordinateFace {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (t : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => t ≤ x.1 v)

@[simp] theorem mem_upperCoordinateFace_iff {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (t : ℝ) (v : V) :
    v ∈ upperCoordinateFace x t ↔ t ≤ x.1 v := by
  classical
  simp [upperCoordinateFace]

/-- A positive candidate face is exactly the upper set at its smallest
internal coordinate. -/
theorem faceInverseWeight_positive_eq_upper {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (F : Finset V)
    (hF : 0 < faceInverseWeight F x) :
    F = upperCoordinateFace x (faceInsideMin F x) := by
  have hFn : F.Nonempty := by
    by_contra h
    have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst F
    simp at hF
  have hgap := (faceInverseWeight_pos_iff F hFn x).mp hF
  ext v
  constructor
  · intro hv
    exact (mem_upperCoordinateFace_iff x _ v).2 (faceInsideMin_le F x hv)
  · intro hv
    by_contra hvF
    have hvle : x.1 v ≤ faceOutsideMax F x := le_faceOutsideMax F x hvF
    have hminle : faceInsideMin F x ≤ x.1 v :=
      (mem_upperCoordinateFace_iff x _ v).1 hv
    exact (not_lt_of_ge (hminle.trans hvle)) hgap

/-- Positive candidate faces are upper sets at strictly positive levels. -/
theorem faceInverseWeight_positive_level_pos {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (F : Finset V)
    (hF : 0 < faceInverseWeight F x) :
    0 < faceInsideMin F x := by
  have hFn : F.Nonempty := by
    by_contra h
    have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst F
    simp at hF
  exact lt_of_le_of_lt (faceOutsideMax_nonneg F x)
    ((faceInverseWeight_pos_iff F hFn x).mp hF)

/-- The internal minimum of a nonempty face is attained at one of its
vertices. -/
theorem faceInsideMin_attained {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (F : Finset V) (hF : F.Nonempty) :
    ∃ v ∈ F, faceInsideMin F x = x.1 v := by
  classical
  obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image F (fun w => x.1 w) hF
  refine ⟨v, hv, le_antisymm (faceInsideMin_le F x hv) ?_⟩
  rw [faceInsideMin, dif_pos hF]
  apply (Finset.le_inf'_iff hF (fun w => x.1 w)).2
  intro w hw
  exact hmin w hw

/-- Every positive candidate face is indexed by an actual original
coordinate level. -/
theorem faceInverseWeight_positive_level_attained {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (F : Finset V)
    (hF : 0 < faceInverseWeight F x) :
    ∃ v : V, faceInsideMin F x = x.1 v := by
  have hFn : F.Nonempty := by
    by_contra h
    have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst F
    simp at hF
  obtain ⟨v, _, hv⟩ := faceInsideMin_attained x F hFn
  exact ⟨v, hv⟩

/-- The finite set of coordinate values of a probability vector. -/
noncomputable def coordinateLevels {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun v => x.1 v)

@[simp] theorem mem_coordinateLevels_iff {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (t : ℝ) :
    t ∈ coordinateLevels x ↔ ∃ v : V, x.1 v = t := by
  classical
  simp [coordinateLevels]

/-- The upper set of an attained level has that level as its smallest
internal coordinate. -/
theorem faceInsideMin_upper_eq {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (t : ℝ) (hatt : ∃ v : V, x.1 v = t) :
    faceInsideMin (upperCoordinateFace x t) x = t := by
  obtain ⟨v, hv⟩ := hatt
  have hvF : v ∈ upperCoordinateFace x t :=
    (mem_upperCoordinateFace_iff x t v).2 hv.ge
  have hF : (upperCoordinateFace x t).Nonempty := ⟨v, hvF⟩
  change (if h : (upperCoordinateFace x t).Nonempty then
      (upperCoordinateFace x t).inf' h (fun w => x.1 w) else 0) = t
  rw [dif_pos hF]
  apply le_antisymm
  · calc
      (upperCoordinateFace x t).inf' hF (fun w => x.1 w) ≤ x.1 v :=
        Finset.inf'_le (fun w => x.1 w) hvF
      _ = t := hv
  · apply (Finset.le_inf'_iff hF (fun w => x.1 w)).2
    intro w hw
    exact (mem_upperCoordinateFace_iff x t w).1 hw

/-- Coordinates outside an upper face are exactly the attained
coordinate levels below its threshold. -/
theorem outsideImage_upper_eq_levels_filter {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (t : ℝ) :
    (Finset.univ \ upperCoordinateFace x t).image (fun v => x.1 v) =
      (coordinateLevels x).filter (· < t) := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨v, hvG, rfl⟩ := Finset.mem_image.mp hu
    have hvF : v ∉ upperCoordinateFace x t := (Finset.mem_sdiff.mp hvG).2
    have hvlt : x.1 v < t := lt_of_not_ge (by
      intro hge
      exact hvF ((mem_upperCoordinateFace_iff x t v).2 hge))
    exact Finset.mem_filter.mpr
      ⟨(mem_coordinateLevels_iff x (x.1 v)).2 ⟨v, rfl⟩, hvlt⟩
  · intro hu
    obtain ⟨huL, hut⟩ := Finset.mem_filter.mp hu
    obtain ⟨v, hv⟩ := (mem_coordinateLevels_iff x u).1 huL
    apply Finset.mem_image.mpr
    refine ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, ?_⟩, hv⟩
    intro hvF
    have hge := (mem_upperCoordinateFace_iff x t v).1 hvF
    rw [hv] at hge
    exact (not_lt_of_ge hge) hut

/-- The maximum coordinate outside an upper face is the preceding
attained coordinate level. -/
theorem faceOutsideMax_upper_eq_pred {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (t : ℝ) :
    faceOutsideMax (upperCoordinateFace x t) x =
      finiteLevelPred (coordinateLevels x) t := by
  classical
  let G := Finset.univ \ upperCoordinateFace x t
  let T := (coordinateLevels x).filter (· < t)
  have himg : G.image (fun v => x.1 v) = T :=
    outsideImage_upper_eq_levels_filter x t
  by_cases hG : G.Nonempty
  · have hT : T.Nonempty := by
      rw [← himg]
      exact hG.image (fun v => x.1 v)
    change (if h : G.Nonempty then G.sup' h (fun v => x.1 v) else 0) =
      (if h : T.Nonempty then T.max' h else 0)
    rw [dif_pos hG, dif_pos hT]
    have hsup : G.sup' hG (fun v => x.1 v) =
        (G.image (fun v => x.1 v)).max' (hG.image (fun v => x.1 v)) := by
      simpa only [Finset.max'_eq_sup', Function.id_comp, id_eq] using
        (Finset.sup'_comp_eq_image (s := G) (f := fun v => x.1 v)
          hG (id : ℝ → ℝ))
    simpa only [himg] using hsup
  · have hG0 : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hG
    have hT0 : T = ∅ := by rw [← himg, hG0]; rfl
    change (if h : G.Nonempty then G.sup' h (fun v => x.1 v) else 0) =
      (if h : T.Nonempty then T.max' h else 0)
    simp [hG0, hT0]

/-- At an attained level, the candidate face weight is its cardinality
times the gap above the preceding coordinate level. -/
theorem faceInverseWeight_upper_eq_gap {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (t : ℝ) (hatt : ∃ v : V, x.1 v = t) :
    faceInverseWeight (upperCoordinateFace x t) x =
      ((upperCoordinateFace x t).card : ℝ) *
        max 0 (t - finiteLevelPred (coordinateLevels x) t) := by
  simp only [faceInverseWeight, faceInsideMin_upper_eq x t hatt,
    faceOutsideMax_upper_eq_pred x t]

/-- Every positive attained coordinate level gives a positive
subdivision face weight. -/
theorem faceInverseWeight_upper_pos {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (t : ℝ)
    (hatt : ∃ v : V, x.1 v = t) (ht : 0 < t) :
    0 < faceInverseWeight (upperCoordinateFace x t) x := by
  obtain ⟨v, hv⟩ := hatt
  have hvF : v ∈ upperCoordinateFace x t :=
    (mem_upperCoordinateFace_iff x t v).2 hv.ge
  have hc : 0 < ((upperCoordinateFace x t).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨v, hvF⟩
  rw [faceInverseWeight_upper_eq_gap x t ⟨v, hv⟩]
  apply mul_pos hc
  have hgap : 0 < t - finiteLevelPred (coordinateLevels x) t :=
    sub_pos.mpr (finiteLevelPred_lt_of_pos (coordinateLevels x) t ht)
  exact lt_of_lt_of_le hgap (le_max_right 0 _)

/-- Distinct attained coordinate levels give distinct upper faces. -/
theorem upperCoordinateFace_injective_on_levels {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) {s t : ℝ}
    (hs : ∃ v : V, x.1 v = s) (ht : ∃ v : V, x.1 v = t)
    (heq : upperCoordinateFace x s = upperCoordinateFace x t) : s = t := by
  calc
    s = faceInsideMin (upperCoordinateFace x s) x :=
      (faceInsideMin_upper_eq x s hs).symm
    _ = faceInsideMin (upperCoordinateFace x t) x := by rw [heq]
    _ = t := faceInsideMin_upper_eq x t ht

/-- The positive candidate faces are exactly the upper faces at
positive attained coordinate levels. -/
theorem faceInverseSupport_eq_upper_levels {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) :
    faceInverseSupport x =
      ((coordinateLevels x).filter (fun t => 0 < t)).image
        (upperCoordinateFace x) := by
  classical
  ext F
  constructor
  · intro hF
    have hpos := (mem_faceInverseSupport_iff x F).1 hF
    let t := faceInsideMin F x
    obtain ⟨v, hv⟩ := faceInverseWeight_positive_level_attained x F hpos
    have htLevel : t ∈ coordinateLevels x :=
      (mem_coordinateLevels_iff x t).2 ⟨v, hv.symm⟩
    have htPos : 0 < t := faceInverseWeight_positive_level_pos x F hpos
    apply Finset.mem_image.mpr
    exact ⟨t, Finset.mem_filter.mpr ⟨htLevel, htPos⟩,
      (faceInverseWeight_positive_eq_upper x F hpos).symm⟩
  · intro hF
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨htLevel, htPos⟩ := Finset.mem_filter.mp ht
    have hatt := (mem_coordinateLevels_iff x t).1 htLevel
    exact (mem_faceInverseSupport_iff x _).2
      (faceInverseWeight_upper_pos x t hatt htPos)

/-- All attained simplex coordinate levels are nonnegative. -/
theorem coordinateLevels_nonneg {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (t : ℝ) (ht : t ∈ coordinateLevels x) :
    0 ≤ t := by
  obtain ⟨v, hv⟩ := (mem_coordinateLevels_iff x t).1 ht
  rw [← hv]
  exact x.2.1 v

/-- A nonnegative probability vector has no negative coordinate level,
so zero has predecessor zero. -/
theorem finiteLevelPred_coordinate_zero {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) : finiteLevelPred (coordinateLevels x) 0 = 0 := by
  have hEmpty : (coordinateLevels x).filter (· < 0) = ∅ := by
    apply Finset.filter_false_of_mem
    intro t ht
    exact not_lt_of_ge (coordinateLevels_nonneg x t ht)
  simp [finiteLevelPred, hEmpty, finiteLevelTop]

/-- Summing predecessor gaps over positive upper faces containing `v`
recovers the original `v` coordinate. -/
theorem positiveUpperGap_sum_coordinate {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (v : V) :
    ((coordinateLevels x).filter (0 < ·)).sum
      (fun t => if v ∈ upperCoordinateFace x t then
        t - finiteLevelPred (coordinateLevels x) t else 0) = x.1 v := by
  classical
  have hvLevel : x.1 v ∈ coordinateLevels x :=
    (mem_coordinateLevels_iff x (x.1 v)).2 ⟨v, rfl⟩
  have hLevels : ∀ t ∈ coordinateLevels x, 0 ≤ t :=
    coordinateLevels_nonneg x
  calc
    ((coordinateLevels x).filter (0 < ·)).sum
        (fun t => if v ∈ upperCoordinateFace x t then
          t - finiteLevelPred (coordinateLevels x) t else 0) =
      (((coordinateLevels x).filter (0 < ·)).filter (· ≤ x.1 v)).sum
        (fun t => t - finiteLevelPred (coordinateLevels x) t) := by
          simp only [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro t _
          simp only [mem_upperCoordinateFace_iff]
    _ = x.1 v := finitePositiveLevelGap_sum_le_eq
      (coordinateLevels x) (x.1 v) hLevels hvLevel

end FairDivision.Topology.NerveConnectivity
