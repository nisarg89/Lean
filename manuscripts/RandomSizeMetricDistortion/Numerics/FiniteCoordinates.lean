import RandomSizeMetricDistortion.Statements
noncomputable section
open Set
namespace MetricDistortion.NumericalFiniteCoordinates

private theorem unit_parameter (lo hi x : ℝ) (hlo : lo ≤ hi) (hx : x ∈ Icc lo hi) :
    ∃ t ∈ Icc (0 : ℝ) 1, x = lo+(hi-lo)*t := by
  have hs : x ∈ segment ℝ lo hi := by rwa [segment_eq_Icc hlo]
  rw [segment_eq_image' ℝ lo hi] at hs
  obtain ⟨t,ht,he⟩ := hs
  exact ⟨t,ht,by simpa only [smul_eq_mul,mul_comm] using he.symm⟩

def mix (a b t : ℝ) : ℝ := a+(b-a)*t
def finiteBox (lo hi : ℚ) : Box := ![⟨lo,hi⟩,⟨0,1⟩,⟨0,1⟩,⟨0,1⟩]
def coordinates (p u v w : ℝ) : Fin 4 → ℝ := ![p,u,v,w]
private theorem in_finiteBox (lo hi : ℚ) (p u v w : ℝ)
    (hp : p ∈ Icc (lo : ℝ) hi) (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1) :
    inBox (finiteBox lo hi) (coordinates p u v w) := by
  intro i
  fin_cases i
  · exact hp
  · simpa [coordinates,finiteBox] using hu
  · simpa [coordinates,finiteBox] using hv
  · simpa [coordinates,finiteBox] using hw

theorem knot_left (lo hi p t : ℝ) (hlo : lo < p) (hhi : p ≤ hi)
    (hk : hi ≤ t ∨ t ≤ lo) (hp : p ≤ t) : hi ≤ t := by
  rcases hk with h | h
  · exact h
  · linarith

theorem knot_right (lo hi p t : ℝ) (hlo : lo < p) (hhi : p ≤ hi)
    (hk : hi ≤ t ∨ t ≤ lo) (hp : t < p) : t ≤ lo := by
  rcases hk with h | h
  · linarith
  · exact h

private theorem branch_min (lo hi p t : ℝ) (hlo : lo < p) (hhi : p ≤ hi)
    (hk : hi ≤ t ∨ t ≤ lo) : (if hi ≤ t then p else t) = min p t := by
  by_cases hh : hi ≤ t
  · rw [if_pos hh,min_eq_left (hhi.trans hh)]
  · have ht : t ≤ lo := hk.resolve_left hh
    rw [if_neg hh,min_eq_right (ht.trans hlo.le)]

private theorem branch_max (lo hi p t : ℝ) (hlo : lo < p) (hhi : p ≤ hi)
    (hk : hi ≤ t ∨ t ≤ lo) : (if hi ≤ t then t else p) = max p t := by
  by_cases hh : hi ≤ t
  · rw [if_pos hh,max_eq_right (hhi.trans hh)]
  · have ht : t ≤ lo := hk.resolve_left hh
    rw [if_neg hh,max_eq_left (ht.trans hlo.le)]

def lowFirstBottomA (hi : ℚ) (r0 : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  (if (hi : ℝ) ≤ r0 then x 0 else r0)*x 1
def lowFirstBottomR (r0 r1 : ℝ) (x : Fin 4 → ℝ) : ℝ := mix r0 r1 (x 2)
def lowFirstTopA (hi : ℚ) (r0 r1 : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  mix r0 (if (hi : ℝ) ≤ r1 then x 0 else r1) (x 1)
def lowFirstTopR (hi : ℚ) (r0 r1 : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  mix (lowFirstTopA hi r0 r1 x) r1 (x 2)
def lowInternalA (x : Fin 4 → ℝ) : ℝ := x 0*x 1
def lowInternalR (hi : ℚ) (r0 r1 : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  mix (if (hi : ℝ) ≤ r0 then r0 else x 0) r1 (x 3)
def lowInternalCap (hi : ℚ) (r0 r1 : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  mix (x 0) (lowInternalR hi r0 r1 x) (x 2)
def highFirstBottomA (hi : ℚ) (b : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  (if (hi : ℝ) ≤ b then x 0 else b)*x 1
def highFirstBottomR (b : ℝ) (x : Fin 4 → ℝ) : ℝ := mix b 1 (x 2)
def highFirstTopA (b : ℝ) (x : Fin 4 → ℝ) : ℝ := mix b (x 0) (x 1)
def highFirstTopR (b : ℝ) (x : Fin 4 → ℝ) : ℝ := mix (highFirstTopA b x) 1 (x 2)
def highInternalBottomA (x : Fin 4 → ℝ) : ℝ := x 0*x 1
def highInternalBottomCap (b : ℝ) (x : Fin 4 → ℝ) : ℝ := mix (x 0) b (x 2)
def highInternalBottomR (b : ℝ) (x : Fin 4 → ℝ) : ℝ := mix b 1 (x 3)
def highInternalTopA (b : ℝ) (x : Fin 4 → ℝ) : ℝ := mix b (x 0) (x 1)
def highInternalTopCap (x : Fin 4 → ℝ) : ℝ := mix (x 0) 1 (x 2)
def highInternalTopR (x : Fin 4 → ℝ) : ℝ := mix (highInternalTopCap x) 1 (x 3)

theorem low_first_bottom_coordinates (lo hi : ℚ) (r0 r1 p a r : ℝ)
    (hp : (lo : ℝ) < p ∧ p ≤ (hi : ℝ))
    (hk0 : (hi : ℝ) ≤ r0 ∨ r0 ≤ (lo : ℝ))
    (hr : r ∈ Icc r0 r1) (ha : 0 ≤ a) (hap : a ≤ min p r) (ha0 : a ≤ r0) :
    ∃ x, inBox (finiteBox lo hi) x ∧ x 0 = p ∧
      lowFirstBottomA hi r0 x = a ∧ lowFirstBottomR r0 r1 x = r := by
  have hacap : a ≤ min p r0 := le_min (hap.trans (min_le_left _ _)) ha0
  obtain ⟨u,hu,haeq⟩ := unit_parameter 0 (min p r0) a (ha.trans hacap) ⟨ha,hacap⟩
  obtain ⟨v,hv,hreq⟩ := unit_parameter r0 r1 r (hr.1.trans hr.2) hr
  let x := coordinates p u v 0
  refine ⟨x,in_finiteBox lo hi p u v 0 ⟨hp.1.le,hp.2⟩ hu hv (by norm_num),rfl,?_,?_⟩
  · change (if (hi : ℝ) ≤ r0 then p else r0)*u = a
    rw [branch_min (lo : ℝ) hi p r0 hp.1 hp.2 hk0]
    simpa using haeq.symm
  · exact hreq.symm

theorem low_first_top_coordinates (lo hi : ℚ) (r0 r1 p a r : ℝ)
    (hp : (lo : ℝ) < p ∧ p ≤ (hi : ℝ))
    (hk0 : (hi : ℝ) ≤ r0 ∨ r0 ≤ (lo : ℝ))
    (hk1 : (hi : ℝ) ≤ r1 ∨ r1 ≤ (lo : ℝ))
    (hr : r ∈ Icc r0 r1) (hap : a ≤ min p r) (ha0 : r0 < a) :
    r0 ≤ (lo : ℝ) ∧ ∃ x, inBox (finiteBox lo hi) x ∧ x 0 = p ∧
      lowFirstTopA hi r0 r1 x = a ∧ lowFirstTopR hi r0 r1 x = r := by
  have hpa : a ≤ p := hap.trans (min_le_left _ _)
  have har : a ≤ r := hap.trans (min_le_right _ _)
  have hcap : a ≤ min p r1 := le_min hpa (har.trans hr.2)
  have hactive : r0 ≤ (lo : ℝ) := knot_right lo hi p r0 hp.1 hp.2 hk0 (ha0.trans_le hpa)
  obtain ⟨u,hu,haeq⟩ := unit_parameter r0 (min p r1) a (ha0.le.trans hcap) ⟨ha0.le,hcap⟩
  obtain ⟨v,hv,hreq⟩ := unit_parameter a r1 r (har.trans hr.2) ⟨har,hr.2⟩
  let x := coordinates p u v 0
  have hA : lowFirstTopA hi r0 r1 x = a := by
    change mix r0 (if (hi : ℝ) ≤ r1 then p else r1) u = a
    rw [branch_min (lo : ℝ) hi p r1 hp.1 hp.2 hk1]
    exact haeq.symm
  refine ⟨hactive,x,in_finiteBox lo hi p u v 0 ⟨hp.1.le,hp.2⟩ hu hv (by norm_num),rfl,hA,?_⟩
  change mix (lowFirstTopA hi r0 r1 x) r1 v = r
  rw [hA]
  exact hreq.symm

theorem low_internal_coordinates (lo hi : ℚ) (r0 r1 p a cap r : ℝ)
    (hp : (lo : ℝ) < p ∧ p ≤ (hi : ℝ))
    (hk0 : (hi : ℝ) ≤ r0 ∨ r0 ≤ (lo : ℝ))
    (hk1 : (hi : ℝ) ≤ r1 ∨ r1 ≤ (lo : ℝ))
    (hr : r ∈ Icc r0 r1) (ha : 0 ≤ a) (hap : a ≤ p) (hpA : p ≤ cap) (hAr : cap ≤ r) :
    (hi : ℝ) ≤ r1 ∧ ∃ x, inBox (finiteBox lo hi) x ∧ x 0 = p ∧
      lowInternalA x = a ∧ lowInternalCap hi r0 r1 x = cap ∧ lowInternalR hi r0 r1 x = r := by
  have hpr : p ≤ r := hpA.trans hAr
  have hstart : max p r0 ≤ r := max_le hpr hr.1
  have hactive : (hi : ℝ) ≤ r1 := knot_left lo hi p r1 hp.1 hp.2 hk1 (hpr.trans hr.2)
  obtain ⟨u,hu,haeq⟩ := unit_parameter 0 p a (ha.trans hap) ⟨ha,hap⟩
  obtain ⟨v,hv,hAeq⟩ := unit_parameter p r cap hpr ⟨hpA,hAr⟩
  obtain ⟨w,hw,hreq⟩ := unit_parameter (max p r0) r1 r (hstart.trans hr.2) ⟨hstart,hr.2⟩
  let x := coordinates p u v w
  have hR : lowInternalR hi r0 r1 x = r := by
    change mix (if (hi : ℝ) ≤ r0 then r0 else p) r1 w = r
    rw [branch_max (lo : ℝ) hi p r0 hp.1 hp.2 hk0]
    exact hreq.symm
  refine ⟨hactive,x,in_finiteBox lo hi p u v w ⟨hp.1.le,hp.2⟩ hu hv hw,rfl,?_,?_,hR⟩
  · simpa [lowInternalA,x,coordinates] using haeq.symm
  · change mix p (lowInternalR hi r0 r1 x) v = cap
    rw [hR]
    exact hAeq.symm

theorem high_first_bottom_coordinates (lo hi : ℚ) (b p a r : ℝ)
    (hp : (lo : ℝ) < p ∧ p ≤ (hi : ℝ))
    (hkb : (hi : ℝ) ≤ b ∨ b ≤ (lo : ℝ))
    (hr : r ∈ Icc b 1) (ha : 0 ≤ a) (hap : a ≤ min p r) (hab : a ≤ b) :
    ∃ x, inBox (finiteBox lo hi) x ∧ x 0 = p ∧
      highFirstBottomA hi b x = a ∧ highFirstBottomR b x = r := by
  have hacap : a ≤ min p b := le_min (hap.trans (min_le_left _ _)) hab
  obtain ⟨u,hu,haeq⟩ := unit_parameter 0 (min p b) a (ha.trans hacap) ⟨ha,hacap⟩
  obtain ⟨v,hv,hreq⟩ := unit_parameter b 1 r (hr.1.trans hr.2) hr
  let x := coordinates p u v 0
  refine ⟨x,in_finiteBox lo hi p u v 0 ⟨hp.1.le,hp.2⟩ hu hv (by norm_num),rfl,?_,?_⟩
  · change (if (hi : ℝ) ≤ b then p else b)*u = a
    rw [branch_min (lo : ℝ) hi p b hp.1 hp.2 hkb]
    simpa using haeq.symm
  · exact hreq.symm

theorem high_first_top_coordinates (lo hi : ℚ) (b p a r : ℝ)
    (hp : (lo : ℝ) < p ∧ p ≤ (hi : ℝ))
    (hkb : (hi : ℝ) ≤ b ∨ b ≤ (lo : ℝ))
    (hr : r ≤ 1) (hap : a ≤ min p r) (hba : b < a) :
    b ≤ (lo : ℝ) ∧ ∃ x, inBox (finiteBox lo hi) x ∧ x 0 = p ∧
      highFirstTopA b x = a ∧ highFirstTopR b x = r := by
  have hpa : a ≤ p := hap.trans (min_le_left _ _)
  have har : a ≤ r := hap.trans (min_le_right _ _)
  have hactive := knot_right lo hi p b hp.1 hp.2 hkb (hba.trans_le hpa)
  obtain ⟨u,hu,haeq⟩ := unit_parameter b p a (hba.le.trans hpa) ⟨hba.le,hpa⟩
  obtain ⟨v,hv,hreq⟩ := unit_parameter a 1 r (har.trans hr) ⟨har,hr⟩
  let x := coordinates p u v 0
  have hA : highFirstTopA b x = a := haeq.symm
  refine ⟨hactive,x,in_finiteBox lo hi p u v 0 ⟨hp.1.le,hp.2⟩ hu hv (by norm_num),rfl,hA,?_⟩
  change mix (highFirstTopA b x) 1 v = r
  rw [hA]
  exact hreq.symm

theorem high_internal_bottom_coordinates (lo hi : ℚ) (b p a cap r : ℝ)
    (hp : (lo : ℝ) < p ∧ p ≤ (hi : ℝ))
    (hkb : (hi : ℝ) ≤ b ∨ b ≤ (lo : ℝ))
    (hr : r ∈ Icc b 1) (ha : 0 ≤ a) (hap : a ≤ p)
    (hpA : p ≤ cap) (hAb : cap ≤ b) :
    (hi : ℝ) ≤ b ∧ ∃ x, inBox (finiteBox lo hi) x ∧ x 0 = p ∧
      highInternalBottomA x = a ∧ highInternalBottomCap b x = cap ∧ highInternalBottomR b x = r := by
  have hpb : p ≤ b := hpA.trans hAb
  have hactive := knot_left lo hi p b hp.1 hp.2 hkb hpb
  obtain ⟨u,hu,haeq⟩ := unit_parameter 0 p a (ha.trans hap) ⟨ha,hap⟩
  obtain ⟨v,hv,hAeq⟩ := unit_parameter p b cap hpb ⟨hpA,hAb⟩
  obtain ⟨w,hw,hreq⟩ := unit_parameter b 1 r (hr.1.trans hr.2) hr
  let x := coordinates p u v w
  refine ⟨hactive,x,in_finiteBox lo hi p u v w ⟨hp.1.le,hp.2⟩ hu hv hw,rfl,?_,?_,?_⟩
  · simpa [highInternalBottomA,x,coordinates] using haeq.symm
  · exact hAeq.symm
  · exact hreq.symm

theorem high_internal_top_coordinates (lo hi : ℚ) (b p a cap r : ℝ)
    (hp : (lo : ℝ) < p ∧ p ≤ (hi : ℝ))
    (hkb : (hi : ℝ) ≤ b ∨ b ≤ (lo : ℝ))
    (hr : r ≤ 1) (hap : a ≤ p) (hba : b < a) (hpA : p ≤ cap) (hAr : cap ≤ r) :
    b ≤ (lo : ℝ) ∧ ∃ x, inBox (finiteBox lo hi) x ∧ x 0 = p ∧
      highInternalTopA b x = a ∧ highInternalTopCap x = cap ∧ highInternalTopR x = r := by
  have hactive := knot_right lo hi p b hp.1 hp.2 hkb (hba.trans_le hap)
  obtain ⟨u,hu,haeq⟩ := unit_parameter b p a (hba.le.trans hap) ⟨hba.le,hap⟩
  obtain ⟨v,hv,hAeq⟩ := unit_parameter p 1 cap (hpA.trans (hAr.trans hr)) ⟨hpA,hAr.trans hr⟩
  obtain ⟨w,hw,hreq⟩ := unit_parameter cap 1 r (hAr.trans hr) ⟨hAr,hr⟩
  let x := coordinates p u v w
  have hA : highInternalTopA b x = a := haeq.symm
  have hCap : highInternalTopCap x = cap := hAeq.symm
  refine ⟨hactive,x,in_finiteBox lo hi p u v w ⟨hp.1.le,hp.2⟩ hu hv hw,rfl,hA,hCap,?_⟩
  change mix (highInternalTopCap x) 1 w = r
  rw [hCap]
  exact hreq.symm

/-- First intervals below b use exactly the two low source tasks. -/
theorem low_first_selection (lo hi : ℚ) (r0 r1 p a r : ℝ)
    (hp : (lo : ℝ) < p ∧ p ≤ (hi : ℝ))
    (hk0 : (hi : ℝ) ≤ r0 ∨ r0 ≤ (lo : ℝ))
    (hk1 : (hi : ℝ) ≤ r1 ∨ r1 ≤ (lo : ℝ))
    (hr : r ∈ Icc r0 r1) (ha : 0 ≤ a) (hap : a ≤ min p r) :
    (∃ x, inBox (finiteBox lo hi) x ∧ x 0 = p ∧
      lowFirstBottomA hi r0 x = a ∧ lowFirstBottomR r0 r1 x = r) ∨
    (r0 ≤ (lo : ℝ) ∧ ∃ x, inBox (finiteBox lo hi) x ∧ x 0 = p ∧
      lowFirstTopA hi r0 r1 x = a ∧ lowFirstTopR hi r0 r1 x = r) := by
  by_cases hlow : a ≤ r0
  · exact Or.inl (low_first_bottom_coordinates lo hi r0 r1 p a r hp hk0 hr ha hap hlow)
  · exact Or.inr (low_first_top_coordinates lo hi r0 r1 p a r hp hk0 hk1 hr hap (lt_of_not_ge hlow))

/-- First intervals above b use the bottom task, or the enabled top task. -/
theorem high_first_selection (lo hi : ℚ) (b p a r : ℝ)
    (hp : (lo : ℝ) < p ∧ p ≤ (hi : ℝ))
    (hkb : (hi : ℝ) ≤ b ∨ b ≤ (lo : ℝ))
    (hr : r ∈ Icc b 1) (ha : 0 ≤ a) (hap : a ≤ min p r) :
    (∃ x, inBox (finiteBox lo hi) x ∧ x 0 = p ∧
      highFirstBottomA hi b x = a ∧ highFirstBottomR b x = r) ∨
    (b ≤ (lo : ℝ) ∧ ∃ x, inBox (finiteBox lo hi) x ∧ x 0 = p ∧
      highFirstTopA b x = a ∧ highFirstTopR b x = r) := by
  by_cases hlow : a ≤ b
  · exact Or.inl (high_first_bottom_coordinates lo hi b p a r hp hkb hr ha hap hlow)
  · exact Or.inr (high_first_top_coordinates lo hi b p a r hp hkb hr.2 hap (lt_of_not_ge hlow))

/-- At A=b the bottom branch is selected. The middle branch is precisely StrongCrossing's domain. -/
theorem high_internal_selection (lo hi : ℚ) (b p a cap r : ℝ)
    (hp : (lo : ℝ) < p ∧ p ≤ (hi : ℝ))
    (hkb : (hi : ℝ) ≤ b ∨ b ≤ (lo : ℝ))
    (hr : r ∈ Icc b 1) (ha : 0 ≤ a) (hap : a ≤ p) (hpA : p ≤ cap) (hAr : cap ≤ r) :
    ((hi : ℝ) ≤ b ∧ ∃ x, inBox (finiteBox lo hi) x ∧ x 0 = p ∧
      highInternalBottomA x = a ∧ highInternalBottomCap b x = cap ∧ highInternalBottomR b x = r) ∨
    (0 ≤ a ∧ a ≤ min p b ∧ max p b ≤ cap ∧ b < cap ∧ cap ≤ r ∧ r ≤ 1) ∨
    (b ≤ (lo : ℝ) ∧ ∃ x, inBox (finiteBox lo hi) x ∧ x 0 = p ∧
      highInternalTopA b x = a ∧ highInternalTopCap x = cap ∧ highInternalTopR x = r) := by
  by_cases hbottom : cap ≤ b
  · exact Or.inl (high_internal_bottom_coordinates lo hi b p a cap r hp hkb hr ha hap hpA hbottom)
  · have hbCap : b < cap := lt_of_not_ge hbottom
    by_cases haBottom : a ≤ b
    · exact Or.inr (Or.inl ⟨ha,le_min hap haBottom,max_le hpA hbCap.le,hbCap,hAr,hr.2⟩)
    · exact Or.inr (Or.inr (high_internal_top_coordinates lo hi b p a cap r hp hkb hr.2 hap
        (lt_of_not_ge haBottom) hpA hAr))

/-- The problematic threshold points force the source interval to end there. -/
theorem threshold_face_uses_left (lo hi : ℚ) (t : ℝ)
    (hp : (lo : ℝ) < t ∧ t ≤ (hi : ℝ))
    (hk : (hi : ℝ) ≤ t ∨ t ≤ (lo : ℝ)) : (hi : ℝ) = t := by
  apply le_antisymm (knot_left lo hi t t hp.1 hp.2 hk le_rfl) hp.2

#print axioms low_first_bottom_coordinates
#print axioms low_first_top_coordinates
#print axioms low_internal_coordinates
#print axioms high_first_bottom_coordinates
#print axioms high_first_top_coordinates
#print axioms high_internal_bottom_coordinates
#print axioms high_internal_top_coordinates
#print axioms high_internal_selection
#print axioms threshold_face_uses_left
end MetricDistortion.NumericalFiniteCoordinates

namespace MetricDistortion.Contracts.Numerics_FiniteCoordinates

theorem proved : Statement := by
  exact ⟨
    MetricDistortion.NumericalFiniteCoordinates.low_first_bottom_coordinates,
    MetricDistortion.NumericalFiniteCoordinates.low_first_top_coordinates,
    MetricDistortion.NumericalFiniteCoordinates.low_internal_coordinates,
    MetricDistortion.NumericalFiniteCoordinates.high_first_bottom_coordinates,
    MetricDistortion.NumericalFiniteCoordinates.high_first_top_coordinates,
    MetricDistortion.NumericalFiniteCoordinates.high_internal_bottom_coordinates,
    MetricDistortion.NumericalFiniteCoordinates.high_internal_top_coordinates⟩

#print axioms proved
end MetricDistortion.Contracts.Numerics_FiniteCoordinates
