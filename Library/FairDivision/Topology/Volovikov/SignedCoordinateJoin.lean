import RequestProject.Dvoretzky.ElemAb.Main
import Mathlib.Tactic

/-!
# Positive-part coordinates on a join of two-point character spheres

A nonzero real coordinate vector determines a point of the two-point join:
use the positive and negative parts, normalized by the sum of absolute
values. This avoids a discontinuous choice of signs at zero coordinates.
It is continuous on the punctured vector space and commutes with every
independent coordinate sign change.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov.SignedCoordinateJoin

open scoped BigOperators
open Dvoretzky Dvoretzky.ElemAb

/-- The two real values of the multiplicative two-element label group. -/
noncomputable def sign (b : L2) : ℝ := if b=1 then 1 else -1

theorem label_cases (b : L2) : b=1 ∨ b=Multiplicative.ofAdd 1 :=
  (show ∀ b : L2, b=1 ∨ b=Multiplicative.ofAdd 1 from by decide) b

@[simp] theorem sign_one : sign 1=1 := by simp [sign]
@[simp] theorem sign_other : sign (Multiplicative.ofAdd (1 : ZMod 2))= -1 := by
  norm_num [sign]

theorem sign_mul (a b : L2) : sign (a*b)=sign a*sign b := by
  rcases label_cases a with rfl|rfl <;> rcases label_cases b with rfl|rfl
  · simp
  · simp
  · simp
  · rw [ofAdd_mul_self]
    norm_num

@[simp] theorem abs_sign (b : L2) : |sign b|=1 := by
  rcases label_cases b with rfl|rfl <;> simp

theorem sign_ofAdd (b : ZMod 2) : sign (Multiplicative.ofAdd b)=if b=0 then 1 else -1 := by
  rcases (show ∀ b : ZMod 2,b=0 ∨ b=1 from by decide) b with rfl|rfl <;> simp

variable {K : ℕ}

noncomputable def mass (v : Fin K → ℝ) : ℝ := ∑ i : Fin K,|v i|

noncomputable def coordinates (v : Fin K → ℝ) : Fin K → L2 → ℝ :=
  fun i b => max (sign b*v i) 0 / mass v

theorem mass_pos (v : Fin K → ℝ) (hv : v≠0) : 0< mass v := by
  classical
  have h : ∃ i,v i≠0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  obtain ⟨i,hi⟩ := h
  exact (abs_pos.mpr hi).trans_le (Finset.single_le_sum
    (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i))

theorem positive_parts_sum (x : ℝ) : (∑ b : L2,max (sign b*x) 0)=|x| := by
  classical
  have hLabels : (Finset.univ : Finset L2)={1,Multiplicative.ofAdd 1} := by decide
  rw [hLabels]
  simp only [Finset.sum_pair (by decide : (1 : L2)≠Multiplicative.ofAdd 1),
    sign_one,sign_other,one_mul,neg_one_mul]
  by_cases h : 0≤x
  · rw [max_eq_left h,max_eq_right (by linarith),abs_of_nonneg h]
    ring
  · have hx : x≤0 := le_of_not_ge h
    rw [max_eq_right hx,max_eq_left (by linarith),abs_of_nonpos hx]
    ring

/-- The output lies in the exact imported target join, including all faces
on which some of its character coordinates vanish. -/
theorem coordinates_mem (v : Fin K → ℝ) (hv : v≠0) : coordinates v ∈ GroupJoin L2 K := by
  classical
  have hMass := mass_pos v hv
  refine ⟨?_,?_,?_⟩
  · intro i b
    exact div_nonneg (le_max_right _ _) hMass.le
  · intro i b c hb hc
    rcases label_cases b with rfl|rfl <;> rcases label_cases c with rfl|rfl
    · rfl
    · exfalso
      have hPos : 0<v i := by
        by_contra h
        apply hb
        simp [coordinates,max_eq_right (le_of_not_gt h)]
      have hNeg : v i<0 := by
        by_contra h
        apply hc
        simp [coordinates,max_eq_right (by linarith : -(v i)≤0)]
      linarith
    · exfalso
      have hPos : 0<v i := by
        by_contra h
        apply hc
        simp [coordinates,max_eq_right (le_of_not_gt h)]
      have hNeg : v i<0 := by
        by_contra h
        apply hb
        simp [coordinates,max_eq_right (by linarith : -(v i)≤0)]
      linarith
    · rfl
  · simp only [coordinates,←Finset.sum_div,positive_parts_sum]
    exact div_self (ne_of_gt hMass)

theorem continuous_mass : Continuous (mass : (Fin K → ℝ) → ℝ) := by
  exact continuous_finset_sum _ (fun i _ => (continuous_apply i).abs)

/-- Continuity is asserted precisely where the normalization denominator
is positive; the total formula outside that locus is irrelevant. -/
theorem continuous_coordinates_comp {X : Type*} [TopologicalSpace X]
    (f : X → Fin K → ℝ) (hf : Continuous f) (hne : ∀ x,f x≠0) :
    Continuous (fun x => coordinates (f x)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro b
  exact ((continuous_const.mul ((continuous_apply i).comp hf)).max continuous_const).div
    (continuous_mass.comp hf) (fun x => ne_of_gt (mass_pos (f x) (hne x)))

noncomputable def flipCoordinates (ε : Fin K → ZMod 2) (v : Fin K → ℝ) : Fin K → ℝ :=
  fun i => sign (Multiplicative.ofAdd (ε i))*v i

theorem mass_flip (ε : Fin K → ZMod 2) (v : Fin K → ℝ) :
    mass (flipCoordinates ε v)=mass v := by
  simp [mass,flipCoordinates,abs_mul]

/-- Independent sign changes induce exactly the imported `tflip` action,
so the analytic normalization is compatible with the chain obstruction. -/
theorem coordinates_flip (ε : Fin K → ZMod 2) (v : Fin K → ℝ) :
    coordinates (flipCoordinates ε v)=tflip ε (coordinates v) := by
  funext i b
  simp only [coordinates,flipCoordinates,mass_flip,tflip,sign_mul]
  congr 2
  ring

end FairDivision.Topology.Volovikov.SignedCoordinateJoin
