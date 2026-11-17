import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Analysis_GeneratingFunction

theorem from_children (h : Needs) : Statement := by
  intro D
  have hs (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      Summable (fun k => drawWeight D k*x^(k+1)) := (h.child_0 D x hx).1
  have hw : ∀ k, 0 ≤ drawWeight D k := fun k => ENNReal.toReal_nonneg
  have hweights : Summable (drawWeight D) := by
    simpa using hs 1 (by constructor <;> norm_num)
  have hm : MonotoneOn (phi D) (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact Summable.tsum_le_tsum
      (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hxy (k+1)) (hw k))
      (hs x hx) (hs y hy)
  have hterm (k : ℕ) : ConvexOn ℝ (Icc (0 : ℝ) 1)
      (fun x : ℝ => drawWeight D k*x^(k+1)) := by
    simpa only [smul_eq_mul] using ConvexOn.smul (hw k)
      ((convexOn_pow (k+1)).subset (fun _ hx => hx.1) (convex_Icc 0 1))
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) (phi D) := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hcomb : a*x+b*y ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
      · nlinarith [mul_le_mul_of_nonneg_left hx.2 ha,mul_le_mul_of_nonneg_left hy.2 hb]
    have hrhs : HasSum (fun k => a*(drawWeight D k*x^(k+1))+b*(drawWeight D k*y^(k+1)))
        (a*phi D x+b*phi D y) := ((hs x hx).hasSum.mul_left a).add ((hs y hy).hasSum.mul_left b)
    calc
      phi D (a • x+b • y) ≤ ∑' k, (a*(drawWeight D k*x^(k+1))+b*(drawWeight D k*y^(k+1))) :=
        Summable.tsum_le_tsum (fun k => (hterm k).2 hx hy ha hb hab) (hs _ hcomb) hrhs.summable
      _ = a • phi D x+b • phi D y := hrhs.tsum_eq
  have hcont : ContinuousOn (phi D) (Icc (0 : ℝ) 1) := by
    apply continuousOn_tsum (fun k => (by fun_prop : ContinuousOn
      (fun x : ℝ => drawWeight D k*x^(k+1)) (Icc (0 : ℝ) 1))) hweights
    intro k x hx
    have hn := (h.child_0 D x hx).2 k
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn.1] using hn.2
  have hone : phi D 1 = 1 := by
    have ht : (∑' k, drawWeight D k) = 1 := by
      simpa [drawWeight] using (ENNReal.tsum_toReal_eq D.apply_ne_top).symm
    simpa [phi] using ht
  have hint : Phi D 1 = mu D := by
    simpa [Phi,mu,add_assoc,one_add_one_eq_two,div_eq_mul_inv] using
      h.child_1 D 0 1 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hm,hc,hcont,by simp [phi],hone,hint,?_⟩
  intro hne
  have hindex : ∃ k : ℕ, 1 ≤ k ∧ 0 < drawWeight D k := by
    by_contra! H
    have hz : ∀ k : ℕ, k ≠ 0 → D k = 0 := by
      intro k hk
      have hzreal : (D k).toReal = 0 := le_antisymm (H k (by omega)) ENNReal.toReal_nonneg
      exact ((ENNReal.toReal_eq_zero_iff (D k)).mp hzreal).resolve_right (D.apply_ne_top k)
    have hzero : D 0 = 1 := by
      have ht : (∑' k, D k) = D 0 := tsum_eq_single 0 (fun k hk => hz k hk)
      rw [D.tsum_coe] at ht
      exact ht.symm
    apply hne
    apply PMF.ext
    intro k
    by_cases hk : k=0
    · subst k
      simp [hzero,PMF.pure_apply]
    · simp [hz k hk,hk,PMF.pure_apply]
  obtain ⟨k,hk,hkpos⟩ := hindex
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hcomb : a*x+b*y ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg ha.le hx.1) (mul_nonneg hb.le hy.1)
    · nlinarith [mul_le_mul_of_nonneg_left hx.2 ha.le,mul_le_mul_of_nonneg_left hy.2 hb.le]
  have hstrict : drawWeight D k*(a*x+b*y)^(k+1) <
      a*(drawWeight D k*x^(k+1))+b*(drawWeight D k*y^(k+1)) := by
    have hp := (strictConvexOn_pow (n := k+1) (by omega)).2 hx.1 hy.1 hxy ha hb hab
    have hmul := mul_lt_mul_of_pos_left hp hkpos
    convert hmul using 1 <;> simp only [smul_eq_mul] <;> ring
  have hrhs : HasSum (fun k => a*(drawWeight D k*x^(k+1))+b*(drawWeight D k*y^(k+1)))
      (a*phi D x+b*phi D y) := ((hs x hx).hasSum.mul_left a).add ((hs y hy).hasSum.mul_left b)
  calc
    phi D (a • x+b • y) < ∑' i, (a*(drawWeight D i*x^(i+1))+b*(drawWeight D i*y^(i+1))) :=
      Summable.tsum_lt_tsum (fun i => (hterm i).2 hx hy ha.le hb.le hab)
        hstrict (hs _ hcomb) hrhs.summable
    _ = a • phi D x+b • phi D y := hrhs.tsum_eq

#print axioms from_children
end MetricDistortion.Contracts.Analysis_GeneratingFunction
