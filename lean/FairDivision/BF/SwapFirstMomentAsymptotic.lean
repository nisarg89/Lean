import FairDivision.BF.SwapConditionalProbability
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The manuscript's large-n first-moment inequality

For fixed q and η(q)>0, nq log n−η(q) choose(n,2) is negative eventually.
The only asymptotic input is Mathlib's existing log(x)/x→0 theorem. This
file retains the paper's exponential comparison and exact binomial count;
it does not replace the probabilistic argument by a different construction.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.SwapFirstMomentAsymptotic

open scoped ENNReal Topology
open Filter
open SwapConditionalProbability

/-- The real version of the SAME event lower bound. -/
def etaReal (q : ℕ) : ℝ:=((1 : ℝ)/2)^((2*q).choose q-2)

theorem etaReal_positive (q : ℕ) : 0<etaReal q:=by unfold etaReal;positivity

theorem etaReal_le_one (q : ℕ) : etaReal q≤1:=
  pow_le_one₀ (by norm_num) (by norm_num)

theorem eta_eq_ofReal (q : ℕ) : eta q=ENNReal.ofReal (etaReal q) := by
  unfold eta etaReal
  rw [ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ)<2)]
  norm_num

/-- The fixed-q negative quadratic dominates the n log n term. -/
theorem eventually_negative_exponent (q : ℕ) :
    ∀ᶠn : ℕ in atTop,
      (n : ℝ)*q*Real.log n-etaReal q*(n.choose 2)<0 := by
  have hRatio : Tendsto (fun n : ℕ=>(q : ℝ)*Real.log n/n) atTop (𝓝 0) := by
    have h:=(Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply,pow_one,one_mul,add_zero,mul_div_assoc,mul_zero] using
      h.const_mul (q : ℝ)
  have hSmall : ∀ᶠn : ℕ in atTop,
      (q : ℝ)*Real.log n/n<etaReal q/4 :=
    hRatio.eventually (Iio_mem_nhds
      (div_pos (etaReal_positive q) (by norm_num : (0 : ℝ)<4)))
  filter_upwards [hSmall,eventually_ge_atTop (2 : ℕ)] with n hSmall hn
  have hnReal : (2 : ℝ)≤n:=by exact_mod_cast hn
  have hnPositive : (0 : ℝ)<n:=by linarith
  have hLog : (q : ℝ)*Real.log n<etaReal q*n/4 := by
    have h:=(div_lt_iff₀ hnPositive).mp hSmall
    nlinarith
  have hChoose : (n.choose 2 : ℝ)=(n : ℝ)*((n : ℝ)-1)/2:=Nat.cast_choose_two ℝ n
  rw [hChoose]
  have hEta:=etaReal_positive q
  have hQuadratic : etaReal q*(n : ℝ)/4≤etaReal q*((n : ℝ)-1)/2 := by
    have hGap : 0≤etaReal q*((n : ℝ)-2) :=
      mul_nonneg hEta.le (by linarith)
    nlinarith only [hGap]
  have hNegative : (q : ℝ)*Real.log n-etaReal q*((n : ℝ)-1)/2<0 :=
    sub_neg.mpr (hLog.trans_le hQuadratic)
  calc
    (n : ℝ)*q*Real.log n-etaReal q*((n : ℝ)*((n : ℝ)-1)/2)=
        (n : ℝ)*((q : ℝ)*Real.log n-etaReal q*((n : ℝ)-1)/2) := by ring
    _<0 := mul_neg_of_pos_of_neg hnPositive hNegative

/-- The exact candidate-count times avoidance-probability expression is
strictly less than one for every sufficiently large n. -/
theorem eventually_count_probability_lt_one (q : ℕ) :
    ∀ᶠn : ℕ in atTop,
      (n : ℝ≥0∞)^(n*q)*(1-eta q)^(n.choose 2)<1 := by
  filter_upwards [eventually_negative_exponent q,eventually_ge_atTop (2 : ℕ)]
    with n hExponent hn
  have hnPositive : (0 : ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  have hEtaNonnegative : 0≤etaReal q:=(etaReal_positive q).le
  have hRemaining : 0≤1-etaReal q:=sub_nonneg.mpr (etaReal_le_one q)
  have hAvoid : (1-etaReal q)^(n.choose 2)≤Real.exp (-etaReal q*(n.choose 2)) := by
    have hScalar : 1-etaReal q≤Real.exp (-etaReal q) := by
      simpa only [sub_eq_add_neg,add_comm] using Real.add_one_le_exp (-etaReal q)
    calc
      (1-etaReal q)^(n.choose 2)≤(Real.exp (-etaReal q))^(n.choose 2) :=
        pow_le_pow_left₀ hRemaining hScalar _
      _=Real.exp (-etaReal q*(n.choose 2)) := by
        rw [←Real.exp_nat_mul]
        congr 1
        ring
  have hCount : (n : ℝ)^(n*q)=Real.exp ((n : ℝ)*q*Real.log n) := by
    rw [show (n : ℝ)*q*Real.log n=((n*q : ℕ) : ℝ)*Real.log n by push_cast;ring,
      Real.exp_nat_mul,Real.exp_log hnPositive]
  have hReal : (n : ℝ)^(n*q)*(1-etaReal q)^(n.choose 2)<1 := by
    calc
      _≤Real.exp ((n : ℝ)*q*Real.log n)*Real.exp (-etaReal q*(n.choose 2)) := by
        rw [←hCount]
        exact mul_le_mul_of_nonneg_left hAvoid (by positivity)
      _=Real.exp ((n : ℝ)*q*Real.log n-etaReal q*(n.choose 2)) := by
        rw [←Real.exp_add]
        congr 1
        ring
      _<1:=Real.exp_lt_one_iff.mpr hExponent
  have hEncoding : (n : ℝ≥0∞)^(n*q)*(1-eta q)^(n.choose 2)=
      ENNReal.ofReal ((n : ℝ)^(n*q)*(1-etaReal q)^(n.choose 2)) := by
    rw [ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow hRemaining,ENNReal.ofReal_sub 1 hEtaNonnegative,
      ENNReal.ofReal_one,←eta_eq_ofReal]
  rw [hEncoding]
  simpa only [ENNReal.ofReal_one] using
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ)<1)).mpr hReal

end FairDivision.BF.SwapFirstMomentAsymptotic
