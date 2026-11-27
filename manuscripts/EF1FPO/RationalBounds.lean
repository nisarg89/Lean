import Mathlib

/-! Exact arithmetic bounds for the rational weights and the repair cycles. -/

set_option autoImplicit false

open scoped BigOperators

namespace EF1FPO.RationalBounds

def PositiveRatio (B : ℕ) (x : ℝ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ≤ B ∧ b ≤ B ∧ x = (a : ℝ) / (b : ℝ)

theorem of_rat (B : ℕ) (q : ℚ) (hq : 0 < q)
    (hnum : q.num.natAbs ≤ B) (hden : q.den ≤ B) :
    PositiveRatio B (q : ℝ) := by
  have hn : 0 < q.num := Rat.num_pos.mpr hq
  refine ⟨q.num.natAbs, q.den, Int.natAbs_pos.mpr hn.ne', q.den_pos, hnum, hden, ?_⟩
  rw [Rat.cast_def]
  have hr : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg hn.le)
  rw [hr]

theorem to_rat (B : ℕ) (x : ℝ) (h : PositiveRatio B x) :
    ∃ q : ℚ, x = (q : ℝ) ∧ 0 < q ∧ q.num.natAbs ≤ B ∧ q.den ≤ B := by
  obtain ⟨a, b, ha, hb, haB, hbB, hx⟩ := h
  let q := mkRat (a : ℤ) b
  have hq : q = (a : ℚ) / (b : ℚ) := by simp [q, Rat.mkRat_eq_div]
  have hqpos : 0 < q := by
    rw [hq]
    exact div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  refine ⟨q, ?_, hqpos, ?_, ?_⟩
  · rw [hx, hq, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
  · have hn : q.num.natAbs = a / b.gcd a := by
      simp only [q, Rat.num_mkRat, hb.ne', ite_false, Int.natAbs_natCast, ← Int.natCast_ediv]
    exact hn.le.trans ((Nat.div_le_self _ _).trans haB)
  · have hd : q.den = b / b.gcd a := by
      simp only [q, Rat.den_mkRat, hb.ne', ite_false, Int.natAbs_natCast]
    exact hd.le.trans ((Nat.div_le_self _ _).trans hbB)

theorem mul_ratio {B C : ℕ} {x y : ℝ} (hx : PositiveRatio B x) (hy : PositiveRatio C y) :
    PositiveRatio (B * C) (x * y) := by
  obtain ⟨a, b, ha, hb, haB, hbB, hx⟩ := hx
  obtain ⟨c, d, hc, hd, hcC, hdC, hy⟩ := hy
  refine ⟨a * c, b * d, Nat.mul_pos ha hc, Nat.mul_pos hb hd,
    Nat.mul_le_mul haB hcC, Nat.mul_le_mul hbB hdC, ?_⟩
  rw [hx, hy, Nat.cast_mul, Nat.cast_mul, div_mul_div_comm]

theorem inv_ratio {B : ℕ} {x : ℝ} (h : PositiveRatio B x) :
    PositiveRatio B x⁻¹ := by
  obtain ⟨a, b, ha, hb, haB, hbB, hx⟩ := h
  exact ⟨b, a, hb, ha, hbB, haB, by rw [hx, inv_div]⟩

theorem mono_ratio {B C : ℕ} {x : ℝ} (h : PositiveRatio B x) (hle : B ≤ C) :
    PositiveRatio C x := by
  obtain ⟨a, b, ha, hb, haB, hbB, hx⟩ := h
  exact ⟨a, b, ha, hb, haB.trans hle, hbB.trans hle, hx⟩

theorem sum_num_den_bound {α : Type*} (S : Finset α) (v : α → ℚ) (L : ℕ)
    (h : ∀ g ∈ S, 0 ≤ v g ∧ (v g).num.natAbs ≤ 2 ^ L ∧ (v g).den ≤ 2 ^ L) :
    (∑ g ∈ S, v g).num.natAbs ≤ S.card * 2 ^ (L * (S.card + 1)) ∧
      (∑ g ∈ S, v g).den ≤ 2 ^ (L * S.card) := by
  let q : ℚ := ∑ g ∈ S, v g
  have hq : 0 ≤ q := Finset.sum_nonneg (fun g hg => (h g hg).1)
  have hDen : q.den ≤ 2 ^ (L * S.card) := by
    calc
      _ ≤ ∏ g ∈ S, (v g).den := Nat.le_of_dvd
        (Finset.prod_pos (fun g _ => (v g).den_pos)) (Finset.Rat.den_sum_dvd_prod_den S v)
      _ ≤ ∏ _ ∈ S, 2 ^ L := Finset.prod_le_prod' (fun g hg => (h g hg).2.2)
      _ = _ := by simp [pow_mul]
  have natAbs_num_cast (r : ℚ) (hr : 0 ≤ r) : (r.num.natAbs : ℚ) = (r.num : ℚ) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hr))
  have hVal (g : α) (hg : g ∈ S) : v g ≤ (2 : ℚ) ^ L := by
    have he : (1 : ℚ) ≤ (v g).den := by exact_mod_cast Nat.one_le_of_lt (v g).den_pos
    calc
      _ ≤ ((v g).den : ℚ) * v g := by simpa using mul_le_mul_of_nonneg_right he (h g hg).1
      _ = ((v g).num.natAbs : ℚ) := (Rat.den_mul_eq_num (v g)).trans
        (natAbs_num_cast (v g) (h g hg).1).symm
      _ ≤ _ := by exact_mod_cast (h g hg).2.1
  have hSum : q ≤ (S.card : ℚ) * (2 : ℚ) ^ L := by
    calc
      _ ≤ ∑ _ ∈ S, (2 : ℚ) ^ L := Finset.sum_le_sum hVal
      _ = _ := by simp
  have hNumCast : (q.num.natAbs : ℚ) ≤ (S.card : ℚ) * (2 : ℚ) ^ (L * (S.card + 1)) := by
    calc
      _ = (q.den : ℚ) * q := (natAbs_num_cast q hq).trans (Rat.den_mul_eq_num q).symm
      _ ≤ (2 : ℚ) ^ (L * S.card) * ((S.card : ℚ) * (2 : ℚ) ^ L) :=
        mul_le_mul (by exact_mod_cast hDen) hSum hq (by positivity)
      _ = _ := by rw [Nat.mul_succ, pow_add]; ring
  exact ⟨by exact_mod_cast hNumCast, hDen⟩

theorem log_le_negative_inv {B : ℕ} {x : ℝ} (h : PositiveRatio B x) (hlt : x < 1) :
    Real.log x ≤ -(B : ℝ)⁻¹ := by
  obtain ⟨a, b, ha, hb, _, hbB, hx⟩ := h
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hab : a < b := by
    rw [hx, div_lt_one₀ hb'] at hlt
    exact_mod_cast hlt
  have hIntGap : (a : ℝ) + 1 ≤ b := by exact_mod_cast Nat.succ_le_of_lt hab
  have hFrac : (a : ℝ) / (b : ℝ) + (b : ℝ)⁻¹ ≤ 1 := by
    rw [← one_div, ← add_div, div_le_one hb']
    exact hIntGap
  have hNInv : (B : ℝ)⁻¹ ≤ (b : ℝ)⁻¹ := inv_anti₀ hb' (by exact_mod_cast hbB)
  rw [hx]
  linarith [Real.log_le_sub_one_of_pos (div_pos ha' hb')]

end EF1FPO.RationalBounds
