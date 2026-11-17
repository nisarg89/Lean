import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Lower_FiniteElectorate

theorem from_children (_h : Needs) : Statement := by
  intro N k hk hkN z hz hz1
  let a : ℕ := z.num.natAbs
  let b : ℕ := z.den
  have hnum : 0 < z.num := Rat.num_pos.mpr hz
  have haZ : (a : ℤ) = z.num := Int.natAbs_of_nonneg hnum.le
  have haR : (a : ℝ) = (z.num : ℝ) := by exact_mod_cast haZ
  have ha : 0 < a := by exact_mod_cast (haZ.symm ▸ hnum)
  have hb : 0 < b := z.den_pos
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hza : (z : ℝ) = (a : ℝ)/b := by
    rw [Rat.cast_def]
    dsimp [b]
    rw [haR]
  have hab : a ≤ b := by
    have hzR : (z : ℝ) ≤ 1 := by exact_mod_cast hz1
    rw [hza] at hzR
    have : (a : ℝ) ≤ b := by simpa using (div_le_iff₀ hbR).mp hzR
    exact_mod_cast this
  let mult : Ranking (N+1) → ℕ := fun r =>
    if (r 0).val = k then a else if (r 0).val = N then b-a else 0
  let V := Σ r : Ranking (N+1), Fin (mult r)
  let n := Fintype.card V
  let e : Fin n ≃ V := (Fintype.equivFin V).symm
  let σ : Profile n (N+1) := fun v => (e v).1
  have hNfac : 0 < Nat.factorial N := Nat.factorial_pos N
  have hpossum : ∑ q : Fin (N+1),
      (if q.val = k then a else if q.val = N then b-a else 0) = b := by
    let qk : Fin (N+1) := ⟨k,hkN.trans (Nat.lt_succ_self N)⟩
    let qN : Fin (N+1) := ⟨N,Nat.lt_succ_self N⟩
    have hs (q : Fin (N+1)) :
        (if q.val = k then a else if q.val = N then b-a else 0) =
        (if q = qk then a else 0)+(if q = qN then b-a else 0) := by
      have hkN' : qk ≠ qN := by intro he; have := congrArg Fin.val he; dsimp [qk,qN] at this; omega
      have hqk : (q.val = k) ↔ q = qk := by simp [qk,Fin.ext_iff]
      have hqN : (q.val = N) ↔ q = qN := by simp [qN,Fin.ext_iff]
      by_cases hkq : q = qk <;> by_cases hNq : q = qN
      · exact False.elim (hkN' (hkq.symm.trans hNq))
      · simp [hqk,hqN,hkq,hNq,qk,qN,Nat.ne_of_lt hkN,Ne.symm (Nat.ne_of_lt hkN)]
      · simp [hqk,hqN,hkq,hNq,qk,qN,Nat.ne_of_lt hkN,Ne.symm (Nat.ne_of_lt hkN)]
      · simp [hqk,hqN,hkq,hNq,qk,qN,Nat.ne_of_lt hkN,Ne.symm (Nat.ne_of_lt hkN)]
    simp_rw [hs,Finset.sum_add_distrib]
    simp [Nat.add_sub_of_le hab]
  have hncard : n = b*Nat.factorial N := by
    dsimp [n,V]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    have heq := (Equiv.Perm.decomposeFin (n := N)).symm.sum_comp mult
    rw [← heq,Fintype.sum_prod_type]
    simp only [mult,Equiv.Perm.decomposeFin_symm_apply_zero,Finset.sum_const,
      Fintype.card_perm,Fintype.card_fin,Finset.card_univ,nsmul_eq_mul]
    rw [← Finset.mul_sum,hpossum]
    exact Nat.mul_comm _ _
  have hn : 0 < n := by rw [hncard]; exact Nat.mul_pos hb hNfac
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hfiber (r : Ranking (N+1)) :
      (Finset.univ.filter fun v => σ v = r).card = mult r := by
    have heq := e.sum_comp (fun i : V => if i.1 = r then (1 : ℕ) else 0)
    have hh : (∑ v : Fin n, if σ v = r then (1 : ℕ) else 0) = mult r := by
      change (∑ v : Fin n, (fun i : V => if i.1 = r then (1 : ℕ) else 0) (e v)) = mult r
      rw [heq,Fintype.sum_sigma]
      calc
        _ = ∑ s : Ranking (N+1), if s = r then mult r else 0 := by
          apply Finset.sum_congr rfl
          intro s hs
          by_cases he : s = r
          · subst s; simp
          · simp [he]
        _ = mult r := by simp
    simpa [Finset.sum_filter] using hh
  refine ⟨n,hn,σ,?_⟩
  intro r
  rw [hfiber,hncard]
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hbR
  have hfac0 : (Nat.factorial N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hNfac
  by_cases hrk : (r 0).val = k
  · simp only [mult,hrk,if_pos]
    rw [hza]
    push_cast
    field_simp
    <;> ring
  · by_cases hrN : (r 0).val = N
    · simp only [mult,hrk,hrN,show N ≠ k from Ne.symm (Nat.ne_of_lt hkN),if_false,if_true]
      rw [Nat.cast_sub hab,hza]
      push_cast
      field_simp
      <;> ring
    · simp [mult,hrk,hrN]

#print axioms from_children
end MetricDistortion.Contracts.Lower_FiniteElectorate
