import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Lower_ScoreFormula

private theorem ranking_fiber_card (N : ℕ) (q : Fin (N+1)) :
    (Finset.univ.filter fun r : Ranking (N+1) => (r 0).val = q.val).card = Nat.factorial N := by
  have heq : (Finset.univ.filter fun r : Ranking (N+1) => (r 0).val = q.val) =
      Finset.univ.filter (fun r : Ranking (N+1) => r 0 = q) := by
    ext r
    simp [Fin.ext_iff]
  rw [heq]
  have he := (Equiv.Perm.decomposeFin (n := N)).symm.sum_comp
    (fun r : Ranking (N+1) => if r 0 = q then (1 : ℕ) else 0)
  have hh : (∑ r : Ranking (N+1), if r 0 = q then (1 : ℕ) else 0) = Nat.factorial N := by
    rw [← he,Fintype.sum_prod_type]
    simp only [Equiv.Perm.decomposeFin_symm_apply_zero,Finset.sum_const,
      Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
    simp [mul_ite]
  simpa [Finset.sum_filter] using hh

private theorem reference_below {N : ℕ} (p : ℝ) (P : Lottery (N+1))
    (hP : Reference p P) (r : Ranking (N+1)) :
    below r P 0 = p*(r 0).val/N := by
  have hh : below r P 0 = ∑ c : Fin (N+1), if r c < r 0 then p/N else 0 := by
    unfold below mass
    apply Finset.sum_congr rfl
    intro c hc
    by_cases hlt : r c < r 0
    · have hc0 : c.val ≠ 0 := by
        intro he
        have : c = 0 := Fin.ext he
        simpa [this] using hlt
      simp [prefers,hlt,hP c,hc0]
    · simp [prefers,hlt]
  rw [hh, Equiv.sum_comp r (fun j => if j < r 0 then p/N else 0)]
  have hc : (Finset.univ.filter fun j : Fin (N+1) => j < r 0).card = (r 0).val := by
    have heq : (Finset.univ.filter fun j : Fin (N+1) => j < r 0) = Finset.Iio (r 0) := by
      ext j
      simp
    rw [heq]
    exact Fin.card_Iio (r 0)
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,hc]
  ring

private theorem closed_formula (h : Needs) :
    ∀ n N k, 0 < n → 0 < k → k < N → ∀ z ∈ Ioc (0 : ℝ) 1,
      ∀ D (σ : Profile n (N+1)), Symmetric σ k z →
      ∀ p ∈ Icc (0 : ℝ) 1, ∀ P, Reference p P →
        score D σ P 0 = z*(∫ s in (0 : ℝ)..1, phi D (p*k/N+s*(1-p))) +
          (1-z)*(∫ s in (0 : ℝ)..1, phi D (p+s*(1-p))) := by
  intro n N k hn hk hkN z hz D σ hσ p hp P hP
  have hzero : P.val 0 = 1-p := by simpa using hP 0
  have hcompare (r : Ranking (N+1)) : compare D r P 0 =
      ∫ s in (0 : ℝ)..1, phi D (p*(r 0).val/N+s*(1-p)) := by
    have hc := (h.child_0 (N+1) D r P 0).1
    change compare D r P 0 = ∫ s in (0 : ℝ)..1, phi D (below r P 0+s*P.val 0) at hc
    simpa [reference_below p P hP r,hzero] using hc
  have hsum (q : Fin (N+1)) :
      (∑ r ∈ Finset.univ.filter (fun r : Ranking (N+1) => (r 0).val = q.val), compare D r P 0) =
      (Nat.factorial N : ℝ)*(∫ s in (0 : ℝ)..1, phi D (p*q.val/N+s*(1-p))) := by
    calc
      _ = ∑ r ∈ Finset.univ.filter (fun r : Ranking (N+1) => (r 0).val = q.val),
          (∫ s in (0 : ℝ)..1, phi D (p*q.val/N+s*(1-p))) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hcompare,(Finset.mem_filter.mp hr).2]
      _ = _ := by simp [ranking_fiber_card]
  have hm := h.child_2 n N k hn hk hkN z hz σ hσ (fun r => compare D r P 0)
  unfold score
  rw [hm]
  rw [hsum ⟨k,hkN.trans (Nat.lt_succ_self N)⟩,hsum ⟨N,Nat.lt_succ_self N⟩]
  have hfac : (Nat.factorial N : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (hk.trans hkN)
  dsimp
  rw [mul_div_cancel_right₀ p hN]
  generalize (∫ s in (0 : ℝ)..1, phi D (p*k/N+s*(1-p))) = A
  generalize (∫ s in (0 : ℝ)..1, phi D (p+s*(1-p))) = B
  field_simp
  <;> ring

theorem from_children (h : Needs) : Statement := by
  refine ⟨?_,closed_formula h⟩
  intro n N k hn hk hkN z hz D σ hσ p hp P hP
  have hc := closed_formula h n N k hn hk hkN z hz D σ hσ p ⟨hp.1.le,hp.2.le⟩ P hP
  obtain ⟨hmono,hconv,hcont,hphi0,hphi1,hmu,hstrict⟩ := h.child_3 D
  have hNr : (0 : ℝ) < N := by exact_mod_cast hk.trans hkN
  have hkr : (k : ℝ) ≤ N := by exact_mod_cast hkN.le
  have hp0 := hp.1
  have hp1 := hp.2
  have ha0 : (0 : ℝ) ≤ p*k/N :=
    div_nonneg (mul_nonneg hp0.le (Nat.cast_nonneg k)) hNr.le
  have hap : p*k/N ≤ p :=
    (div_le_iff₀ hNr).2 (mul_le_mul_of_nonneg_left hkr hp0.le)
  have hab : p*k/N ≤ p*k/N+1-p := by linarith [hp1]
  have hb1 : p*k/N+1-p ≤ 1 := by linarith
  have hint (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
      (∫ u in a..b, phi D u) = Phi D b-Phi D a := by
    have hi0a := (hcont.mono (Icc_subset_Icc le_rfl (hab.trans hb))).intervalIntegrable_of_Icc (μ := volume) ha
    have hiab := (hcont.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc (μ := volume) hab
    have hadj := intervalIntegral.integral_add_adjacent_intervals hi0a hiab
    unfold Phi
    linarith
  have hIA : (1-p)*(∫ s in (0 : ℝ)..1, phi D (p*k/N+s*(1-p))) =
      Phi D (p*k/N+1-p)-Phi D (p*k/N) := by
    have hh := intervalIntegral.smul_integral_comp_add_mul (phi D) (1-p) (p*k/N)
      (a := (0 : ℝ)) (b := 1)
    simp only [smul_eq_mul,mul_zero,add_zero,mul_one] at hh
    have he : (fun s : ℝ => phi D (p*k/N+s*(1-p))) =
        (fun s : ℝ => phi D (p*k/N+(1-p)*s)) := by funext s; congr 1; ring
    rw [he]
    have hend : p*k/N+(1-p) = p*k/N+1-p := by ring
    rw [hend,hint (p*k/N) (p*k/N+1-p) ha0 hab hb1] at hh
    exact hh
  have hIB : (1-p)*(∫ s in (0 : ℝ)..1, phi D (p+s*(1-p))) = mu D-Phi D p := by
    have hh := intervalIntegral.smul_integral_comp_add_mul (phi D) (1-p) p
      (a := (0 : ℝ)) (b := 1)
    have he : (fun s : ℝ => phi D (p+s*(1-p))) =
        (fun s : ℝ => phi D (p+(1-p)*s)) := by funext s; congr 1; ring
    rw [he]
    simp only [smul_eq_mul,mul_zero,add_zero,mul_one] at hh
    have hend : p+(1-p) = 1 := by ring
    rw [hend,hint p 1 hp.1.le hp.2.le le_rfl,hmu] at hh
    exact hh
  rw [hc]
  calc
    _ = z*((1-p)*(∫ s in (0 : ℝ)..1, phi D (p*k/N+s*(1-p)))) +
        (1-z)*((1-p)*(∫ s in (0 : ℝ)..1, phi D (p+s*(1-p)))) := by ring
    _ = _ := by rw [hIA,hIB]

#print axioms from_children
end MetricDistortion.Contracts.Lower_ScoreFormula
