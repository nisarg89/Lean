import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Lower_SymmetricAverages

theorem proved : Statement := by
  intro n N k hn hk hkN z hz σ hσ f
  have hfiber : (∑ r : Ranking (N+1),
      ((Finset.univ.filter fun v => σ v = r).card : ℝ)*f r) = ∑ v, f (σ v) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_fiberwise' (Finset.univ : Finset (Fin n)) σ f)
  have hfreq (r : Ranking (N+1)) :
      ((Finset.univ.filter fun v => σ v = r).card : ℝ)/n =
      (if (r 0).val = k then z/(Nat.factorial N) else 0) +
      (if (r 0).val = N then (1-z)/(Nat.factorial N) else 0) := by
    rw [hσ r]
    have hkn : k ≠ N := Nat.ne_of_lt hkN
    have hNk : N ≠ k := Ne.symm hkn
    by_cases hrk : (r 0).val = k <;> by_cases hrN : (r 0).val = N
    · omega
    · simp [hrk,hrN,hkn,hNk]
    · simp [hrk,hrN,hkn,hNk]
    · simp [hrk,hrN,hkn,hNk]
  unfold avg
  rw [← hfiber,Finset.sum_div]
  calc
    (∑ r : Ranking (N+1),
      (((Finset.univ.filter fun v => σ v = r).card : ℝ)*f r)/n) =
      ∑ r : Ranking (N+1),
        (((Finset.univ.filter fun v => σ v = r).card : ℝ)/n)*f r := by
          apply Finset.sum_congr rfl
          intro r hr
          ring
    _ = ∑ r : Ranking (N+1),
        ((if (r 0).val = k then z/(Nat.factorial N) else 0) +
        (if (r 0).val = N then (1-z)/(Nat.factorial N) else 0))*f r := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [hfreq]
    _ = _ := by
      simp_rw [add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_filter]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro r hr <;> split_ifs <;> simp

#print axioms proved
end MetricDistortion.Contracts.Lower_SymmetricAverages
