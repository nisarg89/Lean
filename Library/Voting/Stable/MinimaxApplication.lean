import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Stability_MinimaxApplication
theorem from_children (h : Needs) : Statement := by
  intro n m hn hm D σ
  let S := simplex m
  let F : (Fin m → ℝ) → (Fin m → ℝ) → ℝ :=
    fun a p => ∑ c, a c * ambientScore D σ p c
  have hS : Convex ℝ S := by
    simpa [S, simplex, stdSimplex] using convex_stdSimplex ℝ (Fin m)
  have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc (c : Fin m) : ContinuousOn (fun p => ambientScore D σ p c) S := by
    exact (continuousOn_finsetSum Finset.univ (fun v _ =>
      (h.child_1 m D (σ v) c).1)).div_const (n : ℝ)
  have hconv (c : Fin m) : ConvexOn ℝ S (fun p => ambientScore D σ p c) := by
    refine ⟨hS, ?_⟩
    intro p hp q hq a b ha hb hab
    change (∑ v, ambientCompare D (σ v) (a • p+b • q) c)/(n : ℝ) ≤
      a*((∑ v, ambientCompare D (σ v) p c)/(n : ℝ)) +
        b*((∑ v, ambientCompare D (σ v) q c)/(n : ℝ))
    calc
      _ ≤ (∑ v, (a*ambientCompare D (σ v) p c+b*ambientCompare D (σ v) q c))/(n : ℝ) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum (fun v _ =>
          (h.child_1 m D (σ v) c).2.2 hp hq ha hb hab)) hN
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  have hct : ContinuousOn (Function.uncurry F) (S ×ˢ S) := by
    apply continuousOn_finsetSum
    intro c _
    exact (((continuous_apply c).comp continuous_fst).continuousOn).mul
      ((hc c).comp continuous_snd.continuousOn (fun x hx => hx.2))
  have hca : ∀ p ∈ S, ConcaveOn ℝ S (fun a => F a p) := by
    intro p hp
    refine ⟨hS, ?_⟩
    intro a ha b hb u v hu hv huv
    dsimp [F]
    have heq : (∑ c, (u*a c+v*b c)*ambientScore D σ p c) =
        u*(∑ c, a c*ambientScore D σ p c)+v*(∑ c, b c*ambientScore D σ p c) := by
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]
    exact le_of_eq heq.symm
  have hcp : ∀ a ∈ S, ConvexOn ℝ S (fun p => F a p) := by
    intro a ha
    refine ⟨hS, ?_⟩
    intro p hp q hq u v hu hv huv
    dsimp [F]
    calc
      _ ≤ ∑ c, a c*(u*ambientScore D σ p c+v*ambientScore D σ q c) :=
        Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
          ((hconv c).2 hp hq hu hv huv) (ha.1 c))
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, smul_eq_mul, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  obtain ⟨a, ha, p, hp, hmax, hmin⟩ := h.child_0 m hm F hct hca hcp
  have hF (A P : Lottery m) : F A.val P.val = payoff D σ A P := by
    unfold F payoff
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    change (∑ v, ambientCompare D (σ v) P.val c)/(n : ℝ) =
      (∑ v, compare D (σ v) P c)/(n : ℝ)
    congr 1
    exact Finset.sum_congr rfl (fun v _ => (h.child_4 m D (σ v) P c).1.symm)
  have hdiag : F a a = mu D := by
    rw [hF ⟨a,ha⟩ ⟨a,ha⟩]
    exact h.child_3 n m hn hm D σ ⟨a,ha⟩
  refine ⟨⟨p,hp⟩, ?_⟩
  apply (h.child_2 n m D σ ⟨p,hp⟩ (mu D)).2
  intro A
  rw [← hF A ⟨p,hp⟩]
  exact (hmax A.val A.property).trans ((hmin a ha).trans hdiag.le)
#print axioms from_children
end MetricDistortion.Contracts.Stability_MinimaxApplication
