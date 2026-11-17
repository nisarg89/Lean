import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Appendix_MixingCounterexample

private def binary (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) : Lottery 2 :=
  ⟨fun c => if c = 0 then p else 1-p,by
    constructor
    · intro c
      dsimp
      split_ifs
      · exact hp.1
      · linarith [hp.2]
    · simp only [Fin.sum_univ_two]
      norm_num <;> ring⟩

private def electorate : Profile 5 2 := fun v =>
  if v.val < 3 then Equiv.swap 0 1 else Equiv.refl _

private theorem pure_weight (j k : ℕ) :
    drawWeight (PMF.pure j) k = if k = j then (1 : ℝ) else 0 := by
  by_cases hk : k = j <;> simp [drawWeight,PMF.pure_apply,hk]

private theorem pure_phi (j : ℕ) (s : ℝ) : phi (PMF.pure j) s = s^(j+1) := by
  unfold phi
  simp_rw [pure_weight,ite_mul,one_mul,zero_mul]
  simp

private theorem pure_compare (j : ℕ) (r : Ranking 2) (P : Lottery 2) (c : Fin 2) :
    compare (PMF.pure j) r P c = fixedCompare r P c (j+1) := by
  unfold compare
  simp_rw [pure_weight,ite_mul,one_mul,zero_mul]
  simp

private theorem pure_mu (j : ℕ) : mu (PMF.pure j) = 1/(j+2 : ℕ) := by
  unfold mu
  simp_rw [pure_weight,ite_div,zero_div]
  simp

private theorem avg_electorate (f : Ranking 2 → ℝ) :
    avg (fun v => f (electorate v)) =
      (3*f (Equiv.swap 0 1)+2*f (Equiv.refl _))/5 := by
  unfold avg
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_two]
  norm_num [electorate] <;> ring

private theorem integral_affine (b p : ℝ) :
    (∫ s in (0 : ℝ)..1, b+s*p) = b+p/2 := by
  have hi : IntervalIntegrable (fun s : ℝ => s*p) volume 0 1 :=
    (continuous_id.mul continuous_const).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add (f := fun _ : ℝ => b) (g := fun s : ℝ => s*p)
    intervalIntegrable_const hi,
    intervalIntegral.integral_const,intervalIntegral.integral_mul_const p (fun s : ℝ => s)]
  norm_num [integral_id] <;> ring

private theorem integral_square (b p : ℝ) :
    (∫ s in (0 : ℝ)..1, (b+s*p)^2) = b^2+b*p+p^2/3 := by
  have hpoly : (fun s : ℝ => (b+s*p)^2) =
      fun s => b^2+(2*b*p)*s+p^2*s^2 := by funext s; ring
  have hl : IntervalIntegrable (fun s : ℝ => (2*b*p)*s) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have hq : IntervalIntegrable (fun s : ℝ => p^2*s^2) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
  rw [hpoly,intervalIntegral.integral_add (intervalIntegrable_const.add hl) hq,
    intervalIntegral.integral_add intervalIntegrable_const hl]
  rw [intervalIntegral.integral_const_mul (2*b*p) (fun s : ℝ => s),
    intervalIntegral.integral_const_mul (p^2) (fun s : ℝ => s^2),
    intervalIntegral.integral_const]
  norm_num [integral_id,integral_pow] <;> ring

private theorem fixed_one (hc : Comparison_CandidateDraws.Statement)
    (r : Ranking 2) (P : Lottery 2) (c : Fin 2) :
    fixedCompare r P c 1 = below r P c+P.val c/2 := by
  have hh := (hc 2 (PMF.pure 0) r P c).1
  rw [pure_compare] at hh
  simp only [ambientCompare,pure_phi,Nat.zero_add,pow_one] at hh
  change fixedCompare r P c 1 = (∫ s in (0 : ℝ)..1, below r P c+s*P.val c) at hh
  rw [hh,integral_affine]

private theorem fixed_two (hc : Comparison_CandidateDraws.Statement)
    (r : Ranking 2) (P : Lottery 2) (c : Fin 2) :
    fixedCompare r P c 2 = (below r P c)^2+below r P c*P.val c+(P.val c)^2/3 := by
  have hh := (hc 2 (PMF.pure 1) r P c).1
  rw [pure_compare] at hh
  simp only [ambientCompare,pure_phi] at hh
  change fixedCompare r P c 2 = (∫ s in (0 : ℝ)..1, (below r P c+s*P.val c)^2) at hh
  rw [hh,integral_square]

theorem from_children (h : Needs) : Statement := by
  let P1 := binary 1 ⟨by norm_num,le_rfl⟩
  let P2 := binary (4/5) ⟨by norm_num,by norm_num⟩
  let P := binary (9/10) ⟨by norm_num,by norm_num⟩
  have hcount : (Finset.univ.filter fun v => prefers (electorate v) 0 1).card = 3 := by
    have hf : (Finset.univ.filter fun v => prefers (electorate v) 0 1) =
        ({0,1,2} : Finset (Fin 5)) := by
      ext v
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
        Finset.mem_singleton]
      fin_cases v <;> norm_num [electorate,prefers]
    rw [hf]
    norm_num
  have hmix (c : Fin 2) : P.val c = (P1.val c+P2.val c)/2 := by
    fin_cases c <;> norm_num [P,P1,P2,binary]
  have hstable1 : Stable (PMF.pure 0) electorate P1 := by
    intro c
    unfold score
    rw [avg_electorate (fun r => compare (PMF.pure 0) r P1 c),pure_mu]
    simp_rw [pure_compare,fixed_one h.child_0]
    fin_cases c <;>
      norm_num [below,mass,prefers,P1,binary,Fin.sum_univ_two]
  have hstable2 : Stable (PMF.pure 1) electorate P2 := by
    intro c
    unfold score
    rw [avg_electorate (fun r => compare (PMF.pure 1) r P2 c),pure_mu]
    simp_rw [pure_compare,fixed_two h.child_0]
    fin_cases c <;>
      norm_num [below,mass,prefers,P2,binary,Fin.sum_univ_two]
  have hone : avg (fun v => fixedCompare (electorate v) P 0 1) = 51/100 := by
    norm_num [avg,Fin.sum_univ_succ,fixed_one h.child_0,below,mass,prefers,
      electorate,P,binary,Fin.sum_univ_two]
  have htwo : avg (fun v => fixedCompare (electorate v) P 0 2) = 33/100 := by
    norm_num [avg,Fin.sum_univ_succ,fixed_two h.child_0,below,mass,prefers,
      electorate,P,binary,Fin.sum_univ_two]
  refine ⟨electorate,P1,P2,P,hcount,?_,?_,hmix,hstable1,hstable2,hone,htwo,?_⟩
  · norm_num [P1,binary]
  · norm_num [P2,binary]
  · rw [hone,htwo]
    norm_num

#print axioms from_children
end MetricDistortion.Contracts.Appendix_MixingCounterexample
