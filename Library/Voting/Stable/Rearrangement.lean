import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Geometry_Rearrangement

theorem from_children (h : Needs) : Statement := by
  intro D a p A ha hap hpA hA S hS hSA hvol hcontain
  have hφ := h.child_1 D
  have hcont : ContinuousOn (phi D) (Icc (0 : ℝ) 1) := hφ.2.2.1
  have hmono : MonotoneOn (fun u => phi D u-mu D) (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact sub_le_sub_right (hφ.1 hx hy hxy) _
  have hbase := h.child_0 (fun u => phi D u-mu D) (hcont.sub continuousOn_const)
    hmono a p A ha hap hpA hA S hS hSA hvol hcontain
  let c := a+A-p
  have haA : a ≤ A := hap.trans hpA
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hcA : c ≤ A := by dsimp [c]; linarith
  have hI (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
      IntervalIntegrable (phi D) volume u v :=
    (hcont.mono (Icc_subset_Icc hu hv)).intervalIntegrable_of_Icc huv
  have h0a := hI 0 a (by norm_num) ha (haA.trans hA)
  have h0c := hI 0 c (by norm_num) hc0 (hcA.trans hA)
  have hcAi := hI c A hc0 hcA hA
  have hleft : (∫ u in (0 : ℝ)..a, (phi D u-mu D)) = Phi D a-a*mu D := by
    rw [intervalIntegral.integral_sub h0a intervalIntegrable_const]
    simp only [Phi, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hright : (∫ u in c..A, (phi D u-mu D)) = Phi D A-Phi D c-(A-c)*mu D := by
    have hadj := intervalIntegral.integral_add_adjacent_intervals h0c hcAi
    change Phi D c+(∫ u in c..A, phi D u) = Phi D A at hadj
    rw [intervalIntegral.integral_sub hcAi intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    linarith
  calc
    (∫ u in S, (phi D u-mu D)) ≤
        (∫ u in (0 : ℝ)..a, (phi D u-mu D))+(∫ u in c..A, (phi D u-mu D)) := hbase
    _ = Phi D a-a*mu D+(Phi D A-Phi D c-(A-c)*mu D) := by rw [hleft,hright]
    _ = _ := by dsimp [c]; ring

#print axioms from_children
end MetricDistortion.Contracts.Geometry_Rearrangement
