import FairDivision.BF.Applications.DensityPartition
import FairDivision.BF.Applications.DensitySingleRemainder
import FairDivision.BF.Applications.DensitySharpness

/-!
# Sharp balanced density partitions: the complete reader statement

This combines the SAME manuscript proof branches: exact-deletion windows,
the one-large-part perturbation and finite star transfer, and its literal
sharp examples. The sharpness quantifiers fix the graph order and number
of parts before choosing the example graph.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Applications

open FairDivision

/-- The exact piecewise constant displayed in `applications-density`.
Here r is floor(m/k) and s is m mod k at the final public interface. -/
def sharpDensityBound (r s:ℕ):ℝ:=
  if s=0 ∨s=1 ∧2≤r then densityRadius r else densityRadius (r+1)

/-- All graphs at fixed order kr+s admit the manuscript's exact radius. -/
theorem exists_balanced_density_partition_cases
    (k m r s:ℕ) (hk:2≤k) (hr:0<r) (hs:s<k) (hCount:m=k*r+s)
    (G:SimpleGraph (Fin m)):
    ∃A:Allocation k m,IsBalanced A ∧HasDensitySpread G A (sharpDensityBound r s):=by
  by_cases hZero:s=0
  · have hCount':m=k*r:=by simpa only [hZero,Nat.add_zero] using hCount
    simpa only [sharpDensityBound,if_pos (Or.inl hZero)] using
      exists_equal_size_density_partition k m r hk hr hCount' G
  · by_cases hSpecial:s=1 ∧2≤r
    · have hCount':m=k*r+1:=by simpa only [hSpecial.1] using hCount
      simpa only [sharpDensityBound,if_pos (Or.inr hSpecial)] using
        exists_single_remainder_density_partition k m r hk hSpecial.2 hCount' G
    · have hAlpha:¬(s=0 ∨s=1 ∧2≤r):=not_or.mpr ⟨hZero,hSpecial⟩
      simpa only [sharpDensityBound,if_neg hAlpha] using
        exists_mixed_size_density_partition k m r s hk hr (by omega) hs hCount G

/-- `applications-density`: every N-vertex simple graph, 2≤k≤N,
balanced parts and exactly the displayed best possible bound. -/
theorem exists_balanced_density_partition
    (N k:ℕ) (hk:2≤k) (hkN:k≤N) (G:SimpleGraph (Fin N)):
    ∃A:Allocation k N,IsBalanced A ∧
      HasDensitySpread G A (sharpDensityBound (N/k) (N%k)):=by
  have hkPos:0<k:=by omega
  have hr:0<N/k:=Nat.div_pos hkN hkPos
  have hs:N%k<k:=Nat.mod_lt N hkPos
  have hCount:N=k*(N/k)+N%k:=by have h:=Nat.mod_add_div N k;omega
  exact exists_balanced_density_partition_cases k N (N/k) (N%k) hk hr hs hCount G

/-- For EVERY fixed N,k in the theorem's range there is a literal graph
with this optimal radius, including an attaining balanced partition. -/
theorem sharp_balanced_density_bound (N k:ℕ) (hk:2≤k) (hkN:k≤N):
    ∃G:SimpleGraph (Fin N),IsSharpDensityExample (k:=k) G
      (sharpDensityBound (N/k) (N%k)):=by
  have hkPos:0<k:=by omega
  have hr:0<N/k:=Nat.div_pos hkN hkPos
  have hs:N%k<k:=Nat.mod_lt N hkPos
  have hCount:N=k*(N/k)+N%k:=by have h:=Nat.mod_add_div N k;omega
  exact exists_sharp_density_example k N (N/k) (N%k) hk hr hs hCount

/-- The complete displayed theorem together with its 'for every fixed
N,k, best possible' clause, using one common definition of density spread. -/
theorem sharp_balanced_density_partitions (N k:ℕ) (hk:2≤k) (hkN:k≤N):
    (∀G:SimpleGraph (Fin N),∃A:Allocation k N,IsBalanced A ∧
      HasDensitySpread G A (sharpDensityBound (N/k) (N%k))) ∧
    ∃G:SimpleGraph (Fin N),IsSharpDensityExample (k:=k) G
      (sharpDensityBound (N/k) (N%k)):=
  ⟨exists_balanced_density_partition N k hk hkN,sharp_balanced_density_bound N k hk hkN⟩

end FairDivision.BF.Applications
