import FairDivision.BF.Applications.DensitySingleRemainderClassification
import FairDivision.BF.Applications.GraphDensityStarDescent

/-!
# The sharp single-remainder density upper bound

Choose the manuscript's epsilon-perturbed common exact-deletion allocation.
The actual raw brackets intersect on its unperturbed density grid. If its
spread is already at most alpha, keep it. Otherwise the SAME two thresholds
identify the large star, and the paper's finite leaf transfers finish the
partition. No alternate allocation theorem replaces the perturbation.
-/

set_option autoImplicit false
noncomputable section

namespace FairDivision.BF.Applications

open FairDivision FairDivision.Topology Recording
open scoped Classical

/-- The exceptional s=1 improvement from beta=r/(r+1) to alpha=(r-1)/r.
This is the exact upper bound asserted in the density application. -/
theorem exists_single_remainder_density_partition
    (k m r : ℕ) (hk : 2≤k) (hrTwo : 2≤r) (hCount : m=k*r+1)
    (G : SimpleGraph (Fin m)) :
    ∃A : Allocation k m,IsBalanced A ∧HasDensitySpread G A (densityRadius r) := by
  obtain ⟨B,τ,t,hB⟩:=exists_single_remainder_perturbed_partition k m r hk hrTwo hCount G
  let A:=actualRealAllocation B
  by_cases hGood : HasDensitySpread G A (densityRadius r)
  ·have hPad : m+(k-1)=k*(r+1) := by
     simp only [Nat.mul_add,Nat.mul_one]
     omega
   have hBalanced : IsBalanced A:=actualRealAllocation_balanced hPad (by omega)
     (by omega) (by omega) B (fun i=>⟨(hB i).1,(hB i).2.1⟩)
   exact ⟨A,hBalanced,hGood⟩
  ·obtain ⟨j,hLarge,hStar,hSmall⟩:=single_remainder_bad_spread_is_star
     k m r hk hrTwo hCount G B τ t hB hGood
   exact densityStar_descent_exists hk hrTwo hCount G A j hLarge hStar hSmall

end FairDivision.BF.Applications
