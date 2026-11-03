import FairDivision.BF.Applications.GraphDensityWindows
import FairDivision.BF.ReplacementFairnessWitness

/-!
# The equal-size and general mixed-size density upper bounds

The only refined case left to the separate perturbation-and-transfer proof
is a single large part (s=1,r≥2). Every other upper bound follows directly
from the exact size-specific windows of the SAME root allocation.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Applications

open FairDivision FairDivision.Topology Recording FairDivision.BF.ReplacementFairness

/-- Pairwise formulation of maximum density minus minimum density ≤ b.
For a positive number of parts this is exactly the usual spread bound. -/
def HasDensitySpread {k m:ℕ} (G:SimpleGraph (Fin m))
    (A:Allocation k m) (b:ℝ):Prop:=
  ∀i j:Fin k,graphDensity G (bundle A i)-graphDensity G (bundle A j)≤b

theorem graphDensity_eq_zero_of_card_one {V:Type*} [Fintype V]
    (G:SimpleGraph V) (S:Finset V) (hS:S.card=1):graphDensity G S=0:=by
  have h:=two_mul_inducedEdges_le G S
  rw [hS] at h
  have hE:inducedEdges G S=0:=by omega
  simp [graphDensity,hE]

/-- Equal-sized parts: the paper's alpha=(r-1)/r, including r=1. -/
theorem exists_equal_size_density_partition
    (k m r:ℕ) (hk:2≤k) (hr:0<r) (hCount:m=k*r)
    (G:SimpleGraph (Fin m)):
    ∃A:Allocation k m,IsBalanced A ∧HasDensitySpread G A (densityRadius r):=by
  by_cases hrOne:r=1
  · obtain ⟨A,t,hA,hT⟩:=identical_exists_balanced_commonThreshold k m (by omega) (fun _=>0)
    have hSizes:=balanced_exact_size (by omega :0<k) hCount hA
    refine ⟨A,hA,?_⟩
    intro i j
    rw [graphDensity_eq_zero_of_card_one G _ (by simpa only [hrOne] using hSizes i),
      graphDensity_eq_zero_of_card_one G _ (by simpa only [hrOne] using hSizes j)]
    norm_num [densityRadius,hrOne]
  · have hrTwo:2≤r:=by omega
    have hm:2≤ m:=by nlinarith
    obtain ⟨A,t,hA,hWindows⟩:=exists_balanced_density_windows k m r 0 (by omega) hrTwo hm
      (by omega) (by simpa only [Nat.add_zero] using hCount) G
    have hSizes:=balanced_exact_size (by omega :0<k) hCount hA
    refine ⟨A,hA,?_⟩
    intro i j
    have hi:graphDensity G (bundle A i)≤t+densityRadius r:=by
      simpa only [hSizes i] using (hWindows i).2.2
    have hj:t≤graphDensity G (bundle A j):=(hWindows j).2.1
    linarith

/-- Any nonempty remainder: beta=r/(r+1), with the exact paper padding
of k-s dummies. The s=1 refinement is supplied separately. -/
theorem exists_mixed_size_density_partition
    (k m r s:ℕ) (hk:2≤k) (hr:0<r) (hs:0<s) (hsk:s<k)
    (hCount:m=k*r+s) (G:SimpleGraph (Fin m)):
    ∃A:Allocation k m,IsBalanced A ∧HasDensitySpread G A (densityRadius (r+1)):=by
  let q:=r+1
  let d:=k-s
  have hd:d<k:=by dsimp only [d];omega
  have hPad:m+d=k*q:=by
    dsimp only [d,q]
    simp only [Nat.mul_add,Nat.mul_one]
    omega
  have hm:2≤ m:=by nlinarith
  obtain ⟨A,t,hA,hWindows⟩:=exists_balanced_density_windows k m q d
    (by omega) (by omega) hm hd hPad G
  refine ⟨A,hA,?_⟩
  intro i j
  have hCardLe:(bundle A i).card≤q:=by have h:=(hWindows i).1;omega
  have hCardPos:0<(bundle A i).card:=by have h:=(hWindows i).1;dsimp [q] at h;omega
  have hRadius:=densityRadius_mono hCardPos hCardLe
  have hi:=(hWindows i).2.2
  have hj:=(hWindows j).2.1
  linarith

end FairDivision.BF.Applications
