import FairDivision.BF.Applications.DensityPartition

/-!
# The manuscript's epsilon perturbation and common raw deletion threshold

In the single-remainder case every augmented deletion core has r−1 or r
REAL vertices. Its modified density is therefore on the exact grid
1/(r(r+1)). Adding epsilon times real cardinality, with
 epsilon=1/(2r(r+1)), cannot reverse a strict order between two raw grid
values. The actual witnesses of the perturbed deletion brackets consequently
have pairwise compatible raw brackets; a finite maximum supplies one common
raw threshold. No stronger baseline bound replaces the paper's perturbation.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Applications

open scoped BigOperators Classical
open FairDivision FairDivision.Topology Recording

/-- Exactly the perturbation chosen in the s=1 proof. -/
def densityEpsilon (r : ℕ) : ℝ:=1/(2*(r : ℝ)*(r+1))

def perturbedModifiedDensity {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (S : Finset V) : ℝ :=
  modifiedDensity G S+densityEpsilon r*S.card

theorem densityEpsilon_pos {r : ℕ} (hr : 0<r) : 0<densityEpsilon r := by
  unfold densityEpsilon
  positivity

theorem densityEpsilon_twice {r : ℕ} (hr : 0<r) :
    2*densityEpsilon r=1/((r : ℝ)*(r+1)) := by
  have hrR : (r : ℝ)≠0:=by exact_mod_cast hr.ne'
  have hrSucc : (r : ℝ)+1≠0:=by positivity
  unfold densityEpsilon
  field_simp [hrR,hrSucc]

/-- Literal integral grid certificate for a raw deletion-core value. -/
theorem modifiedDensity_deletion_grid {V : Type*} [Fintype V]
    (G : SimpleGraph V) {r : ℕ} (hr : 0<r) (S : Finset V)
    (hSize : S.card=r ∨S.card=r-1) :
    ∃z : ℤ,modifiedDensity G S*((r : ℝ)*(r+1))=(z : ℝ) := by
  have hrR : (r : ℝ)≠0:=by exact_mod_cast hr.ne'
  have hrSucc : (r : ℝ)+1≠0:=by positivity
  rcases hSize with hSize|hSize
  · refine ⟨(inducedEdges G S : ℤ)*r,?_⟩
    unfold modifiedDensity
    rw [hSize]
    push_cast
    field_simp [hrR,hrSucc]
  · refine ⟨(inducedEdges G S : ℤ)*(r+1),?_⟩
    unfold modifiedDensity
    rw [hSize,Nat.cast_sub (by omega : 1≤r),Nat.cast_one]
    push_cast
    field_simp [hrR,hrSucc]
    ring

/-- Two distinct grid values are separated by at least one actual step. -/
theorem density_grid_gap {H a b : ℝ} (hH : 0<H)
    (ha : ∃z : ℤ,a*H=(z : ℝ)) (hb : ∃z : ℤ,b*H=(z : ℝ))
    (hba : b<a) : b+1/H≤a := by
  obtain ⟨u,hu⟩:=ha
  obtain ⟨v,hv⟩:=hb
  have hInt : v<u := by
    exact_mod_cast (show (v : ℝ)<u by nlinarith [mul_lt_mul_of_pos_right hba hH])
  have hStep : (v : ℝ)+1≤u:=by exact_mod_cast (show v+1≤u by omega)
  have hOne : (1/H)*H=1:=div_mul_cancel₀ 1 hH.ne'
  apply (mul_le_mul_iff_left₀ hH).mp
  nlinarith

/-- Perturbation cannot close even one grid gap, since its cardinality
variation is at most epsilon and the grid step is exactly 2 epsilon. -/
theorem raw_le_of_perturbed_brackets {r c d : ℕ} (hr : 0<r)
    (hc : c=r ∨c=r-1) (hd : d=r ∨d=r-1)
    {a b τ : ℝ}
    (ha : ∃z : ℤ,a*((r : ℝ)*(r+1))=(z : ℝ))
    (hb : ∃z : ℤ,b*((r : ℝ)*(r+1))=(z : ℝ))
    (hLow : a+densityEpsilon r*c≤τ) (hHigh : τ≤b+densityEpsilon r*d) : a≤b := by
  by_contra h
  have hGap:=density_grid_gap (by positivity : 0<(r : ℝ)*(r+1)) ha hb (lt_of_not_ge h)
  have hEps : 0<densityEpsilon r:=densityEpsilon_pos hr
  have hTwo:=densityEpsilon_twice hr
  have hcNat : r-1≤c:=by omega
  have hdNat : d≤r:=by omega
  have hcR : (r : ℝ)-1≤c := by
    have hCast : ((r-1 : ℕ) : ℝ)≤c:=by exact_mod_cast hcNat
    simpa only [Nat.cast_sub (by omega : 1≤r),Nat.cast_one] using hCast
  have hdR : (d : ℝ)≤r:=by exact_mod_cast hdNat
  have hLowerShift:=mul_le_mul_of_nonneg_left hcR hEps.le
  have hUpperShift:=mul_le_mul_of_nonneg_left hdR hEps.le
  nlinarith

/-- Exact augmented deletion-core sizes, retaining the at-most-one actual
dummy property after erasing the chosen item. -/
theorem augmented_deletion_core_sizes {m d r : ℕ}
    (B : Finset (Fin (m+d))) (hFull : B.card=r+1)
    (hDummy : (B∩dummyLabels m d).card≤1)
    (z : Fin (m+d)) (hz : z∈B) :
    (realPart (B.erase z)).card=r ∨(realPart (B.erase z)).card=r-1 := by
  have hErase : (B.erase z).card=r:=by rw [Finset.card_erase_of_mem hz,hFull];omega
  have hDummyErase : (B.erase z∩dummyLabels m d).card≤1 := by
    apply (Finset.card_le_card ?_).trans hDummy
    intro x hx
    obtain ⟨hxB,hxD⟩:=Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase hxB,hxD⟩
  exact realPart_full_or_short (B.erase z) hErase hDummyErase

/-- The actual epsilon-bracket witnesses yield one common unperturbed
exact-deletion threshold on the SAME augmented allocation. -/
theorem perturbedBrackets_have_common_raw_threshold {k m d r : ℕ}
    (hk : 0<k) (hr : 0<r) (G : SimpleGraph (Fin m))
    (B : Allocation k (m+d)) (τ : ℝ)
    (hB : ∀i : Fin k,(bundle B i).card=r+1 ∧
      BracketsOneDeletion (fun S=>perturbedModifiedDensity G r (realPart S)) (bundle B i) τ ∧
      (bundle B i∩dummyLabels m d).card≤1) :
    ∃t : ℝ,∀i : Fin k,
      BracketsOneDeletion (fun S=>modifiedDensity G (realPart S)) (bundle B i) t := by
  let low (i : Fin k):=((hB i).2.1.1).choose
  let high (i : Fin k):=((hB i).2.1.2).choose
  have hLowMem (i : Fin k) : low i∈bundle B i:=((hB i).2.1.1).choose_spec.1
  have hHighMem (i : Fin k) : high i∈bundle B i:=((hB i).2.1.2).choose_spec.1
  let lo (i : Fin k):=modifiedDensity G (realPart ((bundle B i).erase (low i)))
  let hi (i : Fin k):=modifiedDensity G (realPart ((bundle B i).erase (high i)))
  have hCross (i j : Fin k) : lo i≤hi j := by
    let L:=realPart ((bundle B i).erase (low i))
    let H:=realPart ((bundle B j).erase (high j))
    have hLSize:=augmented_deletion_core_sizes (bundle B i) (hB i).1 (hB i).2.2 _ (hLowMem i)
    have hHSize:=augmented_deletion_core_sizes (bundle B j) (hB j).1 (hB j).2.2 _ (hHighMem j)
    apply raw_le_of_perturbed_brackets hr hLSize hHSize
      (modifiedDensity_deletion_grid G hr L hLSize)
      (modifiedDensity_deletion_grid G hr H hHSize)
      (((hB i).2.1.1).choose_spec.2) (((hB j).2.1.2).choose_spec.2)
  have hNonempty : (Finset.univ : Finset (Fin k)).Nonempty:=⟨⟨0,hk⟩,Finset.mem_univ _⟩
  obtain ⟨a,ha,hMaximum⟩:=Finset.exists_max_image Finset.univ lo hNonempty
  refine ⟨lo a,?_⟩
  intro i
  exact ⟨⟨low i,hLowMem i,hMaximum i (Finset.mem_univ _)⟩,
    ⟨high i,hHighMem i,hCross a i⟩⟩

/-- The actual initial augmented partition for the exceptional remainder
is chosen using v_epsilon, with BOTH perturbed and raw brackets retained. -/
theorem exists_single_remainder_perturbed_partition
    (k m r : ℕ) (hk : 2≤k) (hr : 2≤r) (hCount : m=k*r+1)
    (G : SimpleGraph (Fin m)) :
    ∃(B : Allocation k (m+(k-1)))(τ t : ℝ),∀i : Fin k,
      (bundle B i).card=r+1 ∧
      (bundle B i∩dummyLabels m (k-1)).card≤1 ∧
      BracketsOneDeletion (fun S=>perturbedModifiedDensity G r (realPart S)) (bundle B i) τ ∧
      BracketsOneDeletion (fun S=>modifiedDensity G (realPart S)) (bundle B i) t := by
  have hPad : m+(k-1)=k*(r+1):=by
    simp only [Nat.mul_add,Nat.mul_one]
    omega
  obtain ⟨B,τ,hB⟩:=identical_exists_augmented_commonThreshold k m (r+1) (k-1)
    (by omega) (by omega) (by nlinarith) (by omega) hPad (perturbedModifiedDensity G r)
  obtain ⟨t,ht⟩:=perturbedBrackets_have_common_raw_threshold (by omega) (by omega) G B τ hB
  exact ⟨B,τ,t,fun i=>⟨(hB i).1,(hB i).2.2,(hB i).2.1,ht i⟩⟩

end FairDivision.BF.Applications
