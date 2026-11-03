import FairDivision.BF.Applications.DensityDeletionGrid
import FairDivision.BF.Applications.DensitySharpnessSizes
import FairDivision.BF.Applications.GraphDensityTransfer

/-!
# The exceptional spread detects exactly the manuscript's large star

Retain both thresholds on the same augmented allocation. The raw grid
forces the exceptional gap to be beta. Its lower density is an integer;
the epsilon brackets exclude every positive integer, leaving an edgeless
small part and the unique large star. This is the classification used by
the paper's finite leaf-transfer descent.
-/

set_option autoImplicit false
noncomputable section

namespace FairDivision.BF.Applications

open FairDivision FairDivision.Topology Recording
open scoped BigOperators Classical

/-- With remainder one there is at most one large part. -/
theorem density_single_large_part {k m r : ℕ} (hk : 2≤k)
    (hCount : m=k*r+1) {A : Allocation k m} (hA : IsBalanced A)
    (j : Fin k) (hj : (bundle A j).card=r+1) :
    ∀i : Fin k,i≠j→(bundle A i).card=r := by
  intro i hij
  rcases density_balanced_size_cases (by omega : 0<k) (by omega : 1<k)
    hCount hA i with hi|hi
  · exact hi
  · have hEach : ∀l : Fin k,r+(if l=i then 1 else 0)+(if l=j then 1 else 0)≤
        (bundle A l).card := by
      intro l
      by_cases hli : l=i
      · subst l
        simp only [ite_true,if_neg hij,Nat.add_zero]
        omega
      · by_cases hlj : l=j
        · subst l
          simp only [if_neg hli,ite_true,Nat.add_zero]
          omega
        · simp only [if_neg hli,if_neg hlj,Nat.add_zero]
          rcases density_balanced_size_cases (by omega : 0<k) (by omega : 1<k)
            hCount hA l with hl|hl <;> omega
    have hTotal : k*r+2≤ m := by
      calc
        k*r+2=∑l : Fin k,(r+(if l=i then 1 else 0)+(if l=j then 1 else 0)) := by
          simp [Finset.sum_add_distrib]
        _≤∑l : Fin k,(bundle A l).card:=Finset.sum_le_sum (fun l _=>hEach l)
        _=m:=sum_bundle_card A
    omega

theorem densityRadius_succ (r : ℕ) :
    densityRadius (r+1)=(r : ℝ)/(r+1) := by
  unfold densityRadius
  push_cast
  congr 1
  ring

theorem densityRadius_grid_gap {r : ℕ} (hr : 0<r) :
    densityRadius (r+1)-densityRadius r=1/((r : ℝ)*(r+1)) := by
  have hR : (r : ℝ)≠0:=by exact_mod_cast hr.ne'
  have hRp : (r : ℝ)+1≠0:=by positivity
  rw [densityRadius_succ]
  unfold densityRadius
  field_simp [hR,hRp]
  ring

/-- Both possible real-part densities are on the common r(r+1) grid. -/
theorem graphDensity_part_grid {V : Type*} [Fintype V]
    (G : SimpleGraph V) {r : ℕ} (hr : 0<r) (S : Finset V)
    (hSize : S.card=r ∨S.card=r+1) :
    ∃z : ℤ,graphDensity G S*((r : ℝ)*(r+1))=(z : ℝ) := by
  have hR : (r : ℝ)≠0:=by exact_mod_cast hr.ne'
  have hRp : (r : ℝ)+1≠0:=by positivity
  rcases hSize with hSize|hSize
  ·refine ⟨(inducedEdges G S : ℤ)*(r+1),?_⟩
   unfold graphDensity
   rw [hSize]
   push_cast
   field_simp [hR,hRp]
  ·refine ⟨(inducedEdges G S : ℤ)*r,?_⟩
   unfold graphDensity
   rw [hSize]
   push_cast
   field_simp [hR,hRp]

/-- A gap strictly between alpha and beta cannot occur on the common grid. -/
theorem density_bad_gap_eq_beta {V : Type*} [Fintype V]
    (G : SimpleGraph V) {r : ℕ} (hr : 0<r) (B A : Finset V)
    (hB : B.card=r+1) (hA : A.card=r)
    (hBad : densityRadius r<graphDensity G B-graphDensity G A)
    (hUpper : graphDensity G B-graphDensity G A≤densityRadius (r+1)) :
    graphDensity G B-graphDensity G A=densityRadius (r+1) := by
  obtain ⟨u,hu⟩:=graphDensity_part_grid G hr B (Or.inr hB)
  obtain ⟨v,hv⟩:=graphDensity_part_grid G hr A (Or.inl hA)
  have hDiff : ∃z : ℤ,(graphDensity G B-graphDensity G A)*
      ((r : ℝ)*(r+1))=(z : ℝ) := by
    refine ⟨u-v,?_⟩
    push_cast
    nlinarith
  have hBeta : ∃z : ℤ,densityRadius (r+1)*((r : ℝ)*(r+1))=(z : ℝ) := by
    refine ⟨(r : ℤ)^2,?_⟩
    rw [densityRadius_succ]
    push_cast
    have hRp : (r : ℝ)+1≠0:=by positivity
    field_simp [hRp]
  apply le_antisymm hUpper
  by_contra h
  have hGap:=density_grid_gap (by positivity : 0<(r : ℝ)*(r+1)) hBeta hDiff
    (lt_of_not_ge h)
  have hStep:=densityRadius_grid_gap hr
  linarith

/-- Clearing the two literal denominators shows that the lower density is
an integer. No integrality assumption on a threshold is introduced. -/
theorem density_lower_integer_of_beta_gap {V : Type*} [Fintype V]
    (G : SimpleGraph V) {r : ℕ} (hr : 0<r) (B A : Finset V)
    (hB : B.card=r+1) (hA : A.card=r)
    (hGap : graphDensity G B-graphDensity G A=densityRadius (r+1)) :
    ∃z : ℤ,graphDensity G A=(z : ℝ) ∧0≤z := by
  have hR : (r : ℝ)≠0:=by exact_mod_cast hr.ne'
  have hRp : (r : ℝ)+1≠0:=by positivity
  have hEq : (r : ℝ)*(inducedEdges G B : ℝ)=
      ((r : ℝ)+1)*(inducedEdges G A : ℝ)+(r : ℝ)^2 := by
    rw [graphDensity,graphDensity,hB,hA,densityRadius_succ] at hGap
    push_cast at hGap
    field_simp [hR,hRp] at hGap
    nlinarith
  let z : ℤ:=(inducedEdges G B : ℤ)-(inducedEdges G A : ℤ)-r
  have hz : graphDensity G A=(z : ℝ) := by
    unfold graphDensity
    rw [hA]
    apply (div_eq_iff hR).mpr
    dsimp only [z]
    push_cast
    nlinarith
  refine ⟨z,hz,?_⟩
  exact_mod_cast (hz▸graphDensity_nonneg G A)

/-- When an augmented part is entirely real and has r+1 vertices, every
exact deletion is real and has r real vertices. -/
theorem large_real_deletion_size {m d r : ℕ}
    (B : Finset (Fin (m+d))) (hFull : B.card=r+1)
    (hReal : (realPart B).card=r+1) (hDummy : (B∩dummyLabels m d).card≤1)
    (z : Fin (m+d)) (hz : z∈B) :
    (realPart (B.erase z)).card=r ∧
      ∃x∈realPart B,realPart (B.erase z)=(realPart B).erase x := by
  have hSize:=augmented_deletion_core_sizes B hFull hDummy z hz
  rcases augmentedDeletion_real_cases B z hz with hSame|hErase
  ·rw [hSame,hReal] at hSize
   omega
  ·obtain ⟨x,hx,hErase⟩:=hErase
   refine ⟨?_,x,hx,hErase⟩
   rw [hErase,Finset.card_erase_of_mem hx,hReal]
   omega

/-- Under a positive integral lower density, every perturbed small-part
deletion is at most a+epsilon(r-1), including the dummy deletion. -/
theorem perturbed_small_deletion_le {m d r : ℕ} (hr : 2≤r)
    (G : SimpleGraph (Fin m)) (B : Finset (Fin (m+d)))
    (hReal : (realPart B).card=r) (hPositive : 1≤graphDensity G (realPart B))
    (z : Fin (m+d)) (hz : z∈B) :
    perturbedModifiedDensity G r (realPart (B.erase z))≤
      graphDensity G (realPart B)+densityEpsilon r*(r-1 : ℕ) := by
  have hR : (0 : ℝ)<r:=by exact_mod_cast (show 0<r by omega)
  have hRTwo : (2 : ℝ)≤r:=by exact_mod_cast hr
  have hRp : (r : ℝ)+1≠0:=by positivity
  have hEps : 0<densityEpsilon r:=densityEpsilon_pos (by omega)
  rcases augmentedDeletion_real_cases B z hz with hSame|⟨x,hx,hErase⟩
  ·rw [hSame]
   have hRelation : modifiedDensity G (realPart B)=
       (r : ℝ)/(r+1)*graphDensity G (realPart B) := by
     unfold modifiedDensity graphDensity
     rw [hReal]
     field_simp [hR.ne',hRp]
   have hEpsSmall : densityEpsilon r≤1/((r : ℝ)+1) := by
     unfold densityEpsilon
     apply one_div_le_one_div_of_le (by positivity)
     nlinarith
   have hScale : densityEpsilon r*((r : ℝ)+1)≤graphDensity G (realPart B) := by
     have :=(le_div_iff₀ (by positivity : 0<(r : ℝ)+1)).mp hEpsSmall
     linarith
   unfold perturbedModifiedDensity
   rw [hRelation,hReal,Nat.cast_sub (by omega : 1≤r),Nat.cast_one]
   have hDivide : densityEpsilon r≤graphDensity G (realPart B)/((r : ℝ)+1) :=
     (le_div_iff₀ (by positivity : 0<(r : ℝ)+1)).mpr hScale
   have hRewrite : (r : ℝ)/(r+1)*graphDensity G (realPart B)=
       graphDensity G (realPart B)-graphDensity G (realPart B)/((r : ℝ)+1) := by
     field_simp [hR.ne',hRp]
     ring
   rw [hRewrite]
   linarith
  ·have hSize : ((realPart B).erase x).card=r-1 := by
     rw [Finset.card_erase_of_mem hx,hReal]
   have hBound:=(augmentedDeletion_density_bounds G B
     (by rw [hReal];omega) z hz).2
   rw [hErase] at hBound
   unfold perturbedModifiedDensity
   rw [hErase,hSize]
   linarith

/-- The SAME two actual perturbed brackets rule out a positive integral
minimum in the exceptional beta-gap configuration. -/
theorem beta_gap_lower_density_zero {m d r : ℕ} (hr : 2≤r)
    (G : SimpleGraph (Fin m)) (B A : Finset (Fin (m+d))) (τ : ℝ)
    (hFull : B.card=r+1) (hBig : (realPart B).card=r+1)
    (hDummy : (B∩dummyLabels m d).card≤1) (hSmall : (realPart A).card=r)
    (hGap : graphDensity G (realPart B)-graphDensity G (realPart A)=densityRadius (r+1))
    (hBracketB : BracketsOneDeletion (fun S=>perturbedModifiedDensity G r (realPart S)) B τ)
    (hBracketA : BracketsOneDeletion (fun S=>perturbedModifiedDensity G r (realPart S)) A τ) :
    graphDensity G (realPart A)=0 := by
  obtain ⟨a,ha,haNonneg⟩:=density_lower_integer_of_beta_gap G (by omega)
    (realPart B) (realPart A) hBig hSmall hGap
  by_contra hNonzero
  have haNe : a≠0:=by intro h;apply hNonzero;simpa [h] using ha
  have haOne : 1≤a:=by omega
  have hPositive : 1≤graphDensity G (realPart A):=by rw [ha];exact_mod_cast haOne
  obtain ⟨⟨z,hz,hLow⟩,_⟩:=hBracketB
  obtain ⟨_,⟨y,hy,hHigh⟩⟩:=hBracketA
  change perturbedModifiedDensity G r (realPart (B.erase z))≤τ at hLow
  change τ≤perturbedModifiedDensity G r (realPart (A.erase y)) at hHigh
  have hCore:=large_real_deletion_size B hFull hBig hDummy z hz
  have hRaw:=(augmentedDeletion_density_bounds G B (by omega) z hz).1
  rw [hBig] at hRaw
  have hPerturbed : graphDensity G (realPart A)+densityEpsilon r*r≤τ := by
    unfold perturbedModifiedDensity at hLow
    rw [hCore.1] at hLow
    linarith
  have hSmallBound:=perturbed_small_deletion_le hr G A hSmall hPositive y hy
  have hEps:=densityEpsilon_pos (by omega : 0<r)
  rw [Nat.cast_sub (by omega : 1≤r),Nat.cast_one] at hSmallBound
  linarith

/-- The paper's whole bad-spread classification, on the literal real
restriction of the perturbed augmented allocation. -/
theorem single_remainder_bad_spread_is_star
    (k m r : ℕ) (hk : 2≤k) (hr : 2≤r) (hCount : m=k*r+1)
    (G : SimpleGraph (Fin m)) (B : Allocation k (m+(k-1))) (τ t : ℝ)
    (hB : ∀i : Fin k,
      (bundle B i).card=r+1 ∧
      (bundle B i∩dummyLabels m (k-1)).card≤1 ∧
      BracketsOneDeletion (fun S=>perturbedModifiedDensity G r (realPart S)) (bundle B i) τ ∧
      BracketsOneDeletion (fun S=>modifiedDensity G (realPart S)) (bundle B i) t)
    (hBad : ¬HasDensitySpread G (actualRealAllocation B) (densityRadius r)) :
    ∃j : Fin k,
      (bundle (actualRealAllocation B) j).card=r+1 ∧
      IsDensityStar G (bundle (actualRealAllocation B) j) ∧
      ∀i : Fin k,i≠j→
        (bundle (actualRealAllocation B) i).card=r ∧
        0≤graphDensity G (bundle (actualRealAllocation B) i) ∧
        graphDensity G (bundle (actualRealAllocation B) i)≤densityRadius r := by
  let A:=actualRealAllocation B
  have hPad : m+(k-1)=k*(r+1) := by
    simp only [Nat.mul_add,Nat.mul_one]
    omega
  have hBalanced : IsBalanced A:=actualRealAllocation_balanced hPad (by omega)
    (by omega) (by omega) B (fun i=>⟨(hB i).1,(hB i).2.1⟩)
  have hSizes : ∀i : Fin k,(bundle A i).card=r ∨(bundle A i).card=r+1 :=
    density_balanced_size_cases (by omega) (by omega : 1<k) hCount hBalanced
  have hWindows : ∀i : Fin k,
      t≤graphDensity G (bundle A i) ∧
      graphDensity G (bundle A i)≤t+densityRadius (bundle A i).card := by
    intro i
    have hPos : 0<(realPart (bundle B i)).card := by
      have hi:=hSizes i
      change (bundle (actualRealAllocation B) i).card=r ∨
        (bundle (actualRealAllocation B) i).card=r+1 at hi
      rw [bundle_actualRealAllocation] at hi
      omega
    simpa only [A,bundle_actualRealAllocation] using
      exactBrackets_density_window G (bundle B i) hPos t (hB i).2.2.2
  obtain ⟨j,i,hGapBad⟩ : ∃j i : Fin k,densityRadius r<
      graphDensity G (bundle A j)-graphDensity G (bundle A i) := by
    simpa only [HasDensitySpread,not_forall,not_le] using hBad
  have hLarge : (bundle A j).card=r+1 := by
    rcases hSizes j with hj|hj
    ·have hJ:=(hWindows j).2
     rw [hj] at hJ
     have hI:=(hWindows i).1
     linarith
    ·exact hj
  have hAlphaNonneg : 0≤densityRadius r := by
    unfold densityRadius
    have hR : (1 : ℝ)≤r:=by exact_mod_cast (show 1≤r by omega)
    positivity
  have hij : i≠j := by
    intro he
    subst i
    simp only [sub_self] at hGapBad
    linarith
  have hSmallAll:=density_single_large_part hk hCount hBalanced j hLarge
  have hSmall : (bundle A i).card=r:=hSmallAll i hij
  have hGapUpper : graphDensity G (bundle A j)-graphDensity G (bundle A i)≤
      densityRadius (r+1) := by
    have hJ:=(hWindows j).2
    rw [hLarge] at hJ
    linarith [(hWindows i).1]
  have hGap:=density_bad_gap_eq_beta G (by omega) (bundle A j) (bundle A i)
    hLarge hSmall hGapBad hGapUpper
  have hThreshold : t=graphDensity G (bundle A i) := by
    have hJ:=(hWindows j).2
    rw [hLarge] at hJ
    linarith [(hWindows i).1]
  have hLargeReal : (realPart (bundle B j)).card=r+1 := by
    simpa only [A,bundle_actualRealAllocation] using hLarge
  have hSmallReal : (realPart (bundle B i)).card=r := by
    simpa only [A,bundle_actualRealAllocation] using hSmall
  have hGapReal : graphDensity G (realPart (bundle B j))-
      graphDensity G (realPart (bundle B i))=densityRadius (r+1) := by
    simpa only [A,bundle_actualRealAllocation] using hGap
  have hZeroReal:=beta_gap_lower_density_zero hr G (bundle B j) (bundle B i) τ
    (hB j).1 hLargeReal (hB j).2.1 hSmallReal hGapReal
    (hB j).2.2.1 (hB i).2.2.1
  have hZero : graphDensity G (bundle A i)=0 := by
    simpa only [A,bundle_actualRealAllocation] using hZeroReal
  have htZero : t=0:=hThreshold.trans hZero
  have hBigDensity : graphDensity G (bundle A j)=densityRadius (r+1) := by
    linarith
  have hEdges : inducedEdges G (bundle A j)=r := by
    rw [graphDensity,hLarge,densityRadius_succ] at hBigDensity
    push_cast at hBigDensity
    have hCast : (inducedEdges G (bundle A j) : ℝ)=r := by
      exact (div_left_inj' (by positivity : (r : ℝ)+1≠0)).mp hBigDensity
    exact_mod_cast hCast
  obtain ⟨⟨z,hz,hLow⟩,_⟩:=(hB j).2.2.2
  have hCore:=large_real_deletion_size (bundle B j) (hB j).1 hLargeReal
    (hB j).2.1 z hz
  obtain ⟨c,hc,hErase⟩:=hCore.2
  have hDeleteZero : inducedEdges G ((realPart (bundle B j)).erase c)=0 := by
    change modifiedDensity G (realPart ((bundle B j).erase z))≤t at hLow
    rw [htZero] at hLow
    rw [hErase] at hLow
    have hRawZero : modifiedDensity G ((realPart (bundle B j)).erase c)=0 := by
      apply le_antisymm hLow
      unfold modifiedDensity
      positivity
    have hDen : (((realPart (bundle B j)).erase c).card : ℝ)+1≠0:=by positivity
    unfold modifiedDensity at hRawZero
    have hCast : (inducedEdges G ((realPart (bundle B j)).erase c) : ℝ)=0 := by
      simpa only [zero_mul] using (div_eq_iff hDen).mp hRawZero
    exact_mod_cast hCast
  have hEraseChoice :
      @Finset.erase (Fin m) (Classical.decEq (Fin m)) (realPart (bundle B j)) c=
        (realPart (bundle B j)).erase c:=by
    ext y
    simp only [Finset.mem_erase]
  refine ⟨j,hLarge,?_,?_⟩
  ·change IsDensityStar G (bundle A j)
   refine ⟨c,?_,?_,?_⟩
   ·simpa only [A,bundle_actualRealAllocation] using hc
   ·rw [hEdges,hLarge]
    omega
   ·simpa only [A,bundle_actualRealAllocation,hEraseChoice] using hDeleteZero
  ·intro l hlj
   refine ⟨hSmallAll l hlj,graphDensity_nonneg G _,?_⟩
   have hl:=(hWindows l).2
   rw [hSmallAll l hlj,htZero,zero_add] at hl
   exact hl

end FairDivision.BF.Applications
