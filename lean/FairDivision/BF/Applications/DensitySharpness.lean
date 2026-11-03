import FairDivision.BF.Applications.DensitySharpnessSizes

/-!
# The manuscript's three exact sharp density examples

Stars realize alpha; a clique with one isolate realizes beta when there are
at least two large parts; complete graphs realize beta when r=1. The graphs
are literal Mathlib simple graphs on Fin m. Every balanced allocation has a
pair attaining at least the asserted gap, and one balanced allocation attains
the corresponding upper bound. The argument is the manuscript's final three
sharpness paragraphs, with explicit complete-allocation bookkeeping.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Applications

open FairDivision
open scoped Classical

/-- A literal graph forcing radius b for every balanced partition, with a
balanced partition attaining b. Pairwise spread is the existing public one. -/
def IsSharpDensityExample {k m : ℕ} (G : SimpleGraph (Fin m)) (b : ℝ) : Prop :=
  (∀A : Allocation k m,IsBalanced A→∃i j : Fin k,
    b≤graphDensity G (bundle A i)-graphDensity G (bundle A j)) ∧
  ∃A : Allocation k m,IsBalanced A ∧ HasDensitySpread G A b

private theorem densityRadius_nonnegative {r : ℕ} (hr : 0<r) : 0≤densityRadius r := by
  have hrOne : (1:ℝ)≤r := by exact_mod_cast (Nat.succ_le_of_lt hr)
  exact div_nonneg (by linarith) (Nat.cast_nonneg _)

/-- The center's part is the only part with positive star density. -/
theorem star_every_balanced_lower {k m r s : ℕ} (hk : 2≤k) (hr : 0<r)
    (hs : s<k) (hCount : m=k*r+s) (z : Fin m) (A : Allocation k m) (hA : IsBalanced A) :
    ∃i j : Fin k,densityRadius r≤
      graphDensity (SimpleGraph.starGraph z) (bundle A i)-
        graphDensity (SimpleGraph.starGraph z) (bundle A j) := by
  obtain ⟨j,hj⟩:=density_exists_other_agent hk (A z)
  have hOwner:=distinguished_vertex_owner A z
  refine ⟨A z,j,?_⟩
  rw [graphDensity_star_of_mem z _ hOwner.1,
    graphDensity_star_of_not_mem z _ (hOwner.2 j hj),sub_zero]
  apply densityRadius_mono hr
  rcases density_balanced_size_cases (by omega) hs hCount hA (A z) with hi|hi <;> omega

/-- Putting the center in an r-part gives the paper's attaining partition. -/
theorem star_spread_of_center_small {k m r : ℕ} (hr : 0<r)
    (z : Fin m) (A : Allocation k m) (hCenter : (bundle A (A z)).card=r) :
    HasDensitySpread (SimpleGraph.starGraph z) A (densityRadius r) := by
  have hAll : ∀i : Fin k,graphDensity (SimpleGraph.starGraph z) (bundle A i)≤densityRadius r := by
    intro i
    by_cases hi : i=A z
    · subst i
      rw [graphDensity_star_of_mem z _ (distinguished_vertex_owner A z).1,hCenter]
    · rw [graphDensity_star_of_not_mem z _ ((distinguished_vertex_owner A z).2 i hi)]
      exact densityRadius_nonnegative hr
  intro i j
  have hj:=graphDensity_nonneg (SimpleGraph.starGraph z) (bundle A j)
  linarith [hAll i]

/-- The star example attains alpha at every order with an r-part. The public
sharpness theorem uses it precisely in the manuscript's alpha regimes. -/
theorem exists_star_sharpness (k m r s : ℕ) (hk : 2≤k) (hr : 0<r)
    (hs : s<k) (hCount : m=k*r+s) :
    ∃z : Fin m,IsSharpDensityExample (k:=k) (SimpleGraph.starGraph z) (densityRadius r) := by
  obtain ⟨A,hA⟩:=exists_balanced_allocation k m (by omega)
  obtain ⟨i,hi⟩:=density_exists_small_part (by omega) hs hCount hA
  obtain ⟨z,hz⟩:=Finset.card_pos.mp (by simpa only [hi] using hr : 0<(bundle A i).card)
  have hOwner : A z=i := by simpa [bundle] using hz
  refine ⟨z,fun B hB=>star_every_balanced_lower hk hr hs hCount z B hB,A,hA,?_⟩
  exact star_spread_of_center_small hr z A (by simpa only [hOwner] using hi)

private theorem clique_isolate_large_gap (r : ℕ) (hr : 0<r) :
    (r:ℝ)/2-((r:ℝ)*((r:ℝ)-1))/(2*((r:ℝ)+1))=densityRadius (r+1) := by
  unfold densityRadius
  push_cast
  have hrOne : (r:ℝ)+1≠0 := by positivity
  field_simp [hrOne]
  ring

private theorem clique_isolate_small_gap (r : ℕ) (hr : 2≤r) :
    densityRadius (r+1)≤(r:ℝ)/2-(((r:ℝ)-1)*((r:ℝ)-2))/(2*r) := by
  have hrR : (2:ℝ)≤r := by exact_mod_cast hr
  have hDiff : (r:ℝ)/2-(((r:ℝ)-1)*((r:ℝ)-2))/(2*r)=
      (3*(r:ℝ)-2)/(2*r) := by
    have hrNe : (r:ℝ)≠0 := by linarith
    field_simp [hrNe]
    ring
  rw [hDiff]
  unfold densityRadius
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (r:ℝ)]

/-- With at least two large parts, a large clique part remains away from the
isolate's owner. The two possible isolate-part sizes give the paper's gaps. -/
theorem cliqueWithIsolate_every_balanced_lower {k m r s : ℕ}
    (hk : 2≤k) (hr : 2≤r) (hs : 2 ≤ s) (hsk : s<k) (hCount : m=k*r+s)
    (z : Fin m) (A : Allocation k m) (hA : IsBalanced A) :
    ∃i j : Fin k,densityRadius (r+1)≤
      graphDensity (cliqueWithIsolate z) (bundle A i)-
        graphDensity (cliqueWithIsolate z) (bundle A j) := by
  obtain ⟨j,hj,hLarge⟩:=density_exists_other_large_part (by omega) hs hsk hCount hA (A z)
  have hOwner:=distinguished_vertex_owner A z
  have hClique : graphDensity (cliqueWithIsolate z) (bundle A j)=(r:ℝ)/2 := by
    rw [graphDensity_cliqueWithIsolate_of_not_mem z _ (hOwner.2 j hj) (by omega),hLarge]
    push_cast
    ring
  refine ⟨j,A z,?_⟩
  rcases density_balanced_size_cases (by omega) hsk hCount hA (A z) with hSmall|hBig
  · rw [hClique,graphDensity_cliqueWithIsolate_of_mem z _ hOwner.1 (by omega),hSmall]
    exact clique_isolate_small_gap r hr
  · rw [hClique,graphDensity_cliqueWithIsolate_of_mem z _ hOwner.1 (by omega),hBig]
    push_cast
    have hNum : ((r:ℝ)+1-1)*((r:ℝ)+1-2)=(r:ℝ)*((r:ℝ)-1) := by ring
    rw [hNum]
    exact le_of_eq (clique_isolate_large_gap r (by omega)).symm

/-- If the isolate lies in a large part, all densities are in the paper's
explicit interval [r(r−1)/(2(r+1)),r/2], whose width is beta. -/
theorem cliqueWithIsolate_spread_of_isolate_large {k m r s : ℕ}
    (hk : 0<k) (hr : 2≤r) (hs : s<k) (hCount : m=k*r+s)
    (z : Fin m) (A : Allocation k m) (hA : IsBalanced A)
    (hOwnerSize : (bundle A (A z)).card=r+1) :
    HasDensitySpread (cliqueWithIsolate z) A (densityRadius (r+1)) := by
  let low : ℝ:=(r:ℝ)*((r:ℝ)-1)/(2*((r:ℝ)+1))
  have hrR : (2:ℝ)≤r := by exact_mod_cast hr
  have hLowSmall : low≤((r:ℝ)-1)/2 := by
    dsimp [low]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*((r:ℝ)+1))).mpr
    nlinarith
  have hLowHigh : low≤(r:ℝ)/2 := by linarith
  have hAll : ∀i : Fin k,low≤graphDensity (cliqueWithIsolate z) (bundle A i) ∧
      graphDensity (cliqueWithIsolate z) (bundle A i)≤(r:ℝ)/2 := by
    intro i
    by_cases hi : i=A z
    · subst i
      rw [graphDensity_cliqueWithIsolate_of_mem z _ (distinguished_vertex_owner A z).1
        (by omega),hOwnerSize]
      push_cast
      have hNum : ((r:ℝ)+1-1)*((r:ℝ)+1-2)=(r:ℝ)*((r:ℝ)-1) := by ring
      rw [hNum]
      change low≤low ∧ low≤(r:ℝ)/2
      exact ⟨le_rfl,hLowHigh⟩
    · rw [graphDensity_cliqueWithIsolate_of_not_mem z _
        ((distinguished_vertex_owner A z).2 i hi) (by
          rcases density_balanced_size_cases hk hs hCount hA i with hi|hi <;> omega)]
      rcases density_balanced_size_cases hk hs hCount hA i with hSmall|hLarge
      · rw [hSmall]
        exact ⟨hLowSmall,by linarith⟩
      · rw [hLarge]
        push_cast
        simp only [add_sub_cancel_right]
        exact ⟨hLowHigh,le_rfl⟩
  intro i j
  have hGap : (r:ℝ)/2-low=densityRadius (r+1):=clique_isolate_large_gap r (by omega)
  linarith [(hAll i).2,(hAll j).1]

/-- The clique-plus-isolate graph, with an attaining balanced partition
having its isolate in a large part, is exactly the manuscript example. -/
theorem exists_cliqueIsolate_sharpness (k m r s : ℕ)
    (hk : 2≤k) (hr : 2≤r) (hs : 2 ≤ s) (hsk : s<k) (hCount : m=k*r+s) :
    ∃z : Fin m,IsSharpDensityExample (k:=k) (cliqueWithIsolate z) (densityRadius (r+1)) := by
  obtain ⟨A,hA⟩:=exists_balanced_allocation k m (by omega)
  obtain ⟨i,hi⟩:=density_exists_large_part (by omega) (by omega) hsk hCount hA
  obtain ⟨z,hz⟩:=Finset.card_pos.mp (by rw [hi];omega : 0<(bundle A i).card)
  have hOwner : A z=i := by simpa [bundle] using hz
  refine ⟨z,fun B hB=>cliqueWithIsolate_every_balanced_lower hk hr hs hsk hCount z B hB,
    A,hA,?_⟩
  exact cliqueWithIsolate_spread_of_isolate_large (by omega) hr hsk hCount z A hA
    (by simpa only [hOwner] using hi)

/-- For r=1 and 0<s<k, both singleton and pair parts occur. Complete graphs
therefore force the exact density gap 1/2 in every balanced partition. -/
theorem complete_every_balanced_lower {k m s : ℕ} (hk : 2≤k) (hs : 0<s) (hsk : s<k)
    (hCount : m=k*1+s) (A : Allocation k m) (hA : IsBalanced A) :
    ∃i j : Fin k,densityRadius 2≤graphDensity (⊤ : SimpleGraph (Fin m)) (bundle A i)-
      graphDensity (⊤ : SimpleGraph (Fin m)) (bundle A j) := by
  obtain ⟨i,hi⟩:=density_exists_large_part (by omega) hs hsk hCount hA
  obtain ⟨j,hj⟩:=density_exists_small_part (by omega) hsk hCount hA
  refine ⟨i,j,?_⟩
  rw [graphDensity_complete _ (by omega),graphDensity_complete _ (by omega),hi,hj]
  norm_num [densityRadius]

theorem complete_spread_r_one {k m s : ℕ} (hk : 0<k) (hsk : s<k)
    (hCount : m=k*1+s) (A : Allocation k m) (hA : IsBalanced A) :
    HasDensitySpread (⊤ : SimpleGraph (Fin m)) A (densityRadius 2) := by
  have hUpper : ∀i : Fin k,graphDensity (⊤ : SimpleGraph (Fin m)) (bundle A i)≤1/2 := by
    intro i
    rcases density_balanced_size_cases hk hsk hCount hA i with hi|hi <;>
      rw [graphDensity_complete _ (by omega),hi] <;> norm_num
  intro i j
  have hNonneg:=graphDensity_nonneg (⊤ : SimpleGraph (Fin m)) (bundle A j)
  norm_num [densityRadius]
  linarith [hUpper i]

theorem complete_sharpness (k m s : ℕ) (hk : 2≤k) (hs : 0<s) (hsk : s<k)
    (hCount : m=k*1+s) :
    IsSharpDensityExample (k:=k) (⊤ : SimpleGraph (Fin m)) (densityRadius 2) := by
  refine ⟨fun A hA=>complete_every_balanced_lower hk hs hsk hCount A hA,?_⟩
  obtain ⟨A,hA⟩:=exists_balanced_allocation k m (by omega)
  exact ⟨A,hA,complete_spread_r_one (by omega) hsk hCount A hA⟩

/-- Every fixed order and part count has a literal sharp graph, with the
same three cases and the same radius as the manuscript theorem. -/
theorem exists_sharp_density_example (k m r s : ℕ) (hk : 2≤k) (hr : 0<r)
    (hs : s<k) (hCount : m=k*r+s) :
    ∃G : SimpleGraph (Fin m),IsSharpDensityExample (k:=k) G
      (if s=0 ∨ s=1 ∧ 2≤r then densityRadius r else densityRadius (r+1)) := by
  by_cases hAlpha : s=0 ∨ s=1 ∧ 2≤r
  · obtain ⟨z,hz⟩:=exists_star_sharpness k m r s hk hr hs hCount
    exact ⟨SimpleGraph.starGraph z,by simpa only [if_pos hAlpha] using hz⟩
  · by_cases hrOne : r=1
    · subst r
      have hsPos : 0<s := by omega
      exact ⟨⊤,by simpa only [if_neg hAlpha] using complete_sharpness k m s hk hsPos hs hCount⟩
    · have hrTwo : 2≤r := by omega
      have hsTwo : 2 ≤ s := by omega
      obtain ⟨z,hz⟩:=exists_cliqueIsolate_sharpness k m r s hk hrTwo hsTwo hs hCount
      exact ⟨cliqueWithIsolate z,by simpa only [if_neg hAlpha] using hz⟩

/-- An attained lower witness excludes every smaller proposed universal
bound, which is the precise 'best possible for fixed N,k' conclusion. -/
theorem IsSharpDensityExample.no_smaller_bound {k m : ℕ}
    {G : SimpleGraph (Fin m)} {b c : ℝ} (h : IsSharpDensityExample (k:=k) G b) (hc : c<b) :
    ∀A : Allocation k m,IsBalanced A→¬HasDensitySpread G A c := by
  intro A hA hSpread
  obtain ⟨i,j,hLower⟩:=h.1 A hA
  exact (not_le_of_gt hc) (hLower.trans (hSpread i j))

end FairDivision.BF.Applications
