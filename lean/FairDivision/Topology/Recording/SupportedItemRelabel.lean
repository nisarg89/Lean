import FairDivision.Finite.BundlesToAllocation
import FairDivision.Topology.FiniteSimplexSupportMap

/-!
# Relabel only the items actually available to a compatible lottery

The recording graph uses canonical dummy prefixes. At a zero, its finite
available pool may instead be given arbitrary actual labels. The item map
need be injective ONLY on that pool; unused formal dummy labels need not
have images in the actual dummy stock. Positive-support outcomes are mapped
bundle by bundle, and all unsupported outcomes receive one fixed supported
fallback. Their probability is zero, so this introduces no extra outcome,
changes no average, and uses no unavailable item.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace FairDivision.Topology.Recording

open FairDivision.Finite

/-- Exact compatible-lottery transport under an injective relabeling of
its actual available stock. The valuation clause expresses the literal
renaming of the same real bundle, not a new fairness assumption. -/
theorem exists_supported_item_relabel
    {k M N r c:ℕ} {D:Finset (Fin M)} {D':Finset (Fin N)}
    (μ:stdSimplex ℝ (PartialVertex k D r c))
    (hCompatible:μ∈compatibleLotterySpace k M r c D)
    (E:Finset (Fin M))
    (hPool:∀i:Fin k,pool (lotterySupport μ) i⊆E)
    (e:Fin M→Fin N) (hInject:Set.InjOn e (E:Set (Fin M)))
    (hDummy:∀g∈E,e g∈D'↔g∈D)
    (v:Finset (Fin M)→ℝ) (w:Finset (Fin N)→ℝ)
    (hValue:∀X∈lotterySupport μ,∀i:Fin k,
      w ((partialBundle X.1 i).image e)=v (partialBundle X.1 i)):
    ∃ν:stdSimplex ℝ (PartialVertex k D' r c),
      ν∈compatibleLotterySpace k N r c D' ∧
      (∀i:Fin k,pool (lotterySupport ν) i⊆E.image e) ∧
      ∀i:Fin k,
        (∑Y:PartialVertex k D' r c,ν.1 Y*w (partialBundle Y.1 i))=
        ∑X:PartialVertex k D r c,μ.1 X*v (partialBundle X.1 i):=by
  classical
  let S:=lotterySupport μ
  obtain ⟨X₀,hX₀⟩:=lotterySupport_nonempty μ
  have hBundleE:∀X∈S,∀i:Fin k,partialBundle X.1 i⊆E:=by
    intro X hX i
    exact (partialBundle_subset_pool hX i).trans (hPool i)
  have hImageDummy:∀Q:Finset (Fin M),Q⊆E→
      Q.image e∩D'=(Q∩D).image e:=by
    intro Q hQE
    ext z
    constructor
    ·intro hz
     obtain ⟨hzQ,hzD⟩:=Finset.mem_inter.mp hz
     obtain ⟨g,hg,rfl⟩:=Finset.mem_image.mp hzQ
     exact Finset.mem_image.mpr ⟨g,Finset.mem_inter.mpr
       ⟨hg,(hDummy g (hQE hg)).mp hzD⟩,rfl⟩
    ·intro hz
     obtain ⟨g,hg,rfl⟩:=Finset.mem_image.mp hz
     exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr
       ⟨g,(Finset.mem_inter.mp hg).1,rfl⟩,
       (hDummy g (hQE (Finset.mem_inter.mp hg).1)).mpr (Finset.mem_inter.mp hg).2⟩
  have hCross:∀X∈S,∀Y∈S,∀i j:Fin k,i≠j→
      Disjoint ((partialBundle X.1 i).image e) ((partialBundle Y.1 j).image e):=by
    intro X hX Y hY i j hij
    apply Finset.disjoint_left.mpr
    intro z hzX hzY
    obtain ⟨g,hg,he⟩:=Finset.mem_image.mp hzX
    obtain ⟨h,hh,he'⟩:=Finset.mem_image.mp hzY
    have hgh:g=h:=hInject (hBundleE X hX i hg) (hBundleE Y hY j hh) (he.trans he'.symm)
    subst h
    exact (Finset.disjoint_left.mp (hCompatible.1 i j hij))
      (partialBundle_subset_pool hX i hg) (partialBundle_subset_pool hY j hh)
  let mapSupported:(X:PartialVertex k D r c)→X∈S→PartialVertex k D' r c:=
    fun X hX=>⟨partialAllocationFromBundles
      (fun i:Fin k=>(partialBundle X.1 i).image e),by
        intro i
        rw [partialBundle_fromBundles _ (hCross X hX X hX)]
        constructor
        ·rw [Finset.card_image_of_injOn (hInject.mono (hBundleE X hX i))]
         exact (X.2 i).1
        ·rw [hImageDummy _ (hBundleE X hX i)]
         exact Finset.card_image_le.trans (X.2 i).2⟩
  have hMappedBundle:∀X (hX:X∈S) (i:Fin k),
      partialBundle (mapSupported X hX).1 i=(partialBundle X.1 i).image e:=by
    intro X hX i
    exact partialBundle_fromBundles _ (hCross X hX X hX) i
  let f:PartialVertex k D r c→PartialVertex k D' r c:=fun X=>
    if hX:X∈S then mapSupported X hX else mapSupported X₀ hX₀
  have hFBundles:∀X∈S,∀i:Fin k,
      partialBundle (f X).1 i=(partialBundle X.1 i).image e:=by
    intro X hX i
    simp only [f,dif_pos hX]
    exact hMappedBundle X hX i
  let ν:=stdSimplex.map f μ
  have hTargetPool:∀i:Fin k,pool (lotterySupport ν) i⊆(pool S i).image e:=by
    intro i z hz
    obtain ⟨_,Y,hY,hYz⟩:=Finset.mem_filter.mp hz
    obtain ⟨X,hX,hXY⟩:=Finset.mem_image.mp
      (finiteSimplexSupport_map_subset f μ hY)
    have hzB:z∈partialBundle Y.1 i:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hYz⟩
    rw [←hXY,hFBundles X hX i] at hzB
    obtain ⟨g,hg,rfl⟩:=Finset.mem_image.mp hzB
    exact Finset.mem_image.mpr ⟨g,partialBundle_subset_pool hX i hg,rfl⟩
  have hTargetCompatible:ν∈compatibleLotterySpace k N r c D':=by
    constructor
    ·intro i j hij
     apply Finset.disjoint_left.mpr
     intro z hzI hzJ
     obtain ⟨g,hg,he⟩:=Finset.mem_image.mp (hTargetPool i hzI)
     obtain ⟨h,hh,he'⟩:=Finset.mem_image.mp (hTargetPool j hzJ)
     have hgh:g=h:=hInject (hPool i hg) (hPool j hh) (he.trans he'.symm)
     subst h
     exact (Finset.disjoint_left.mp (hCompatible.1 i j hij)) hg hh
    ·intro i
     have hSub:pool (lotterySupport ν) i∩D'⊆(pool S i).image e∩D':=
       Finset.inter_subset_inter (hTargetPool i) Finset.Subset.rfl
     calc
       (pool (lotterySupport ν) i∩D').card≤((pool S i).image e∩D').card:=Finset.card_le_card hSub
       _=((pool S i∩D).image e).card:=by rw [hImageDummy _ (hPool i)]
       _≤(pool S i∩D).card:=Finset.card_image_le
       _≤c:=hCompatible.2 i
  refine ⟨ν,hTargetCompatible,?_,?_⟩
  ·intro i
   exact (hTargetPool i).trans (Finset.image_subset_image (hPool i))
  ·intro i
   have hPush:(∑Y:PartialVertex k D' r c,ν.1 Y*w (partialBundle Y.1 i))=
       ∑X:PartialVertex k D r c,μ.1 X*w (partialBundle (f X).1 i):=by
     change (∑Y:PartialVertex k D' r c,
       FunOnFinite.linearMap ℝ ℝ f μ.1 Y*w (partialBundle Y.1 i))=_
     simp_rw [FunOnFinite.linearMap_apply_apply]
     calc
       (∑Y:PartialVertex k D' r c,(∑X with f X=Y,μ.1 X)*w (partialBundle Y.1 i))=
         ∑Y:PartialVertex k D' r c,∑X with f X=Y,μ.1 X*w (partialBundle (f X).1 i):=by
           apply Finset.sum_congr rfl
           intro Y hY
           rw [Finset.sum_mul]
           apply Finset.sum_congr rfl
           intro X hX
           rw [(Finset.mem_filter.mp hX).2]
       _=∑X:PartialVertex k D r c,μ.1 X*w (partialBundle (f X).1 i):=
         Finset.sum_fiberwise Finset.univ f _
   rw [hPush]
   apply Finset.sum_congr rfl
   intro X hX
   by_cases hXS:X∈S
   ·rw [hFBundles X hXS i,hValue X hXS i]
   ·have hZero:μ.1 X=0:=by
      have hNot:¬0<μ.1 X:=fun h=>hXS (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      exact le_antisymm (le_of_not_gt hNot) (μ.2.1 X)
    simp only [hZero,zero_mul]

end FairDivision.Topology.Recording
