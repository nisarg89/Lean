import FairDivision.BF.Recording.RootPool

/-!
# The root pool after imposing the actual dummy labels

The recording graph remembers only dummy counts. The manuscript's final
midpoint uses every real item and a d-item formal prefix. Its actual reserve
relabeling has image exactly the entire augmented inventory, including when
d=0. This equality is stronger than the support inclusion needed to recover
the equitable lottery and makes the full-pool realization explicit.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Recording

open FairDivision.Topology
open scoped BigOperators Classical

/-- On its used stock, the reserve relabeling exhausts exactly the chosen
real stock and actual reserve. Only the used prefix must be injective. -/
theorem reserveRelabel_stock_image {m a A:ℕ} (hInventory:0< m+A)
    (E:Finset (Fin m)) (R:Finset (Fin (m+A)))
    (hReserve:R.card≤a) (hDummy:R⊆dummyLabels m A):
    (reserveSourceStock (a:=a) E R).image (reserveRelabel hInventory R)=
      E.map (realEmbedding m A)∪R:=by
  have hSubset:(reserveSourceStock (a:=a) E R).image (reserveRelabel hInventory R)⊆
      E.map (realEmbedding m A)∪R:=by
    intro z hz
    obtain ⟨g,hg,rfl⟩:=Finset.mem_image.mp hz
    exact reserveRelabel_maps_stock hInventory E R hg
  have hSource:Disjoint (E.map (realEmbedding m a)) (initialDummies m a R.card):=
    (realImage_disjoint_dummies E).mono_right (initialDummies_subset m a R.card)
  have hTarget:Disjoint (E.map (realEmbedding m A)) R:=
    (realImage_disjoint_dummies E).mono_right hDummy
  have hSourceCard:(reserveSourceStock (a:=a) E R).card=E.card+R.card:=by
    rw [reserveSourceStock,Finset.card_union_of_disjoint hSource,
      Finset.card_map,card_initialDummies m a R.card hReserve]
  have hTargetCard:(E.map (realEmbedding m A)∪R).card=E.card+R.card:=by
    rw [Finset.card_union_of_disjoint hTarget,Finset.card_map]
  apply Finset.eq_of_subset_of_card_le hSubset
  simpa only [Finset.card_image_of_injOn
    (reserveRelabel_injectiveOn_stock hInventory E R hDummy),hSourceCard,hTargetCard]
    using (le_refl (E.card+R.card))

/-- The actual real prefix and actual dummy suffix partition the finite
augmented inventory. No arbitrary enumeration of real items is used. -/
theorem actualRootInventory_union (m d:ℕ):
    (Finset.univ:Finset (Fin m)).map (realEmbedding m d)∪dummyLabels m d=Finset.univ:=by
  ext z
  constructor
  · intro _
    exact Finset.mem_univ _
  · intro _
    by_cases hReal:z.val< m
    · let g:Fin m:=⟨z.val,hReal⟩
      refine Finset.mem_union_left _ (Finset.mem_map.mpr ⟨g,Finset.mem_univ _,?_⟩)
      exact Fin.ext rfl
    · exact Finset.mem_union_right _ ((mem_dummyLabels_iff z).mpr (by omega))

/-- The literal midpoint's available pool becomes EXACTLY M union D after
its unused formal labels are discarded and its used prefix is relabeled. -/
theorem rootMidpoint_actual_pool {n q m d:ℕ}
    (hd:d<n) (hCount:m+d=n*q) (hInventory:0< m+d)
    (x y:Fin m) (hxy:x≠y):
    (available (rootMidpoint hd hCount x y hxy)).image
      (reserveRelabel (a:=n) hInventory (dummyLabels m d))=Finset.univ:=by
  have hReserve:(dummyLabels m d).card≤n:=by rw [card_dummyLabels];omega
  have hImage:=reserveRelabel_stock_image (a:=n) hInventory
    (Finset.univ:Finset (Fin m)) (dummyLabels m d) hReserve Finset.Subset.rfl
  rw [actualRootInventory_union] at hImage
  simpa only [rootMidpoint_available,reserveSourceStock,card_dummyLabels] using hImage

/-- Combine exact full-inventory realization with the recorder's actual
lottery certificate, before applying integral conversion once. -/
theorem rootMidpoint_certifies_actual_spec {n q m d:ℕ}
    (hd:d<n) (hCount:m+d=n*q) (hInventory:0< m+d)
    (x y:Fin m) (hxy:x≠y)
    {v:Finset (Fin m)→ℝ} {t:ℝ}
    (h:Certifies v (rootMidpoint hd hCount x y hxy) t):
    ((available (rootMidpoint hd hCount x y hxy)).image
      (reserveRelabel (a:=n) hInventory (dummyLabels m d))=Finset.univ) ∧
    ∃μ:stdSimplex ℝ (PartialVertex n (dummyLabels m d) (q-1) 1),
      μ∈compatibleLotterySpace n (m+d) (q-1) 1 (dummyLabels m d) ∧
      ∀i:Fin n,(∑X:PartialVertex n (dummyLabels m d) (q-1) 1,
        μ.1 X*v (realPart (partialBundle X.1 i)))=t:=
  ⟨rootMidpoint_actual_pool hd hCount hInventory x y hxy,
    rootMidpoint_certifies_actual hd hCount hInventory x y hxy h⟩

end FairDivision.BF.Recording
