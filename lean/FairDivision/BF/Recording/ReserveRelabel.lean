import FairDivision.BF.Recording.ZeroInPool
import FairDivision.BF.Recording.RealItemCoordinates
import FairDivision.Finite.OrderedPrefix

/-!
# Relabel the ACTUALLY used child dummy prefix into its outer reserve

Real items keep their original identities. The first |R| child dummy labels
are mapped, in their fixed order, to the actual reserve R. Unused formal
labels take an irrelevant fallback value. All injectivity, valuation, and
stock proofs are confined to the used prefix, exactly as required by the
manuscript's realization down the recursion tree.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace FairDivision.BF.Recording

open FairDivision.Topology

/-- Existing canonical order embedding of a finite reserve. -/
def reserveEmbedding {N:ℕ} (R:Finset (Fin N)):Fin R.card↪oFin N:=
  R.orderEmbOfCardLe le_rfl

theorem reserveEmbedding_mem {N:ℕ} (R:Finset (Fin N)) (j:Fin R.card):
    reserveEmbedding R j∈R:=Finset.orderEmbOfCardLe_mem R le_rfl j

/-- Identity on real labels and the existing ordered reserve embedding on
used dummy labels. The final branch is never used by a supported outcome. -/
def reserveRelabel {m a A:ℕ} (hA:0< m+A) (R:Finset (Fin (m+A))):
    Fin (m+a)→Fin (m+A):=fun z=>
  if hReal:z.val< m then realEmbedding m A ⟨z.val,hReal⟩
  else if hReserve:z.val-m<R.card then reserveEmbedding R ⟨z.val-m,hReserve⟩
  else ⟨0,hA⟩

@[simp] theorem reserveRelabel_real {m a A:ℕ} (hA:0< m+A)
    (R:Finset (Fin (m+A))) (g:Fin m):
    reserveRelabel (a:=a) hA R (realEmbedding m a g)=realEmbedding m A g:=by
  simp only [reserveRelabel,show (realEmbedding m a g).val< m from g.isLt,dif_pos]
  apply congrArg (realEmbedding m A)
  exact Fin.ext rfl

@[simp] theorem reserveRelabel_dummy {m a A:ℕ} (hA:0< m+A)
    (R:Finset (Fin (m+A))) (δ:Fin a) (hδ:δ.val<R.card):
    reserveRelabel hA R (Fin.natAdd m δ)=reserveEmbedding R ⟨δ.val,hδ⟩:=by
  have hNot:¬(Fin.natAdd m δ).val< m:=by change ¬m+δ.val< m;omega
  have hIndex:(Fin.natAdd m δ).val-m=δ.val:=by change m+δ.val-m=δ.val;omega
  simp only [reserveRelabel,dif_neg hNot,hIndex,dif_pos hδ]

/-- All used source labels are either real or in the prefix paid for by R. -/
def reserveSourceStock {m a A:ℕ} (E:Finset (Fin m)) (R:Finset (Fin (m+A))):
    Finset (Fin (m+a)):=E.map (realEmbedding m a)∪initialDummies m a R.card

/-- An empty actual reserve removes every formal dummy from the used
source stock; the ambient type still need not be changed. -/
@[simp] theorem reserveSourceStock_empty {m a A:ℕ} (E:Finset (Fin m)):
    reserveSourceStock (a:=a) E (∅:Finset (Fin (m+A)))=
      E.map (realEmbedding m a):=by
  simp only [reserveSourceStock,Finset.card_empty,initialDummies_zero,Finset.union_empty]

theorem reserveRelabel_maps_stock {m a A:ℕ} (hA:0< m+A)
    (E:Finset (Fin m)) (R:Finset (Fin (m+A))):
    Set.MapsTo (reserveRelabel (a:=a) hA R)
      (reserveSourceStock (a:=a) E R : Set (Fin (m+a)))
      (↑(E.map (realEmbedding m A)∪R) : Set (Fin (m+A))):=by
  intro z hz
  rcases Finset.mem_union.mp hz with hReal|hDummy
  ·obtain ⟨g,hg,rfl⟩:=Finset.mem_map.mp hReal
   rw [reserveRelabel_real]
   exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨g,hg,rfl⟩)
  ·obtain ⟨δ,hδ,rfl⟩:=Finset.mem_map.mp hDummy
   have hδR:δ.val<R.card:=(Finset.mem_filter.mp hδ).2
   change reserveRelabel hA R (Fin.natAdd m δ)∈E.map (realEmbedding m A)∪R
   rw [reserveRelabel_dummy hA R δ hδR]
   exact Finset.mem_union_right _ (reserveEmbedding_mem R _)

theorem reserveRelabel_injectiveOn_stock {m a A:ℕ} (hA:0< m+A)
    (E:Finset (Fin m)) (R:Finset (Fin (m+A))) (hR:R⊆dummyLabels m A):
    Set.InjOn (reserveRelabel (a:=a) hA R)
      (reserveSourceStock (a:=a) E R : Set (Fin (m+a))):=by
  intro z hz w hw he
  rcases Finset.mem_union.mp hz with hz|hz <;>rcases Finset.mem_union.mp hw with hw|hw
  ·obtain ⟨g,hg,rfl⟩:=Finset.mem_map.mp hz
   obtain ⟨h,hh,rfl⟩:=Finset.mem_map.mp hw
   rw [reserveRelabel_real,reserveRelabel_real] at he
   exact congrArg (realEmbedding m a) ((realEmbedding m A).injective he)
  ·obtain ⟨g,hg,rfl⟩:=Finset.mem_map.mp hz
   obtain ⟨δ,hδ,rfl⟩:=Finset.mem_map.mp hw
   change reserveRelabel hA R (realEmbedding m a g)=
     reserveRelabel hA R (Fin.natAdd m δ) at he
   rw [reserveRelabel_real,reserveRelabel_dummy hA R δ (Finset.mem_filter.mp hδ).2] at he
   have hD:realEmbedding m A g∈dummyLabels m A:=he.symm▸hR (reserveEmbedding_mem R _)
   exact False.elim ((not_le_of_gt g.isLt) ((mem_dummyLabels_iff _).mp hD))
  ·obtain ⟨δ,hδ,rfl⟩:=Finset.mem_map.mp hz
   obtain ⟨g,hg,rfl⟩:=Finset.mem_map.mp hw
   change reserveRelabel hA R (Fin.natAdd m δ)=
     reserveRelabel hA R (realEmbedding m a g) at he
   rw [reserveRelabel_dummy hA R δ (Finset.mem_filter.mp hδ).2,reserveRelabel_real] at he
   have hD:realEmbedding m A g∈dummyLabels m A:=he▸hR (reserveEmbedding_mem R _)
   exact False.elim ((not_le_of_gt g.isLt) ((mem_dummyLabels_iff _).mp hD))
  ·obtain ⟨δ,hδ,rfl⟩:=Finset.mem_map.mp hz
   obtain ⟨ε,hε,rfl⟩:=Finset.mem_map.mp hw
   change reserveRelabel hA R (Fin.natAdd m δ)=
     reserveRelabel hA R (Fin.natAdd m ε) at he
   rw [reserveRelabel_dummy hA R δ (Finset.mem_filter.mp hδ).2,
     reserveRelabel_dummy hA R ε (Finset.mem_filter.mp hε).2] at he
   have hVal:δ.val=ε.val:=
     congrArg (fun j:Fin R.card=>j.val) ((reserveEmbedding R).injective he)
   exact congrArg (Fin.natAdd m) (Fin.ext hVal)

theorem reserveRelabel_dummy_iff_on_stock {m a A:ℕ} (hA:0< m+A)
    (E:Finset (Fin m)) (R:Finset (Fin (m+A))) (hR:R⊆dummyLabels m A)
    (z:Fin (m+a)) (hz:z∈reserveSourceStock E R):
    reserveRelabel hA R z∈dummyLabels m A↔z∈dummyLabels m a:=by
  rcases Finset.mem_union.mp hz with hz|hz
  ·obtain ⟨g,hg,rfl⟩:=Finset.mem_map.mp hz
   rw [reserveRelabel_real,mem_dummyLabels_iff,mem_dummyLabels_iff]
   change m≤g.val↔m≤g.val
   rfl
  ·obtain ⟨δ,hδ,rfl⟩:=Finset.mem_map.mp hz
   change reserveRelabel hA R (Fin.natAdd m δ)∈dummyLabels m A↔
     Fin.natAdd m δ∈dummyLabels m a
   rw [reserveRelabel_dummy hA R δ (Finset.mem_filter.mp hδ).2]
   exact iff_of_true (hR (reserveEmbedding_mem R _))
     ((mem_dummyLabels_iff _).mpr (by change m≤ m+δ.val;omega))

/-- Changing the dummy labels preserves the original real bundle EXACTLY. -/
theorem reserveRelabel_realPart {m a A:ℕ} (hA:0< m+A)
    (E:Finset (Fin m)) (R:Finset (Fin (m+A))) (hR:R⊆dummyLabels m A)
    (B:Finset (Fin (m+a))) (hB:B⊆reserveSourceStock E R):
    realPart (B.image (reserveRelabel hA R))=realPart B:=by
  classical
  ext g
  simp only [realPart,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  ·intro hg
   obtain ⟨z,hz,he⟩:=Finset.mem_image.mp hg
   rcases Finset.mem_union.mp (hB hz) with hzReal|hzDummy
   ·obtain ⟨h,hh,rfl⟩:=Finset.mem_map.mp hzReal
    rw [reserveRelabel_real] at he
    have hEq:h=g:=(realEmbedding m A).injective he
    exact hEq▸hz
   ·obtain ⟨δ,hδ,rfl⟩:=Finset.mem_map.mp hzDummy
    change reserveRelabel hA R (Fin.natAdd m δ)=realEmbedding m A g at he
    rw [reserveRelabel_dummy hA R δ (Finset.mem_filter.mp hδ).2] at he
    have hD:realEmbedding m A g∈dummyLabels m A:=he▸hR (reserveEmbedding_mem R _)
    exact False.elim ((not_le_of_gt g.isLt) ((mem_dummyLabels_iff _).mp hD))
  ·intro hg
   exact Finset.mem_image.mpr ⟨realEmbedding m a g,hg,reserveRelabel_real hA R g⟩

/-- The zero-reserve case is the SAME supported-inventory injection,
including when the target itself has zero actual dummy labels. Positivity
of m+A supplies only the unused ambient fallback. -/
theorem reserveRelabel_injectiveOn_real_stock {m a A:ℕ} (hA:0< m+A)
    (E:Finset (Fin m)):
    Set.InjOn (reserveRelabel (a:=a) hA (∅:Finset (Fin (m+A))))
      (E.map (realEmbedding m a)):=by
  simpa only [reserveSourceStock_empty] using
    reserveRelabel_injectiveOn_stock hA E (∅:Finset (Fin (m+A))) (Finset.empty_subset _)

/-- No-dummy realization preserves the SAME original real bundle even
with unused formal source labels and zero target dummy labels. -/
theorem reserveRelabel_realPart_empty {m a A:ℕ} (hA:0< m+A)
    (E:Finset (Fin m)) (B:Finset (Fin (m+a)))
    (hB:B⊆E.map (realEmbedding m a)):
    realPart (B.image (reserveRelabel hA (∅:Finset (Fin (m+A)))))=realPart B:=by
  apply reserveRelabel_realPart hA E (∅:Finset (Fin (m+A))) (Finset.empty_subset _)
  simpa only [reserveSourceStock_empty] using hB

end FairDivision.BF.Recording
