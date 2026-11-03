import FairDivision.BF.Recording.Graph

/-! Literal real-item coordinate transport for different local dummy stocks.
No dummy label is retained in the recording or child-profile vertices. -/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Recording

@[simp] theorem realPart_realMap {m a:ℕ} (A:Finset (Fin m)):
    realPart (A.map (realEmbedding m a))=A:=by
  classical
  ext g
  simp [realPart,Finset.mem_map,(realEmbedding m a).injective.eq_iff]

/-- An augmented label is dummy exactly when it is beyond the real prefix. -/
theorem mem_dummyLabels_iff {m a:ℕ} (z:Fin (m+a)):
    z∈dummyLabels m a↔m≤z.val:=by
  constructor
  ·intro hz
   obtain ⟨δ,hδ,rfl⟩:=Finset.mem_map.mp hz
   change m≤ m+δ.val
   omega
  ·intro hz
   let δ:Fin a:=⟨z.val-m,by have h:=z.isLt;omega⟩
   refine Finset.mem_map.mpr ⟨δ,Finset.mem_univ _,?_⟩
   apply Fin.ext
   change m+(z.val-m)=z.val
   omega

/-- Every dummy-free augmented bundle is literally the image of its original
real set; no arbitrary enumeration is introduced. -/
theorem realMap_realPart_of_disjoint {m a:ℕ} (A:Finset (Fin (m+a)))
    (hA:Disjoint A (dummyLabels m a)):
    (realPart A).map (realEmbedding m a)=A:=by
  classical
  ext z
  constructor
  ·intro hz
   obtain ⟨g,hg,rfl⟩:=Finset.mem_map.mp hz
   exact (Finset.mem_filter.mp hg).2
  ·intro hz
   have hzReal:z.val< m:=by
     by_contra hn
     exact (Finset.disjoint_left.mp hA) hz
       ((mem_dummyLabels_iff z).mpr (by omega))
   let g:Fin m:=⟨z.val,hzReal⟩
   have he:realEmbedding m a g=z:=Fin.ext rfl
   refine Finset.mem_map.mpr ⟨g,?_,he⟩
   exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.symm▸hz⟩

theorem card_realPart_of_disjoint {m a:ℕ} (A:Finset (Fin (m+a)))
    (hA:Disjoint A (dummyLabels m a)):(realPart A).card=A.card:=by
  rw [←Finset.card_map (realEmbedding m a),realMap_realPart_of_disjoint A hA]

end FairDivision.BF.Recording
