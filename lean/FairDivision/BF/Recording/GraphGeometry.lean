import FairDivision.BF.Recording.Graph

/-! Exact representative and pool arithmetic for the recording graph.
The initial dummy prefixes make every graph edge ONE actual item exchange,
including a real-for-dummy edge. No dummy identities enter the vertices. -/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Recording

open FairDivision.Topology

theorem realEmbedding_not_initialDummies {m a d:ℕ} (i:Fin m):
    realEmbedding m a i∉initialDummies m a d:=by
  intro hi
  obtain ⟨j,hj,he⟩:=Finset.mem_map.mp hi
  exact realEmbedding_ne_dummy i j he.symm

theorem initialDummies_succ {m a d:ℕ} (hd:d<a):
    initialDummies m a (d+1)=
      insert (Fin.natAdd m (⟨d,hd⟩:Fin a)) (initialDummies m a d):=by
  classical
  ext z
  constructor
  ·intro hz
   obtain ⟨j,hj,rfl⟩:=Finset.mem_map.mp hz
   have hjd:= (Finset.mem_filter.mp hj).2
   by_cases he:j.val=d
   ·apply Finset.mem_insert.mpr
    left
    exact congrArg (Fin.natAdd m) (Fin.ext he)
   ·apply Finset.mem_insert.mpr
    right
    exact Finset.mem_map.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩,rfl⟩
  ·intro hz
   rcases Finset.mem_insert.mp hz with he|hz
   ·rw [he]
    exact Finset.mem_map.mpr ⟨⟨d,hd⟩,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,by
        simpa only [Fin.val_mk,Fin.val_natAdd,Nat.add_sub_cancel_left]
          using Nat.lt_succ_self d⟩,rfl⟩
   ·exact initialDummies_mono (Nat.le_succ d) hz

theorem nextDummy_not_represented {a q m:ℕ} (b:Vertex a q m)
    (hd:dummyCount b<a):
    Fin.natAdd m (⟨dummyCount b,hd⟩:Fin a)∉represented b:=by
  intro hz
  rcases Finset.mem_union.mp hz with hz|hz
  ·obtain ⟨i,hi,he⟩:=Finset.mem_map.mp hz
   exact realEmbedding_ne_dummy i ⟨dummyCount b,hd⟩ he
  ·obtain ⟨j,hj,he⟩:=Finset.mem_map.mp hz
   have hjlt: j.val<dummyCount b:= (Finset.mem_filter.mp hj).2
   have hej:j.val=dummyCount b:=by
     have hv:=congrArg Fin.val he
     change m+j.val=m+dummyCount b at hv
     omega
   omega

/-- In a real exchange the only new available item is its incoming real item. -/
theorem represented_union_realExchange {a q m:ℕ} (b c:Vertex a q m)
    (h:RealExchange b c):
    ∃y:Fin m,realEmbedding m a y∉represented b ∧
      represented b∪represented c=insert (realEmbedding m a y) (represented b):=by
  classical
  obtain ⟨hD,x,hx,y,hy,hReal⟩:=h
  refine ⟨y,?_,?_⟩
  ·intro hyB
   rcases Finset.mem_union.mp hyB with hyR|hyD
   ·obtain ⟨z,hz,he⟩:=Finset.mem_map.mp hyR
    exact hy ((realEmbedding m a).injective he ▸hz)
   ·exact realEmbedding_not_initialDummies y hyD
  ·simp only [represented,hReal,←hD,Finset.map_insert,Finset.map_erase]
   ext z
   simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_erase]
   aesop

/-- In a dummy-count exchange the only new available item is the next
formal dummy label; the old dummy representatives are retained literally. -/
theorem represented_union_dummyExchange {a q m:ℕ} (b c:Vertex a q m)
    (h:DummyExchange b c):
    ∃δ:Fin a,Fin.natAdd m δ∉represented b ∧
      represented b∪represented c=insert (Fin.natAdd m δ) (represented b):=by
  classical
  obtain ⟨hD,x,hx,hReal⟩:=h
  have hd:dummyCount b<a:=by have hc:=dummyCount_le c;omega
  refine ⟨⟨dummyCount b,hd⟩,nextDummy_not_represented b hd,?_⟩
  simp only [represented,hReal,hD,Finset.map_erase,initialDummies_succ hd]
  ext z
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_erase]
  aesop

/-- Every nondegenerate graph edge makes exactly one extra item available. -/
theorem card_represented_union_of_adjacent {a q m:ℕ}
    (ha:0<a) (hq:0<q) (b c:Vertex a q m) (h:adjacent b c):
    (represented b∪represented c).card=a*q:=by
  have hProduct:0<a*q:=Nat.mul_pos ha hq
  have hReal:∀b c:Vertex a q m,RealExchange b c→
      (represented b∪represented c).card=a*q:=by
    intro b c hbc
    obtain ⟨y,hy,hUnion⟩:=represented_union_realExchange b c hbc
    rw [hUnion,Finset.card_insert_of_notMem hy,card_represented]
    omega
  have hDummy:∀b c:Vertex a q m,DummyExchange b c→
      (represented b∪represented c).card=a*q:=by
    intro b c hbc
    obtain ⟨δ,hδ,hUnion⟩:=represented_union_dummyExchange b c hbc
    rw [hUnion,Finset.card_insert_of_notMem hδ,card_represented]
    omega
  rcases h.2 with h|h|h|h
  ·exact hReal b c h
  ·simpa only [Finset.union_comm] using hReal c b h
  ·exact hDummy b c h
  ·simpa only [Finset.union_comm] using hDummy c b h

/-- Positive support distinguishes the manuscript's two pool sizes exactly. -/
theorem available_card {a q m:ℕ} (ha:0<a) (hq:0<q) (x:Space a q m):
    ((finiteSimplexSupport x.1).card=1 ∧(available x).card=a*q-1) ∨
    ((finiteSimplexSupport x.1).card=2 ∧(available x).card=a*q):=by
  classical
  have hn:0<(finiteSimplexSupport x.1).card:=
    Finset.card_pos.mpr (finiteSimplexSupport_nonempty x.1)
  have hle:(finiteSimplexSupport x.1).card≤2:=x.2.2.1
  by_cases hone:(finiteSimplexSupport x.1).card=1
  ·left
   refine ⟨hone,?_⟩
   obtain ⟨b,hb⟩:=Finset.card_eq_one.mp hone
   simpa [available,hb] using card_represented b
  ·right
   have htwo:(finiteSimplexSupport x.1).card=2:=by omega
   refine ⟨htwo,?_⟩
   obtain ⟨b,c,hbc,hSupp⟩:=Finset.card_eq_two.mp htwo
   have hb:b∈finiteSimplexSupport x.1:=by simp [hSupp]
   have hc:c∈finiteSimplexSupport x.1:=by simp [hSupp]
   rw [available_of_support_pair x b c hSupp]
   exact card_represented_union_of_adjacent ha hq b c (x.2.2.2 b hb c hc hbc)

end FairDivision.BF.Recording
