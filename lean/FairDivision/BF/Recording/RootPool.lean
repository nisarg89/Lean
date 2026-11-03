import FairDivision.BF.Recording.ReserveRelabel
import FairDivision.Topology.SimplexOneSkeletonMap

/-!
# The manuscript's full root pool

The root point is exactly the midpoint of the edge from `(M-x,d)` to
`(M-y,d)`, for distinct real items x,y. Its positive support is both endpoints,
so its available pool contains every real item and exactly the first d formal
dummies. Relabel only those used dummies into the actual d-item dummy stock.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Recording

open FairDivision.Topology
open scoped BigOperators Classical

/-- Actual midpoint probability vector, with its exact two-point support. -/
def pairMidpoint {V:Type*} [Fintype V] (b c:V):stdSimplex ℝ V:=
  ⟨(1/2:ℝ) • (stdSimplex.vertex b).1 + (1/2:ℝ) • (stdSimplex.vertex c).1,
    (convex_stdSimplex ℝ V) (stdSimplex.vertex b).2 (stdSimplex.vertex c).2
      (by norm_num) (by norm_num) (by norm_num)⟩

theorem pairMidpoint_support {V:Type*} [Fintype V] (b c:V):
    finiteSimplexSupport (pairMidpoint b c)={b,c}:=by
  classical
  ext z
  by_cases hb:z=b
  · subst z
    by_cases hbc:b=c
    · subst c
      norm_num [finiteSimplexSupport,pairMidpoint,stdSimplex.vertex_coe,Pi.single_apply]
    · norm_num [finiteSimplexSupport,pairMidpoint,stdSimplex.vertex_coe,
        Pi.single_apply,hbc,Ne.symm hbc]
  · by_cases hc:z=c
    · subst z
      norm_num [finiteSimplexSupport,pairMidpoint,stdSimplex.vertex_coe,
        Pi.single_apply,hb,Ne.symm hb]
    · norm_num [finiteSimplexSupport,pairMidpoint,stdSimplex.vertex_coe,
        Pi.single_apply,hb,Ne.symm hb,hc,Ne.symm hc]


/-- The midpoint belongs to the actual recording graph, rather than a
higher simplex of its clique complex. -/
def edgeMidpoint {a q m:ℕ} (b c:Vertex a q m) (hbc:adjacent b c):Space a q m:=by
  classical
  letI : DecidableEq (Vertex a q m):=Classical.decEq _
  refine ⟨pairMidpoint b c,?_⟩
  change finiteSimplexSupport (pairMidpoint b c) ∈ graphComplex a q m
  rw [pairMidpoint_support]
  refine ⟨Finset.insert_nonempty b {c},?_,?_⟩
  · simpa only [Finset.card_singleton] using Finset.card_insert_le b {c}
  intro u hu z hz huz
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu hz
  rcases hu with rfl|rfl <;> rcases hz with rfl|rfl
  ·exact False.elim (huz rfl)
  ·exact hbc
  ·exact adjacent_symm hbc
  ·exact False.elim (huz rfl)

/-- Root endpoint omitting the selected real item. -/
def rootVertex {n q m d:ℕ} (hd:d<n) (hPad:m+d=n*q)
    (x:Fin m):Vertex n q m:=
  ⟨((Finset.univ:Finset (Fin m)).erase x,⟨d,by omega⟩),by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ x),Finset.card_univ,Fintype.card_fin]
    have hx:=x.isLt
    omega⟩

@[simp] theorem rootVertex_real {n q m d:ℕ} (hd:d<n) (hPad:m+d=n*q)
    (x:Fin m):real (rootVertex hd hPad x)=(Finset.univ:Finset (Fin m)).erase x:=rfl

@[simp] theorem rootVertex_dummyCount {n q m d:ℕ} (hd:d<n)
    (hPad:m+d=n*q) (x:Fin m):dummyCount (rootVertex hd hPad x)=d:=rfl

theorem rootVertices_adjacent {n q m d:ℕ} (hd:d<n) (hPad:m+d=n*q)
    (x y:Fin m) (hxy:x≠y):
    adjacent (rootVertex hd hPad x) (rootVertex hd hPad y):=by
  classical
  have hNe:rootVertex hd hPad x≠rootVertex hd hPad y:=by
    intro he
    have hReal:=congrArg real he
    simp only [rootVertex_real] at hReal
    have hx:x∈(Finset.univ:Finset (Fin m)).erase y:=by simp [hxy]
    rw [←hReal] at hx
    exact Finset.notMem_erase x _ hx
  refine ⟨hNe,Or.inl ⟨rfl,y,?_,x,?_,?_⟩⟩
  ·simp [hxy.symm]
  ·simp
  ·ext z
   simp only [rootVertex_real,Finset.mem_erase,Finset.mem_univ,and_true,
     Finset.mem_insert]
   by_cases hz:z=x <;>by_cases hzy:z=y <;>simp_all

/-- The literal midpoint chosen in the final paragraph of Section 4. -/
def rootMidpoint {n q m d:ℕ} (hd:d<n) (hPad:m+d=n*q)
    (x y:Fin m) (hxy:x≠y):Space n q m:=
  edgeMidpoint (rootVertex hd hPad x) (rootVertex hd hPad y)
    (rootVertices_adjacent hd hPad x y hxy)

/-- The full pool, with no unused formal dummy labels. -/
theorem rootMidpoint_available {n q m d:ℕ} (hd:d<n) (hPad:m+d=n*q)
    (x y:Fin m) (hxy:x≠y):
    available (rootMidpoint hd hPad x y hxy)=
      (Finset.univ:Finset (Fin m)).map (realEmbedding m n)∪initialDummies m n d:=by
  classical
  have hSupport : finiteSimplexSupport (rootMidpoint hd hPad x y hxy).1=
      {rootVertex hd hPad x,rootVertex hd hPad y} := by
    ext z
    have hPoint : (rootMidpoint hd hPad x y hxy).1.1 z=
        (pairMidpoint (rootVertex hd hPad x) (rootVertex hd hPad y)).1 z := by
      by_cases hb:z=rootVertex hd hPad x <;>
        by_cases hc:z=rootVertex hd hPad y <;>
        simp [rootMidpoint,edgeMidpoint,pairMidpoint,stdSimplex.vertex_coe,
          Pi.single_apply,hb,hc]
    have h:=congrArg (fun S : Finset (Vertex n q m)=>z∈S)
      (pairMidpoint_support (rootVertex hd hPad x) (rootVertex hd hPad y))
    simpa only [mem_finiteSimplexSupport_iff,Finset.mem_insert,Finset.mem_singleton,hPoint]
      using (Iff.of_eq h)
  rw [available_of_support_pair _ _ _ hSupport]
  simp only [represented,rootVertex_real,rootVertex_dummyCount]
  have hReal:((Finset.univ:Finset (Fin m)).erase x)∪Finset.univ.erase y=Finset.univ:=by
    ext z
    constructor
    · intro _; exact Finset.mem_univ _
    · intro _
      by_cases hz:z=x
      · have hzy:z≠y:=fun he=>hxy (hz.symm.trans he)
        exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hzy,Finset.mem_univ _⟩)
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hz,Finset.mem_univ _⟩)
  rw [show
    ((Finset.univ.erase x).map (realEmbedding m n)∪initialDummies m n d)∪
      ((Finset.univ.erase y).map (realEmbedding m n)∪initialDummies m n d)=
    (((Finset.univ.erase x)∪Finset.univ.erase y).map (realEmbedding m n))∪
      initialDummies m n d by rw [Finset.map_union];ext z;simp only [Finset.mem_union];tauto]
  rw [hReal]

/-- The root certificate with the ACTUAL d dummy labels. All real items
retain their original identities and every expected value is unchanged. -/
theorem rootMidpoint_certifies_actual {n q m d:ℕ}
    (hd:d<n) (hPad:m+d=n*q) (hInventory:0< m+d)
    (x y:Fin m) (hxy:x≠y)
    {v:Finset (Fin m)→ℝ} {t:ℝ}
    (h:Certifies v (rootMidpoint hd hPad x y hxy) t):
    ∃μ:stdSimplex ℝ (PartialVertex n (dummyLabels m d) (q-1) 1),
      μ∈compatibleLotterySpace n (m+d) (q-1) 1 (dummyLabels m d) ∧
      ∀i:Fin n,(∑X:PartialVertex n (dummyLabels m d) (q-1) 1,
        μ.1 X*v (realPart (partialBundle X.1 i)))=t:=by
  let R:=dummyLabels m d
  let e:=reserveRelabel (a:=n) hInventory R
  have hStock:available (rootMidpoint hd hPad x y hxy)=
      reserveSourceStock (a:=n) (Finset.univ:Finset (Fin m)) R:=by
    rw [rootMidpoint_available]
    simp only [reserveSourceStock,R,card_dummyLabels]
  have hInject:Set.InjOn e (available (rootMidpoint hd hPad x y hxy)):=by
    rw [hStock]
    exact reserveRelabel_injectiveOn_stock hInventory Finset.univ R Finset.Subset.rfl
  have hDummy:∀g∈available (rootMidpoint hd hPad x y hxy),
      e g∈dummyLabels m d↔g∈dummyLabels m n:=by
    intro g hg
    apply reserveRelabel_dummy_iff_on_stock hInventory Finset.univ R Finset.Subset.rfl g
    simpa only [hStock] using hg
  obtain ⟨μ,hμ,hPool,hMean⟩:=h.relabel (dummyLabels m d) e hInject hDummy
    (fun B=>v (realPart B)) (by
      intro B hB
      rw [reserveRelabel_realPart hInventory Finset.univ R Finset.Subset.rfl B
        (by simpa only [hStock] using hB)])
  exact ⟨μ,hμ,hMean⟩

end FairDivision.BF.Recording
