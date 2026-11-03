import FairDivision.BF.Recording.GraphGeometry
import FairDivision.Finite.BundlesToAllocation
import FairDivision.Topology.FiniteSimplexSupportMap
import FairDivision.Topology.SimplexOneSkeletonMap

/-!
# The literal leaf recording function and its certified lottery

Phi₁ is t minus the affine average of endpoint real-bundle values. Its zero
is witnessed by the SAME probability vector, pushed to the represented
one-position partial allocations. This keeps the actual endpoint weights,
the exact common value, and the actual positive-support available pool.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace FairDivision.BF.Recording

open FairDivision.Topology FairDivision.Finite

/-- The affine interpolation of real bundle values, defined on the whole
simplex and then restricted to the graph. -/
def expected {a q m:ℕ} (v:Finset (Fin m)→ℝ) (x:Space a q m):ℝ:=
  ∑b:Vertex a q m,x.1.1 b*v (real b)

theorem continuous_expected {a q m:ℕ} (v:Finset (Fin m)→ℝ):
    Continuous (expected (a:=a) (q:=q) v):=by
  unfold expected
  apply continuous_finset_sum
  intro b hb
  exact (((continuous_apply b).comp continuous_subtype_val).comp
    continuous_subtype_val).mul continuous_const

/-- The manuscript formula t minus the affine bundle value. -/
def leafPhi {q m:ℕ} (v:Finset (Fin m)→ℝ) (z:Space 1 q m×ℝ):ℝ:=
  z.2-expected v z.1

theorem continuous_leafPhi {q m:ℕ} (v:Finset (Fin m)→ℝ):Continuous (leafPhi (q:=q) v):=
  continuous_snd.sub ((continuous_expected v).comp continuous_fst)

@[simp] theorem leafPhi_vertex {q m:ℕ} (v:Finset (Fin m)→ℝ)
    (b:Vertex 1 q m) (t:ℝ):leafPhi v (vertexPoint b,t)=t-v (real b):=by
  classical
  simp [leafPhi,expected,vertexPoint,Pi.single_apply]

/-- On an edge the literal lottery weight is its interval parameter,
so the recorder has exactly the manuscript's `(1-s)v(P)+s v(Q)` formula. -/
theorem leafPhi_edge {q m:ℕ} (v:Finset (Fin m)→ℝ)
    (x:Space 1 q m) (b c:Vertex 1 q m) (hbc:b≠c)
    (hSupport:finiteSimplexSupport x.1={b,c}) (t:ℝ):
    leafPhi v (x,t)=t-((1-x.1.1 c)*v (real b)+x.1.1 c*v (real c)):=by
  classical
  have hZero:∀d:Vertex 1 q m,d∉({b,c}:Finset _)→x.1.1 d=0:=by
    intro d hd
    apply simplex_coordinate_eq_zero_of_not_support x.1
    simpa only [hSupport] using hd
  have hRestrict:(∑d ∈ ({b,c}:Finset _),x.1.1 d*v (real d))=expected v x:=by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro d hdU hdPair
    rw [hZero d hdPair,zero_mul]
  have hWeights:x.1.1 b+x.1.1 c=1:=by
    calc
      x.1.1 b+x.1.1 c=(∑d ∈ ({b,c}:Finset _),x.1.1 d):=by simp [hbc]
      _=(∑d:Vertex 1 q m,x.1.1 d):=by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro d hdU hdPair
        exact hZero d hdPair
      _=1:=x.1.2.2
  have hFirst:x.1.1 b=1-x.1.1 c:=by linarith
  unfold leafPhi
  rw [←hRestrict]
  simp only [Finset.sum_pair hbc,hFirst]

/-- The same affine average lies strictly above every strict lower bound
on the finite family of real-bundle values. -/
theorem lower_lt_expected {a q m:ℕ} (v:Finset (Fin m)→ℝ)
    (L:ℝ) (hL:∀A:Finset (Fin m),L<v A) (x:Space a q m):
    L<expected v x:=by
  classical
  obtain ⟨b,hb⟩:=finiteSimplexSupport_nonempty x.1
  have hbpos:0<x.1.1 b:=(mem_finiteSimplexSupport_iff x.1 b).mp hb
  have hStrict:(∑c:Vertex a q m,x.1.1 c*L)<
      ∑c:Vertex a q m,x.1.1 c*v (real c):=by
    apply Finset.sum_lt_sum
    ·intro c hc
     exact mul_le_mul_of_nonneg_left (hL (real c)).le (x.1.2.1 c)
    ·exact ⟨b,Finset.mem_univ _,mul_lt_mul_of_pos_left (hL (real b)) hbpos⟩
  simpa only [expected,←Finset.sum_mul,x.1.2.2,one_mul] using hStrict

theorem expected_lt_upper {a q m:ℕ} (v:Finset (Fin m)→ℝ)
    (H:ℝ) (hH:∀A:Finset (Fin m),v A<H) (x:Space a q m):
    expected v x<H:=by
  classical
  obtain ⟨b,hb⟩:=finiteSimplexSupport_nonempty x.1
  have hbpos:0<x.1.1 b:=(mem_finiteSimplexSupport_iff x.1 b).mp hb
  have hStrict:(∑c:Vertex a q m,x.1.1 c*v (real c))<
      ∑c:Vertex a q m,x.1.1 c*H:=by
    apply Finset.sum_lt_sum
    ·intro c hc
     exact mul_le_mul_of_nonneg_left (hH (real c)).le (x.1.2.1 c)
    ·exact ⟨b,Finset.mem_univ _,mul_lt_mul_of_pos_left (hH (real b)) hbpos⟩
  simpa only [expected,←Finset.sum_mul,x.1.2.2,one_mul] using hStrict

theorem leafPhi_lower {q m:ℕ} (v:Finset (Fin m)→ℝ)
    (L:ℝ) (hL:∀A:Finset (Fin m),L<v A) (x:Space 1 q m):
    leafPhi v (x,L)<0:=sub_neg.mpr (lower_lt_expected v L hL x)

theorem leafPhi_upper {q m:ℕ} (v:Finset (Fin m)→ℝ)
    (H:ℝ) (hH:∀A:Finset (Fin m),v A<H) (x:Space 1 q m):
    0<leafPhi v (x,H):=sub_pos.mpr (expected_lt_upper v H hH x)

/-- The represented bundle assigned to the one leaf position. -/
def leafVertex {q m:ℕ} (b:Vertex 1 q m):
    PartialVertex 1 (dummyLabels m 1) (q-1) 1:=
  ⟨partialAllocationFromBundles (fun _ : Fin 1=>represented b),by
    intro i
    rw [partialBundle_fromBundles _ (fun i j hij=>False.elim (hij (Subsingleton.elim i j)))]
    constructor
    ·simpa only [one_mul] using card_represented b
    ·rw [represented_inter_dummy,card_initialDummies m 1 (dummyCount b) (dummyCount_le b)]
     exact dummyCount_le b⟩

@[simp] theorem leafVertex_bundle {q m:ℕ} (b:Vertex 1 q m) (i:Fin 1):
    partialBundle (leafVertex b).1 i=represented b:=
  partialBundle_fromBundles _ (fun i j hij=>False.elim (hij (Subsingleton.elim i j))) i

/-- The SAME graph lottery, with each endpoint replaced by its actual
represented one-position partial allocation. -/
def leafLottery {q m:ℕ} (x:Space 1 q m):
    stdSimplex ℝ (PartialVertex 1 (dummyLabels m 1) (q-1) 1):=
  stdSimplex.map leafVertex x.1

/-- All positive-probability outcomes use only the exact available pool. -/
theorem leafLottery_pool_subset {q m:ℕ} (x:Space 1 q m) (i:Fin 1):
    pool (lotterySupport (leafLottery x)) i⊆available x:=by
  classical
  intro z hz
  obtain ⟨_,X,hX,hXz⟩:=Finset.mem_filter.mp hz
  have hMapped:X∈finiteSimplexSupport (stdSimplex.map leafVertex x.1):=hX
  obtain ⟨b,hb,hbX⟩:=Finset.mem_image.mp
    (finiteSimplexSupport_map_subset leafVertex x.1 hMapped)
  have hBundle:z∈partialBundle X.1 i:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hXz⟩
  rw [←hbX,leafVertex_bundle] at hBundle
  exact represented_subset_available x hb hBundle

/-- One leaf position has no cross-position overlap, and its whole available
pool contains at most one dummy. Thus the leaf lottery is compatible. -/
theorem leafLottery_compatible {q m:ℕ} (x:Space 1 q m):
    leafLottery x∈compatibleLotterySpace 1 (m+1) (q-1) 1 (dummyLabels m 1):=by
  constructor
  ·intro i j hij
   exact False.elim (hij (Subsingleton.elim i j))
  ·intro i
   have hSubset:pool (lotterySupport (leafLottery x)) i∩dummyLabels m 1⊆
       available x∩dummyLabels m 1:=
     Finset.inter_subset_inter (leafLottery_pool_subset x i) Finset.Subset.rfl
   exact (Finset.card_le_card hSubset).trans (available_dummy_bound x)

/-- Pushforward preserves the actual finite weighted average. -/
theorem leafLottery_expected {q m:ℕ} (v:Finset (Fin m)→ℝ)
    (x:Space 1 q m) (i:Fin 1):
    (∑X:PartialVertex 1 (dummyLabels m 1) (q-1) 1,
      (leafLottery x).1 X*v (realPart (partialBundle X.1 i)))=expected v x:=by
  classical
  change (∑X:PartialVertex 1 (dummyLabels m 1) (q-1) 1,
    FunOnFinite.linearMap ℝ ℝ leafVertex x.1.1 X*
      v (realPart (partialBundle X.1 i)))=_
  simp_rw [FunOnFinite.linearMap_apply_apply]
  calc
    (∑X:PartialVertex 1 (dummyLabels m 1) (q-1) 1,
      (∑b:Vertex 1 q m with leafVertex b=X,x.1.1 b)*
        v (realPart (partialBundle X.1 i)))=
      ∑X:PartialVertex 1 (dummyLabels m 1) (q-1) 1,
        ∑b:Vertex 1 q m with leafVertex b=X,
          x.1.1 b*v (realPart (partialBundle (leafVertex b).1 i)):=by
      apply Finset.sum_congr rfl
      intro X hX
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      rw [(Finset.mem_filter.mp hb).2]
    _=∑b:Vertex 1 q m,x.1.1 b*v (realPart (partialBundle (leafVertex b).1 i)):=
      Finset.sum_fiberwise Finset.univ leafVertex _
    _=expected v x:=by simp only [leafVertex_bundle,realPart_represented,expected]

/-- Exact leaf certificate at a zero: no rounding, support enlargement,
new lottery choice, or different average is introduced. -/
theorem leafPhi_zero_realizes {q m:ℕ} (v:Finset (Fin m)→ℝ)
    (x:Space 1 q m) (t:ℝ) (hZero:leafPhi v (x,t)=0):
    ∃μ:stdSimplex ℝ (PartialVertex 1 (dummyLabels m 1) (q-1) 1),
      μ∈compatibleLotterySpace 1 (m+1) (q-1) 1 (dummyLabels m 1) ∧
      (∀i:Fin 1,pool (lotterySupport μ) i⊆available x) ∧
      ∀i:Fin 1,(∑X:PartialVertex 1 (dummyLabels m 1) (q-1) 1,
        μ.1 X*v (realPart (partialBundle X.1 i)))=t:=by
  refine ⟨leafLottery x,leafLottery_compatible x,leafLottery_pool_subset x,?_⟩
  intro i
  rw [leafLottery_expected]
  exact (sub_eq_zero.mp hZero).symm

end FairDivision.BF.Recording
