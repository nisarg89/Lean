import FairDivision.BF.VirtualValuationSpec
import FairDivision.BF.CompactMaxAdmissibility
import FairDivision.Topology.FiniteSimplexSkeletonExtension

/-!
# Higher-face assembly of the manuscript virtual valuation

The actual one-skeleton vector map is the input of this source adapter.
The full finite-simplex induction and geometric cap construction are proved
in the imported topology modules. Admissibility is checked at the union of
bundles in the point's POSITIVE support, including all lower-dimensional
boundary points, rather than at an unrestricted larger stock.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Topology

/-- The stock represented by a face of the marginal-lottery simplex. -/
noncomputable def virtualFaceStock {m r:ℕ}
    (S:Finset (FixedFinMarginalBundle m r)):Finset (Fin (m+1)):=by
  classical
  exact S.biUnion (fun B=>B.1)

theorem virtualFaceStock_mono {m r:ℕ}{S T:Finset (FixedFinMarginalBundle m r)}
    (hST:S⊆T):virtualFaceStock S⊆virtualFaceStock T:=by
  classical
  intro g hg
  obtain ⟨B,hB,hgB⟩:=Finset.mem_biUnion.mp hg
  exact Finset.mem_biUnion.mpr ⟨B,hST hB,hgB⟩

@[simp] theorem virtualFaceStock_support {m r:ℕ}
    (x:stdSimplex ℝ (FixedFinMarginalBundle m r)):
    virtualFaceStock (finiteSimplexSupport x)=finMarginalStock x:=rfl

/-- Exact deterministic point of the one-skeleton. The proof field adds no
machine or geometric data and any equivalent constructor is definitionally
interchangeable by proof irrelevance. -/
noncomputable def virtualOneSkeletonVertex {m r:ℕ}
    (B:FixedFinMarginalBundle m r):SmallSupportSimplex (FixedFinMarginalBundle m r) 2:=by
  classical
  exact ⟨stdSimplex.vertex B,by rw [finiteSimplexSupport_vertex];simp⟩

/-- Existing stock monotonicity and existing attained-maximum witness
transfer supply exactly the abstract closure used by finite face filling. -/
theorem virtualAdmissibility_supportLocalMaxClosed {n m q:ℕ}
    (v:Fin n→Finset (Fin m)→ℝ):
    SupportLocalMaxClosed
      (fun (S:Finset (FixedFinMarginalBundle m (q-1))) (u:Fin n→ℝ)=>
        IsAdmissible q 0 (fun i E=>v i (marginalRealPart E)) (virtualFaceStock S) u):=by
  classical
  constructor
  ·intro S T u hST hAdm
   exact isAdmissible_mono (virtualFaceStock_mono hST) hAdm
  ·intro S u z hu hEq hDom
   let K:Set (Fin n):=Set.univ
   have hMax:∀j:Fin n,∃a∈K,∀b∈K,u b j≤u a j:=by
     intro j
     refine ⟨j,Set.mem_univ j,?_⟩
     intro b hb
     rw [←hEq j]
     exact hDom j b
   have hAdmissible:=isAdmissible_attained_coordinatewise_max (q:=q) (0:Fin (m+1))
     (fun i E=>v i (marginalRealPart E)) (virtualFaceStock S) K u hMax
     (fun a ha=>hu a)
   have hChosen:(fun j=>u (Classical.choose (hMax j)) j)=z:=by
     funext j
     apply le_antisymm
     ·exact hDom j _
     ·rw [hEq j]
      exact (Classical.choose_spec (hMax j)).2 j (Set.mem_univ j)
   simpa only [hChosen] using hAdmissible

/-- The full manuscript specification follows from its actual continuous
one-skeleton construction. All higher-face extension and pasting work is
performed by the existing actual cap theorem and finite induction. -/
theorem exists_virtualValuationSpec_of_oneSkeleton {n m q:ℕ}
    (v:Fin n→Finset (Fin m)→ℝ)
    (edge:C(SmallSupportSimplex (FixedFinMarginalBundle m (q-1)) 2,Fin n→ℝ))
    (hVertex:∀B:FixedFinMarginalBundle m (q-1),
      edge (virtualOneSkeletonVertex B)=fun i=>v i (marginalRealPart B.1))
    (hEdge:∀x,IsAdmissible q 0 (fun i E=>v i (marginalRealPart E))
      (finMarginalStock x.1) (edge x)):
    Nonempty (VirtualValuationSpec (q:=q) v):=by
  let P:Finset (FixedFinMarginalBundle m (q-1))→(Fin n→ℝ)→Prop:=
    fun S u=>IsAdmissible q 0 (fun i E=>v i (marginalRealPart E)) (virtualFaceStock S) u
  have hP:SupportLocalMaxClosed P:=virtualAdmissibility_supportLocalMaxClosed v
  obtain ⟨score,hOld,hAdmissible⟩:=exists_supportLocal_simplex_extension P hP edge hEdge
  refine ⟨{
    score:=score
    continuous_score:=score.continuous
    vertex_score:=?_
    admissible_score:=?_ }⟩
  ·intro B
   exact (hOld (virtualOneSkeletonVertex B)).trans (hVertex B)
  ·intro x
   exact hAdmissible x

end FairDivision.BF
