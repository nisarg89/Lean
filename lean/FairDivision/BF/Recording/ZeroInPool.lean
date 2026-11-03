import FairDivision.BF.Recording.ExchangePaths
import FairDivision.Finite.ExpectedValue
import Mathlib.Topology.Order.IntermediateValue

/-! The manuscript's supported-sign dichotomy and intermediate-value recovery
on the exact nested-dummy exchange path inside one outer pool. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

open scoped unitInterval Topology

namespace FairDivision.BF.Recording

open FairDivision.Topology

/-- Two weak opposite signs suffice; endpoint zeros are retained literally. -/
theorem recording_zero_in_stock {a q m:ℕ}
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH) (t:Set.Icc L H)
    (E:Finset (Fin m)) (d:ℕ) (b c:Vertex a q m)
    (hb:real b⊆E ∧dummyCount b≤d) (hc:real c⊆E ∧dummyCount c≤d)
    (hNeg:Φ.phi (vertexPoint b,t)≤0) (hPos:0≤Φ.phi (vertexPoint c,t)):
    ∃x:Space a q m,x∈stockSpace E d ∧Φ.phi (x,t)=0:=by
  have hJoined:=recordingVertices_joinedIn_stock E d b c hb hc
  let γ:=hJoined.somePath
  let f:C(I,ℝ):=Φ.phi.comp ⟨fun s=>(γ s,t),γ.continuous.prodMk continuous_const⟩
  have hLow:f 0≤0:=by
    change Φ.phi (γ 0,t)≤0
    rw [γ.source]
    exact hNeg
  have hHigh:0≤f 1:=by
    change 0≤Φ.phi (γ 1,t)
    rw [γ.target]
    exact hPos
  have hZero:(0:ℝ)∈Set.range f:=
    intermediate_value_univ (0:I) (1:I) f.continuous ⟨hLow,hHigh⟩
  obtain ⟨s,hs⟩:=hZero
  exact ⟨γ s,hJoined.somePath_mem s,hs⟩

/-- A zero weighted mean has a positive-supported weakly negative and a
positive-supported weakly positive value. Equality is already a supported
zero; otherwise these are the manuscript's two strict opposite signs. -/
theorem supported_child_scores_bracket_zero {p a q m:ℕ}
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH)
    (μ:stdSimplex ℝ (ChildProfile p a q m)) (t:Set.Icc L H) (i:Fin p)
    (hMean:childScores Φ (μ,t) i=0):
    (∃b∈finiteSimplexSupport μ,Φ.phi (vertexPoint (b i),t)=0) ∨
    ∃b∈finiteSimplexSupport μ,∃c∈finiteSimplexSupport μ,
      Φ.phi (vertexPoint (b i),t)<0 ∧0<Φ.phi (vertexPoint (c i),t):=by
  classical
  have hNegMean:(∑b:ChildProfile p a q m,
      μ.1 b*(-Φ.phi (vertexPoint (b i),t)))=0:=by
    rw [show (∑b:ChildProfile p a q m,μ.1 b*(-Φ.phi (vertexPoint (b i),t)))=
      -(childScores Φ (μ,t) i) by simp only [childScores,mul_neg,←Finset.sum_neg_distrib]]
    rw [hMean,neg_zero]
  obtain ⟨b,hb,hbPos,hbScore⟩:=FairDivision.weighted_average_exists_ge_pos
    Finset.univ μ.1 (fun b=>-Φ.phi (vertexPoint (b i),t)) 0
    (fun b _=>μ.2.1 b) (by simpa using μ.2.2)
    (by simpa using hNegMean)
  obtain ⟨c,hc,hcPos,hcScore⟩:=FairDivision.weighted_average_exists_ge_pos
    Finset.univ μ.1 (fun b=>Φ.phi (vertexPoint (b i),t)) 0
    (fun b _=>μ.2.1 b) (by simpa using μ.2.2)
    (by simpa [childScores] using hMean)
  have hbS:b∈finiteSimplexSupport μ:=(mem_finiteSimplexSupport_iff μ b).mpr hbPos
  have hcS:c∈finiteSimplexSupport μ:=(mem_finiteSimplexSupport_iff μ c).mpr hcPos
  by_cases hbZero:Φ.phi (vertexPoint (b i),t)=0
  ·exact Or.inl ⟨b,hbS,hbZero⟩
  by_cases hcZero:Φ.phi (vertexPoint (c i),t)=0
  ·exact Or.inl ⟨c,hcS,hcZero⟩
  ·right
   exact ⟨b,hbS,c,hcS,
     lt_of_le_of_ne (neg_nonneg.mp hbScore) hbZero,
     lt_of_le_of_ne hcScore (Ne.symm hcZero)⟩

/-- The actual zero for child i uses only that child's outer real pool and
maximum dummy reserve. The expected-zero hypothesis is the literal ith
coordinate of the continuous score map, not a separate oracle. -/
theorem child_zero_in_outer_pool {p a q m:ℕ}
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH)
    (μ:stdSimplex ℝ (ChildProfile p a q m)) (t:Set.Icc L H) (i:Fin p)
    (hMean:childScores Φ (μ,t) i=0):
    ∃x:Space a q m,
      x∈stockSpace (childRealPool (finiteSimplexSupport μ) i)
        (childDummyMax (finiteSimplexSupport μ) i) ∧Φ.phi (x,t)=0:=by
  classical
  let E:=childRealPool (finiteSimplexSupport μ) i
  let d:=childDummyMax (finiteSimplexSupport μ) i
  have hStock:∀b∈finiteSimplexSupport μ,
      real (b i)⊆E ∧dummyCount (b i)≤d:=by
    intro b hb
    refine ⟨?_,Finset.le_sup (f:=fun c=>dummyCount (c i)) hb⟩
    intro g hg
    exact Finset.mem_biUnion.mpr ⟨b,hb,hg⟩
  rcases supported_child_scores_bracket_zero Φ μ t i hMean with hZero|hSigns
  ·obtain ⟨b,hb,hbZero⟩:=hZero
   exact ⟨vertexPoint (b i),(vertexPoint_mem_stockSpace E d (b i)).mpr (hStock b hb),hbZero⟩
  ·obtain ⟨b,hb,c,hc,hNeg,hPos⟩:=hSigns
   exact recording_zero_in_stock Φ t E d (b i) (c i) (hStock b hb) (hStock c hc) hNeg.le hPos.le

/-- Apply the SAME child recorder at that actual zero. Its entire canonical
lottery stays inside the outer real pool plus its needed initial dummy reserve. -/
theorem child_lottery_in_outer_pool {p a q m:ℕ}
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH)
    (μ:stdSimplex ℝ (ChildProfile p a q m)) (t:Set.Icc L H) (i:Fin p)
    (hMean:childScores Φ (μ,t) i=0):
    ∃x:Space a q m,Certifies v x t.val ∧
      available x⊆(childRealPool (finiteSimplexSupport μ) i).map (realEmbedding m a)∪
        initialDummies m a (childDummyMax (finiteSimplexSupport μ) i):=by
  obtain ⟨x,hStock,hZero⟩:=child_zero_in_outer_pool Φ μ t i hMean
  exact ⟨x,Φ.realizes x t hZero,available_subset_of_stock _ _ x hStock⟩

end FairDivision.BF.Recording
