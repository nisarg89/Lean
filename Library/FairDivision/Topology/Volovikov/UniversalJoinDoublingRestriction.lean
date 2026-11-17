import FairDivision.Topology.Volovikov.UniversalJoinDoublingMass
import Mathlib.Algebra.BigOperators.Field

/-!
# Normalized restrictions to the two color blocks

When a doubled-join point has positive mass in one block, restriction and
renormalization give a point in the corresponding smaller universal join.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- Normalize the first color block of a doubled probability vector. -/
noncomputable def leftDoubledJoinRestrict
    {m : ℕ} {G : Type*} [Fintype G]
    (w : stdSimplex ℝ (Fin (m + m) × G))
    (h : 0 < leftDoubledJoinMass w) :
    stdSimplex ℝ (Fin m × G) := by
  classical
  refine ⟨fun v => w.1 (leftDoubledJoinVertex v) / leftDoubledJoinMass w,
    ?_, ?_⟩
  · intro v
    exact div_nonneg (w.2.1 _) h.le
  · rw [← Finset.sum_div]
    exact div_self (ne_of_gt h)

/-- Normalize the second color block of a doubled probability vector. -/
noncomputable def rightDoubledJoinRestrict
    {m : ℕ} {G : Type*} [Fintype G]
    (w : stdSimplex ℝ (Fin (m + m) × G))
    (h : 0 < rightDoubledJoinMass w) :
    stdSimplex ℝ (Fin m × G) := by
  classical
  refine ⟨fun v => w.1 (rightDoubledJoinVertex v) / rightDoubledJoinMass w,
    ?_, ?_⟩
  · intro v
    exact div_nonneg (w.2.1 _) h.le
  · rw [← Finset.sum_div]
    exact div_self (ne_of_gt h)

/-- A positive first-block restriction is still a universal-join point. -/
noncomputable def leftDoubledJoinRealization
    {m : ℕ} {G : Type*} [Fintype G]
    (w : simplicialRealization (universalJoinComplex (m + m) G))
    (h : 0 < leftDoubledJoinMass w.1) :
    simplicialRealization (universalJoinComplex m G) := by
  classical
  let x := leftDoubledJoinRestrict w.1 h
  refine ⟨x, ?_⟩
  change IsUniversalJoinFace (FairDivision.Topology.finiteSimplexSupport x)
  constructor
  · exact FairDivision.Topology.finiteSimplexSupport_nonempty x
  · intro i g g' hg hg'
    have hw : IsUniversalJoinFace
        (FairDivision.Topology.finiteSimplexSupport w.1) := w.2
    have hcoord : ∀ v : Fin m × G,
        v ∈ FairDivision.Topology.finiteSimplexSupport x →
        leftDoubledJoinVertex v ∈
          FairDivision.Topology.finiteSimplexSupport w.1 := by
      intro v hv
      have hpos := (FairDivision.Topology.mem_finiteSimplexSupport_iff x v).1 hv
      have hpos' : 0 < w.1.1 (leftDoubledJoinVertex v) := by
        exact (div_pos_iff_of_pos_right h).mp hpos
      exact (FairDivision.Topology.mem_finiteSimplexSupport_iff w.1 _).2 hpos'
    exact hw.2 (Fin.castAdd m i) g g'
      (hcoord (i, g) hg) (hcoord (i, g') hg')

/-- A positive second-block restriction is still a universal-join point. -/
noncomputable def rightDoubledJoinRealization
    {m : ℕ} {G : Type*} [Fintype G]
    (w : simplicialRealization (universalJoinComplex (m + m) G))
    (h : 0 < rightDoubledJoinMass w.1) :
    simplicialRealization (universalJoinComplex m G) := by
  classical
  let x := rightDoubledJoinRestrict w.1 h
  refine ⟨x, ?_⟩
  change IsUniversalJoinFace (FairDivision.Topology.finiteSimplexSupport x)
  constructor
  · exact FairDivision.Topology.finiteSimplexSupport_nonempty x
  · intro i g g' hg hg'
    have hw : IsUniversalJoinFace
        (FairDivision.Topology.finiteSimplexSupport w.1) := w.2
    have hcoord : ∀ v : Fin m × G,
        v ∈ FairDivision.Topology.finiteSimplexSupport x →
        rightDoubledJoinVertex v ∈
          FairDivision.Topology.finiteSimplexSupport w.1 := by
      intro v hv
      have hpos := (FairDivision.Topology.mem_finiteSimplexSupport_iff x v).1 hv
      have hpos' : 0 < w.1.1 (rightDoubledJoinVertex v) := by
        exact (div_pos_iff_of_pos_right h).mp hpos
      exact (FairDivision.Topology.mem_finiteSimplexSupport_iff w.1 _).2 hpos'
    exact hw.2 (Fin.natAdd m i) g g'
      (hcoord (i, g) hg) (hcoord (i, g') hg')

end FairDivision.Topology.Volovikov
