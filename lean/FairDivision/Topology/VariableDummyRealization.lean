import FairDivision.Topology.FiniteSimplexSupport
import FairDivision.Topology.VariableDummySaturation
import FairDivision.Topology.UnlabeledLottery

/-!
# Probability-simplex realization of the variable-size auxiliary complex

This realization is the topological space used by the connectivity induction.
Its finite support is a face of the variable-size complex. A vertex map that
preserves faces induces a continuous map of the realization.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Positive support of a probability vector on variable-size profiles. -/
noncomputable def variableLotterySupport {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (lot : stdSimplex ℝ (VariableUnlabeledVertex k m D r c)) :
    Finset (VariableUnlabeledVertex k m D r c) :=
  finiteSimplexSupport lot

/-- Geometric realization in the finite probability simplex. -/
def variableLotterySpace (k m : ℕ) (D : Finset (Fin m))
    (r c : Fin k → ℕ) :
    Set (stdSimplex ℝ (VariableUnlabeledVertex k m D r c)) :=
  {lot | IsVariableUnlabeledFamily (variableLotterySupport lot)}

/-- Every probability vector has nonempty positive support. -/
theorem variableLotterySupport_nonempty {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (lot : stdSimplex ℝ (VariableUnlabeledVertex k m D r c)) :
    (variableLotterySupport lot).Nonempty := by
  exact finiteSimplexSupport_nonempty lot

/-- Realization membership is positive-support face membership. -/
theorem variableLottery_iff_support_face {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (lot : stdSimplex ℝ (VariableUnlabeledVertex k m D r c)) :
    lot ∈ variableLotterySpace k m D r c ↔
      variableLotterySupport lot ∈ variableDummyComplex k m D r c := by
  change IsVariableUnlabeledFamily (variableLotterySupport lot) ↔
    (variableLotterySupport lot).Nonempty ∧
      IsVariableUnlabeledFamily (variableLotterySupport lot)
  exact ⟨fun h => ⟨variableLotterySupport_nonempty lot, h⟩,
    fun h => h.2⟩

/-- Every positive weight in the pushforward came from a positive source
weight. This holds even when the vertex map is not injective. -/
theorem variableLotterySupport_map_subset {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D r c)
    (lot : stdSimplex ℝ (VariableUnlabeledVertex k m D r c)) :
    variableLotterySupport (stdSimplex.map f lot) ⊆
      (variableLotterySupport lot).image f := by
  classical
  intro q hq
  have hpos : 0 < (stdSimplex.map f lot).1 q :=
    (Finset.mem_filter.mp hq).2
  change 0 < FunOnFinite.linearMap ℝ ℝ f lot.1 q at hpos
  rw [FunOnFinite.linearMap_apply_apply] at hpos
  obtain ⟨p, hp, hppos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun p _ => lot.2.1 p)).mp hpos
  exact Finset.mem_image.mpr
    ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hppos⟩,
      (Finset.mem_filter.mp hp).2⟩

/-- A face-preserving vertex map acts on the variable-size realization. -/
theorem variableLotteryMap_mem {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D r c)
    (hFace : ∀ S : Finset (VariableUnlabeledVertex k m D r c),
      IsVariableUnlabeledFamily S → IsVariableUnlabeledFamily (S.image f))
    (lot : stdSimplex ℝ (VariableUnlabeledVertex k m D r c))
    (hlot : lot ∈ variableLotterySpace k m D r c) :
    stdSimplex.map f lot ∈ variableLotterySpace k m D r c := by
  exact variableUnlabeled_mono (variableLotterySupport_map_subset f lot)
    (hFace (variableLotterySupport lot) hlot)

/-- The ambient simplex pushforward is continuous. -/
theorem variableLotteryMap_continuous {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D r c) :
    Continuous (stdSimplex.map f :
      stdSimplex ℝ (VariableUnlabeledVertex k m D r c) →
      stdSimplex ℝ (VariableUnlabeledVertex k m D r c)) := by
  exact stdSimplex.continuous_map f

end FairDivision.Topology
