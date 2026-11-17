import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_TableCoverage

private def CellChain : List MassCell → ℚ → ℚ → Bool
  | [], lo, hi => decide (lo = hi)
  | c::cs, lo, hi => decide (c.lo = lo) && CellChain cs c.hi hi

private theorem CellChain.cover (cells : List MassCell) (lo hi : ℚ)
    (hc : CellChain cells lo hi = true) (p : ℝ) (hlo : (lo : ℝ) ≤ p) (hhi : p < (hi : ℝ)) :
    ∃ c ∈ cells, (c.lo : ℝ) ≤ p ∧ p < (c.hi : ℝ) := by
  induction cells generalizing lo with
  | nil =>
    have heq : lo = hi := of_decide_eq_true hc
    subst lo
    exact False.elim ((not_lt_of_ge hlo) hhi)
  | cons c cs ih =>
    have hh : decide (c.lo = lo) = true ∧ CellChain cs c.hi hi = true := by
      simpa only [CellChain,Bool.and_eq_true_iff] using hc
    have hc : c.lo = lo := of_decide_eq_true hh.1
    have ht := hh.2
    by_cases hp : p < (c.hi : ℝ)
    · refine ⟨c,by simp,?_,hp⟩
      simpa [hc] using hlo
    · obtain ⟨d,hd,hld,hhd⟩ := ih c.hi ht (le_of_not_gt hp)
      exact ⟨d,List.mem_cons_of_mem _ hd,hld,hhd⟩

theorem from_children (h : Needs) : Statement := by
  refine ⟨?_,?_,?_⟩
  · intro p hp
    by_cases h8 : p ≤ (3/100 : ℝ)
    · refine Set.mem_iUnion.mpr ⟨8,?_⟩
      norm_num [root,rootLows,rootHighs]
      exact ⟨hp.1,h8⟩
    by_cases h7 : p ≤ (7/50 : ℝ)
    · refine Set.mem_iUnion.mpr ⟨7,?_⟩
      norm_num [root,rootLows,rootHighs]
      constructor <;> linarith
    by_cases h6 : p ≤ (21/100 : ℝ)
    · refine Set.mem_iUnion.mpr ⟨6,?_⟩
      norm_num [root,rootLows,rootHighs]
      constructor <;> linarith
    by_cases h5 : p ≤ (13/50 : ℝ)
    · refine Set.mem_iUnion.mpr ⟨5,?_⟩
      norm_num [root,rootLows,rootHighs]
      constructor <;> linarith
    by_cases h4 : p ≤ (3/10 : ℝ)
    · refine Set.mem_iUnion.mpr ⟨4,?_⟩
      norm_num [root,rootLows,rootHighs]
      constructor <;> linarith
    by_cases h3 : p ≤ (7/20 : ℝ)
    · refine Set.mem_iUnion.mpr ⟨3,?_⟩
      norm_num [root,rootLows,rootHighs]
      constructor <;> linarith
    by_cases h2 : p ≤ (21/50 : ℝ)
    · refine Set.mem_iUnion.mpr ⟨2,?_⟩
      norm_num [root,rootLows,rootHighs]
      constructor <;> linarith
    by_cases h1 : p ≤ (49/100 : ℝ)
    · refine Set.mem_iUnion.mpr ⟨1,?_⟩
      norm_num [root,rootLows,rootHighs]
      constructor <;> linarith
    · refine Set.mem_iUnion.mpr ⟨0,?_⟩
      norm_num [root,rootLows,rootHighs,bStar] at hp ⊢
      constructor <;> linarith
  · intro j
    refine ⟨isClosed_Icc,ordConnected_Icc,?_⟩
    intro p hp
    fin_cases j <;> norm_num [root,rootLows,rootHighs,bStar] at hp ⊢ <;>
      constructor <;> linarith
  · intro p hp
    have hchain : CellChain fixedCells 0 1 = true := by decide +kernel
    exact CellChain.cover fixedCells 0 1 hchain p (by simpa using hp.1.le) (by simpa using hp.2)

#print axioms from_children
end MetricDistortion.Contracts.Numerics_TableCoverage
