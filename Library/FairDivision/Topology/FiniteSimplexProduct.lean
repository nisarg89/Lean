import FairDivision.Topology.FiniteSimplexSupportMap
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Actual independent products of finite probability vectors

The manuscript combines child lotteries by their independent product.
Use Mathlib's finite product-of-sums identity directly for normalization and
coordinate marginals; no measure-theoretic product construction is needed
for these finite real probability vectors.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology

open scoped BigOperators Classical

/-- The literal independent weight is the product of the child weights. -/
def finiteSimplexProduct {ι V : Type*} [Fintype ι] [Fintype V]
    (μ : ι→stdSimplex ℝ V) : stdSimplex ℝ (ι→V) :=
  ⟨fun x=>∏i, (μ i).1 (x i),
    fun x=>Finset.prod_nonneg (fun i _=>(μ i).2.1 (x i)),by
      rw [←Fintype.prod_sum]
      simp only [fun i=>(μ i).2.2,Finset.prod_const_one]⟩

@[simp] theorem finiteSimplexProduct_apply {ι V : Type*} [Fintype ι] [Fintype V]
    (μ : ι→stdSimplex ℝ V) (x : ι→V) :
    (finiteSimplexProduct μ).1 x=∏i,(μ i).1 (x i) := rfl

/-- Every coordinate of a positive product outcome is a positive child
outcome; no unsupported outcome enters the combined allocation. -/
theorem finiteSimplexProduct_support {ι V : Type*} [Fintype ι] [Fintype V]
    (μ : ι→stdSimplex ℝ V) {x : ι→V}
    (hx : x∈finiteSimplexSupport (finiteSimplexProduct μ)) :
    ∀i,x i∈finiteSimplexSupport (μ i) := by
  have hPos:= (mem_finiteSimplexSupport_iff _ x).mp hx
  have hNonzero : (∏i,(μ i).1 (x i))≠0 := ne_of_gt hPos
  intro i
  apply (mem_finiteSimplexSupport_iff _ _).mpr
  have hChild : (μ i).1 (x i)≠0 := (Finset.prod_ne_zero_iff.mp hNonzero) i (Finset.mem_univ i)
  exact lt_of_le_of_ne ((μ i).2.1 (x i)) (Ne.symm hChild)

/-- The support of the independent product is exactly the Cartesian
product of the child supports. This includes an empty index type: its one
empty tuple has product weight one. -/
@[simp] theorem mem_finiteSimplexProduct_support_iff
    {ι V : Type*} [Fintype ι] [Fintype V]
    (μ : ι → stdSimplex ℝ V) (x : ι → V) :
    x ∈ finiteSimplexSupport (finiteSimplexProduct μ) ↔
      ∀ i, x i ∈ finiteSimplexSupport (μ i) := by
  constructor
  · exact fun hx => finiteSimplexProduct_support μ hx
  · intro hx
    apply (mem_finiteSimplexSupport_iff _ _).mpr
    change 0 < ∏ i, (μ i).1 (x i)
    exact Finset.prod_pos (fun i _ => (mem_finiteSimplexSupport_iff _ _).mp (hx i))

/-- The ith-coordinate expectation of the actual product vector equals
that child's expectation. Every other probability factor sums to one. -/
theorem finiteSimplexProduct_expectation {ι V : Type*} [Fintype ι] [Fintype V]
    (μ : ι→stdSimplex ℝ V) (i : ι) (f : V→ℝ) :
    (∑x : ι→V,(finiteSimplexProduct μ).1 x*f (x i))=
      ∑v : V,(μ i).1 v*f v := by
  calc
    (∑x : ι→V,(finiteSimplexProduct μ).1 x*f (x i))=
        ∑x : ι→V,∏j,(μ j).1 (x j)*(if j=i then f (x j) else 1) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.prod_mul_distrib]
      simp [finiteSimplexProduct]
    _=∏j,∑v : V,(μ j).1 v*(if j=i then f v else 1) :=
      (Fintype.prod_sum (κ := fun _ : ι => V)
        (fun (j : ι) (v : V) => (μ j).1 v * (if j = i then f v else 1))).symm
    _=∑v : V,(μ i).1 v*f v := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hji
        simp only [if_neg hji,mul_one,(μ j).2.2]
      · simp

/-- Finite pushforward preserves expectation. This is the literal fiber
sum defining `stdSimplex.map`, using Mathlib's existing fiberwise sum theorem. -/
theorem finiteSimplexMap_expectation {V W : Type*} [Fintype V] [Fintype W]
    (μ : stdSimplex ℝ V) (e : V→W) (f : W→ℝ) :
    (∑w : W,(stdSimplex.map e μ).1 w*f w)=∑v : V,μ.1 v*f (e v) := by
  change (∑w : W,FunOnFinite.linearMap ℝ ℝ e μ.1 w*f w)=_
  simp_rw [FunOnFinite.linearMap_apply_apply]
  calc
    (∑w : W,(∑v with e v=w,μ.1 v)*f w)=
        ∑w : W,∑v with e v=w,μ.1 v*f (e v) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _=∑v : V,μ.1 v*f (e v) := Finset.sum_fiberwise Finset.univ e _

end FairDivision.Topology
