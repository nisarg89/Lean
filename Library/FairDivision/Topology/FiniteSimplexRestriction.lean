import FairDivision.Topology.FiniteSimplexSupport
import Mathlib.Algebra.BigOperators.Field

/-!
# Restriction of a finite probability vector to positive-mass vertices

This is the finite-index version of `StdSimplex.restrict`, for the
`stdSimplex` representation used throughout both certificates. It supports
open-star deformation retractions of barycentrically subdivided complexes.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology

/-- Total probability mass on a finite vertex set. -/
def finiteSimplexMass {V : Type*} [Fintype V]
    (P : Finset V) (w : stdSimplex ℝ V) : ℝ :=
  ∑ v ∈ P, w.1 v

/-- A positive coordinate in `P` gives positive mass on `P`. -/
theorem finiteSimplexMass_pos_of_mem {V : Type*} [Fintype V]
    (P : Finset V) (w : stdSimplex ℝ V)
    {v : V} (hvP : v ∈ P) (hv : 0 < w.1 v) :
    0 < finiteSimplexMass P w := by
  classical
  unfold finiteSimplexMass
  exact Finset.sum_pos' (fun u _ => w.2.1 u) ⟨v, hvP, hv⟩

/-- Mass varies continuously with the probability vector. -/
theorem finiteSimplexMass_continuous {V : Type*} [Fintype V]
    (P : Finset V) : Continuous (finiteSimplexMass P) := by
  unfold finiteSimplexMass
  apply continuous_finset_sum
  intro v hv
  exact (continuous_apply v).comp continuous_subtype_val

/-- Normalize the weights in `P`, assuming their total mass is positive. -/
noncomputable def finiteSimplexRestrict {V : Type*} [Fintype V]
    (P : Finset V)
    (z : {w : stdSimplex ℝ V // 0 < finiteSimplexMass P w}) :
    stdSimplex ℝ V := by
  classical
  refine ⟨fun v => if v ∈ P then z.1.1 v / finiteSimplexMass P z.1 else 0,
    ?_, ?_⟩
  · intro v
    dsimp
    split_ifs
    · exact div_nonneg (z.1.2.1 v) z.2.le
    · exact le_refl _
  · have hsum :
        (∑ v : V, if v ∈ P then z.1.1 v / finiteSimplexMass P z.1 else 0) =
          (∑ v ∈ P, z.1.1 v) / finiteSimplexMass P z.1 := by
      simp [Finset.sum_ite, ← Finset.sum_div]
    rw [hsum]
    exact div_self (ne_of_gt z.2)

/-- A selected coordinate is positive after restriction exactly when it was
positive beforehand. -/
theorem finiteSimplexRestrict_pos_iff {V : Type*} [Fintype V]
    (P : Finset V)
    (z : {w : stdSimplex ℝ V // 0 < finiteSimplexMass P w})
    (v : V) :
    0 < (finiteSimplexRestrict P z).1 v ↔
      v ∈ P ∧ 0 < z.1.1 v := by
  classical
  by_cases hvP : v ∈ P
  · simp [finiteSimplexRestrict, hvP, div_pos_iff_of_pos_right z.2]
  · simp [finiteSimplexRestrict, hvP]

/-- Restriction erases precisely the coordinates outside `P`. -/
theorem finiteSimplexRestrict_support_subset {V : Type*} [Fintype V]
    (P : Finset V)
    (z : {w : stdSimplex ℝ V // 0 < finiteSimplexMass P w}) :
    ∀ v ∈ finiteSimplexSupport (finiteSimplexRestrict P z),
      v ∈ finiteSimplexSupport z.1 ∧ v ∈ P := by
  classical
  intro v hv
  have hpos := (mem_finiteSimplexSupport_iff _ v).1 hv
  by_cases hvP : v ∈ P
  · have hweight : 0 < z.1.1 v := by
      have hdiv : 0 < z.1.1 v / finiteSimplexMass P z.1 := by
        simpa [finiteSimplexRestrict, hvP] using hpos
      exact (div_pos_iff_of_pos_right z.2).mp hdiv
    exact ⟨(mem_finiteSimplexSupport_iff _ v).2 hweight, hvP⟩
  · simp [finiteSimplexRestrict, hvP] at hpos

/-- Restriction fixes a vector already supported on the selected vertices. -/
theorem finiteSimplexRestrict_eq_self {V : Type*} [Fintype V]
    (P : Finset V)
    (z : {w : stdSimplex ℝ V // 0 < finiteSimplexMass P w})
    (hsub : finiteSimplexSupport z.1 ⊆ P) :
    finiteSimplexRestrict P z = z.1 := by
  classical
  have hzero : ∀ v : V, v ∉ P → z.1.1 v = 0 := by
    intro v hvP
    by_contra hne
    have hpos : 0 < z.1.1 v := lt_of_le_of_ne (z.1.2.1 v) (Ne.symm hne)
    exact hvP (hsub ((mem_finiteSimplexSupport_iff z.1 v).2 hpos))
  have hmass : finiteSimplexMass P z.1 = 1 := by
    calc
      finiteSimplexMass P z.1 = ∑ v : V, z.1.1 v := by
        unfold finiteSimplexMass
        exact (Finset.sum_subset (Finset.subset_univ P)
          (fun v _ hvP => hzero v hvP))
      _ = 1 := z.1.2.2
  apply Subtype.ext
  funext v
  by_cases hvP : v ∈ P
  · simp [finiteSimplexRestrict, hvP, hmass]
  · simp [finiteSimplexRestrict, hvP, hzero v hvP]

/-- Restriction depends continuously on the point in the positive-mass domain. -/
theorem finiteSimplexRestrict_continuous {V : Type*} [Fintype V]
    (P : Finset V) :
    Continuous (finiteSimplexRestrict P) := by
  classical
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  by_cases hvP : v ∈ P
  · have hv : Continuous (fun z : {w : stdSimplex ℝ V // 0 < finiteSimplexMass P w} =>
        z.1.1 v) :=
      (continuous_apply v).comp (continuous_subtype_val.comp continuous_subtype_val)
    have hm : Continuous (fun z : {w : stdSimplex ℝ V // 0 < finiteSimplexMass P w} =>
        finiteSimplexMass P z.1) :=
      (finiteSimplexMass_continuous P).comp continuous_subtype_val
    have hc : Continuous (fun z :
        {w : stdSimplex ℝ V // 0 < finiteSimplexMass P w} =>
        z.1.1 v / finiteSimplexMass P z.1) := by
      convert hv.div hm (fun z => ne_of_gt z.2) using 1
    simpa [finiteSimplexRestrict, hvP] using hc
  · simpa [finiteSimplexRestrict, hvP] using
      (continuous_const : Continuous
        (fun _ : {w : stdSimplex ℝ V // 0 < finiteSimplexMass P w} => (0 : ℝ)))

end FairDivision.Topology
