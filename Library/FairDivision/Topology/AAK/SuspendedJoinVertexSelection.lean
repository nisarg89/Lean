import FairDivision.Topology.AAK.SuspendedJoinPoleHomotopy
import Mathlib.Data.Finset.Max
import Mathlib.Order.WithBot

/-!
# Equivariant large-coordinate selection in the actual suspended target

This adapts the imported DKGM `JoinGeom.vtxSel` construction, retaining its
least-good-color rule. The poles share one color and cannot both have
positive mass. Every face uses at most d+1 colors. Hence the selected vertex
has mass at least 1/(d+1), is unique among positive vertices of its color,
and commutes with every cyclic label translation. No source orbit choice
or simplicial approximation theorem is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.ZeroFreeBipyramid

open FairDivision.Topology
open scoped BigOperators Classical

variable {d : ℕ} {G : Type*} [Fintype G]

/-- Order the pole color first, followed by the finite join colors. -/
local instance : LinearOrder (Option (Fin d)) :=
  inferInstanceAs (LinearOrder (WithBot (Fin d)))

/-- Some coordinate of a suspended-join point has the sharp face-size lower
bound. Its support has size at most d+1 even if the ambient vertex set is larger. -/
theorem exists_large_suspension_coordinate (x : SuspensionRealization d G) :
    ∃ v : SuspensionVertex d G, 1 / (d + 1 : ℝ) ≤ x.1.1 v := by
  by_contra h
  push_neg at h
  let S := finiteSimplexSupport x.1
  have hnonempty : S.Nonempty := finiteSimplexSupport_nonempty _
  have hsum : ∑ v ∈ S, x.1.1 v = 1 := by
    calc
      ∑ v ∈ S, x.1.1 v = ∑ v : SuspensionVertex d G, x.1.1 v := by
        apply Finset.sum_subset (Finset.subset_univ S)
        intro v _ hv
        exact le_antisymm (le_of_not_gt (by simpa [S] using hv)) (x.1.2.1 v)
      _ = 1 := x.1.2.2
  have hlt := Finset.sum_lt_sum_of_nonempty hnonempty (fun v _ => h v)
  have hcard : (S.card : ℝ) ≤ d + 1 := by
    exact_mod_cast suspensionJoinFace_card_le x.2
  have hupper : (S.card : ℝ) * (1 / (d + 1 : ℝ)) ≤ 1 := by
    calc
      (S.card : ℝ) * (1 / (d + 1 : ℝ)) ≤ (d + 1 : ℝ) * (1 / (d + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 1 := by field_simp
  simp only [Finset.sum_const, nsmul_eq_mul, hsum] at hlt
  linarith

def largeSuspensionColors (x : SuspensionRealization d G) : Finset (Option (Fin d)) :=
  Finset.univ.filter fun c => ∃ v, suspensionColor v = c ∧ 1 / (d + 1 : ℝ) ≤ x.1.1 v

theorem largeSuspensionColors_nonempty (x : SuspensionRealization d G) :
    (largeSuspensionColors x).Nonempty := by
  obtain ⟨v, hv⟩ := exists_large_suspension_coordinate x
  refine ⟨suspensionColor v, ?_⟩
  simp only [largeSuspensionColors, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨v, rfl, hv⟩

def selectedSuspensionColor (x : SuspensionRealization d G) : Option (Fin d) :=
  (largeSuspensionColors x).min' (largeSuspensionColors_nonempty x)

theorem selectedSuspensionColor_spec (x : SuspensionRealization d G) :
    ∃ v, suspensionColor v = selectedSuspensionColor x ∧
      1 / (d + 1 : ℝ) ≤ x.1.1 v := by
  have h := Finset.min'_mem (largeSuspensionColors x) (largeSuspensionColors_nonempty x)
  simpa only [largeSuspensionColors, Finset.mem_filter, Finset.mem_univ, true_and,
    selectedSuspensionColor] using h

def suspensionVertexSelection (x : SuspensionRealization d G) : SuspensionVertex d G :=
  Classical.choose (selectedSuspensionColor_spec x)

theorem suspensionVertexSelection_color (x : SuspensionRealization d G) :
    suspensionColor (suspensionVertexSelection x) = selectedSuspensionColor x :=
  (Classical.choose_spec (selectedSuspensionColor_spec x)).1

theorem suspensionVertexSelection_spec (x : SuspensionRealization d G) :
    1 / (d + 1 : ℝ) ≤ x.1.1 (suspensionVertexSelection x) :=
  (Classical.choose_spec (selectedSuspensionColor_spec x)).2

theorem suspensionVertexSelection_positive (x : SuspensionRealization d G) :
    0 < x.1.1 (suspensionVertexSelection x) :=
  lt_of_lt_of_le (by positivity) (suspensionVertexSelection_spec x)

/-- Selection at either exact pole is the pole itself. -/
@[simp] theorem suspensionVertexSelection_pole (b : Bool) :
    suspensionVertexSelection (suspensionPole d G b) = pole b := by
  have h := suspensionVertexSelection_positive (suspensionPole d G b)
  change 0 < (Pi.single (pole b) (1 : ℝ) : SuspensionVertex d G → ℝ)
    (suspensionVertexSelection (suspensionPole d G b)) at h
  simp only [Pi.single_apply] at h
  split_ifs at h with he
  · exact he
  · norm_num at h

variable (p : ℕ) [Fact p.Prime]

@[simp] theorem suspensionColor_translate (a : ZMod p)
    (v : SuspensionVertex (p - 1) (ZMod p)) :
    suspensionColor (suspensionPermutation p a v) = suspensionColor v := by
  cases v <;> rfl

theorem largeSuspensionColors_translate (a : ZMod p)
    (x : SuspensionRealization (p - 1) (ZMod p)) :
    largeSuspensionColors (suspensionRelabel p a x) = largeSuspensionColors x := by
  ext c
  simp only [largeSuspensionColors, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv, hw⟩
    refine ⟨(suspensionPermutation p a).symm v, ?_, ?_⟩
    · have hc := suspensionColor_translate p a ((suspensionPermutation p a).symm v)
      simp only [Equiv.apply_symm_apply] at hc
      exact hc.symm.trans hv
    · have he := simplex_map_equiv_apply (suspensionPermutation p a) x.1
        ((suspensionPermutation p a).symm v)
      change _ ≤ (stdSimplex.map (suspensionPermutation p a) x.1).1 v at hw
      simp only [Equiv.apply_symm_apply] at he
      exact he ▸ hw
  · rintro ⟨v, hv, hw⟩
    refine ⟨suspensionPermutation p a v, (suspensionColor_translate p a v).trans hv, ?_⟩
    change _ ≤ (stdSimplex.map (suspensionPermutation p a) x.1).1 _
    rw [simplex_map_equiv_apply]
    exact hw

theorem selectedSuspensionColor_translate (a : ZMod p)
    (x : SuspensionRealization (p - 1) (ZMod p)) :
    selectedSuspensionColor (suspensionRelabel p a x) = selectedSuspensionColor x := by
  simp only [selectedSuspensionColor, largeSuspensionColors_translate p a x]

/-- Exact equivariance of the actual least-color selector. -/
theorem suspensionVertexSelection_translate (a : ZMod p)
    (x : SuspensionRealization (p - 1) (ZMod p)) :
    suspensionVertexSelection (suspensionRelabel p a x) =
      suspensionTranslate a (suspensionVertexSelection x) := by
  rw [← suspensionPermutation_apply p a (suspensionVertexSelection x)]
  let y := suspensionRelabel p a x
  apply suspensionColor_injOn y.2
  · exact (mem_finiteSimplexSupport_iff _ _).2 (suspensionVertexSelection_positive y)
  · apply (mem_finiteSimplexSupport_iff _ _).2
    change 0 < (stdSimplex.map (suspensionPermutation p a) x.1).1
      (suspensionPermutation p a (suspensionVertexSelection x))
    rw [simplex_map_equiv_apply]
    exact suspensionVertexSelection_positive x
  · rw [suspensionVertexSelection_color, selectedSuspensionColor_translate]
    exact ((suspensionColor_translate p a (suspensionVertexSelection x)).trans
      (suspensionVertexSelection_color x)).symm

/-- Every vertex selected at a sufficiently close point occurs in the
actual support of the reference point. This is the entire local simplicial
approximation argument, using the same half-threshold estimate as DKGM. -/
theorem suspensionVertexSelection_mem_of_close
    (x y : SuspensionRealization (p - 1) (ZMod p))
    (hclose : ∀ v, |x.1.1 v - y.1.1 v| < 1 / (2 * (p : ℝ))) :
    suspensionVertexSelection y ∈ finiteSimplexSupport x.1 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hsize : ((p - 1 : ℕ) : ℝ) + 1 = p := by
    exact_mod_cast (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp.ne'))
  have hlarge := suspensionVertexSelection_spec y
  rw [hsize] at hlarge
  have h := (abs_lt.mp (hclose (suspensionVertexSelection y))).1
  apply (mem_finiteSimplexSupport_iff _ _).2
  have hpos : (0 : ℝ) < 1 / (2 * (p : ℝ)) := by positivity
  have hsplit : (1 : ℝ) / p = 2 * (1 / (2 * (p : ℝ))) := by field_simp
  rw [hsplit] at hlarge
  linarith

end FairDivision.Topology.AAK.ZeroFreeBipyramid
