import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Compact

/-!
# Continuous maximum over a moving compact set

This is the compact-correspondence maximum principle needed for the BF
manuscript's spherical-cap extension. It separates continuity of the maximum
from the geometric work of proving upper and lower hemicontinuity of the caps.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- A continuous real-valued function has a continuous maximum over a
nonempty compact-valued correspondence that is both upper and lower
hemicontinuous. -/
theorem continuous_sSup_image_of_hemicontinuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (K : X → Set Y)
    (hCompact : ∀ x, IsCompact (K x))
    (hNonempty : ∀ x, (K x).Nonempty)
    (hUpper : UpperHemicontinuous K)
    (hLower : LowerHemicontinuous K)
    (f : Y → ℝ) (hf : Continuous f) :
    Continuous (fun x => sSup (f '' K x)) := by
  let M : X → ℝ := fun x => sSup (f '' K x)
  have hMax (x : X) :
      ∃ y ∈ K x, M x = f y ∧ ∀ z ∈ K x, f z ≤ M x := by
    obtain ⟨y, hy, hEq, hGe⟩ :=
      (hCompact x).exists_sSup_image_eq_and_ge
        (hNonempty x) hf.continuousOn
    refine ⟨y, hy, hEq, ?_⟩
    intro z hz
    calc
      f z ≤ f y := hGe z hz
      _ = M x := hEq.symm
  have hLowerSem : LowerSemicontinuous M := by
    rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro a
    have hEq : M ⁻¹' Set.Ioi a =
        {x | (K x ∩ f ⁻¹' Set.Ioi a).Nonempty} := by
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, hMy, _⟩ := hMax x
        exact ⟨y, hy, by simpa only [Set.mem_preimage, Set.mem_Ioi,
          ← hMy] using hx⟩
      · rintro ⟨y, hy, hyf⟩
        obtain ⟨z, hz, _, hGe⟩ := hMax x
        exact lt_of_lt_of_le hyf (hGe y hy)
    rw [hEq]
    exact lowerHemicontinuous_iff_isOpen_inter_nonempty.mp hLower
      (f ⁻¹' Set.Ioi a) (hf.isOpen_preimage (Set.Ioi a) isOpen_Ioi)
  have hUpperSem : UpperSemicontinuous M := by
    rw [upperSemicontinuous_iff_isOpen_preimage]
    intro a
    have hEq : M ⁻¹' Set.Iio a =
        K ⁻¹' Set.Iic (f ⁻¹' Set.Iio a) := by
      ext x
      constructor
      · intro hx y hy
        obtain ⟨_, _, _, hGe⟩ := hMax x
        exact lt_of_le_of_lt (hGe y hy) hx
      · intro hx
        obtain ⟨y, hy, hMy, _⟩ := hMax x
        simpa only [Set.mem_preimage, Set.mem_Iio, hMy] using hx hy
    rw [hEq]
    exact upperHemicontinuous_iff_isOpen_preimage_Iic.mp hUpper
      (f ⁻¹' Set.Iio a) (hf.isOpen_preimage (Set.Iio a) isOpen_Iio)
  exact continuous_iff_lower_upperSemicontinuous.mpr
    ⟨hLowerSem, hUpperSem⟩

end FairDivision.Topology
