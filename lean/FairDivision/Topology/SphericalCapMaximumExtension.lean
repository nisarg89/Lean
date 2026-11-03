import FairDivision.Topology.SphericalCapLower
import FairDivision.Topology.SphericalCapUpper
import FairDivision.Topology.ContinuousCompactMaximum

/-!
# Coordinatewise-maximum extension from a sphere to its ball

For a continuous vector-valued boundary map, take each output coordinate's
maximum on the moving spherical cap. The result is continuous, agrees with
the original map on the boundary, and every output vector is the
coordinatewise maximum of at most one chosen boundary vector per coordinate.
-/

set_option autoImplicit false

namespace FairDivision.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E]
variable {n : ℕ}

/-- The capwise coordinate maximum of a sphere-boundary map. -/
noncomputable def sphericalCapMaximum (f : UnitSphere E → Fin n → ℝ)
    (x : ClosedUnitBall E) : Fin n → ℝ :=
  fun i => sSup ((fun y : UnitSphere E => f y i) '' sphericalCap x)

theorem continuous_sphericalCapMaximum
    (hRank : 1 < Module.rank ℝ E)
    (hUnit : Nonempty (UnitSphere E))
    (f : UnitSphere E → Fin n → ℝ) (hf : Continuous f) :
    Continuous (sphericalCapMaximum f) := by
  apply continuous_pi
  intro i
  exact continuous_sSup_image_of_hemicontinuous
    (sphericalCap (E := E))
    (fun x => sphericalCap_isCompact x)
    (fun x => sphericalCap_nonempty hUnit x)
    sphericalCap_upperHemicontinuous
    (sphericalCap_lowerHemicontinuous hRank)
    (fun y => f y i) ((continuous_apply i).comp hf)

theorem sphericalCapMaximum_boundary
    (f : UnitSphere E → Fin n → ℝ)
    (x : ClosedUnitBall E) (hx : ‖(x : E)‖ = 1) :
    sphericalCapMaximum f x = f (⟨(x : E), hx⟩ : UnitSphere E) := by
  funext i
  simp [sphericalCapMaximum, sphericalCap_eq_singleton_of_boundary x hx]

theorem sphericalCapMaximum_attained
    (hUnit : Nonempty (UnitSphere E))
    (f : UnitSphere E → Fin n → ℝ) (hf : Continuous f)
    (x : ClosedUnitBall E) (i : Fin n) :
    ∃ y ∈ sphericalCap x,
      sphericalCapMaximum f x i = f y i ∧
        ∀ z ∈ sphericalCap x, f z i ≤ sphericalCapMaximum f x i := by
  obtain ⟨y, hy, hEq, hGe⟩ :=
    (sphericalCap_isCompact x).exists_sSup_image_eq_and_ge
      (sphericalCap_nonempty hUnit x)
      (((continuous_apply i).comp hf).continuousOn)
  refine ⟨y, hy, hEq, ?_⟩
  intro z hz
  calc
    f z i ≤ f y i := hGe z hz
    _ = sphericalCapMaximum f x i := hEq.symm

/-- The witness `w i` supplies coordinate `i`'s maximum, and no witness
exceeds the extension value in any coordinate. Hence the extension is the
coordinatewise maximum of the `n` boundary vectors `f (w i)`. -/
theorem sphericalCapMaximum_finite_witness
    (hUnit : Nonempty (UnitSphere E))
    (f : UnitSphere E → Fin n → ℝ) (hf : Continuous f)
    (x : ClosedUnitBall E) :
    ∃ w : Fin n → UnitSphere E,
      (∀ i, w i ∈ sphericalCap x) ∧
      (∀ i, sphericalCapMaximum f x i = f (w i) i) ∧
      (∀ i j, f (w j) i ≤ sphericalCapMaximum f x i) := by
  classical
  have h : ∀ i : Fin n, ∃ y : UnitSphere E,
      y ∈ sphericalCap x ∧
      sphericalCapMaximum f x i = f y i ∧
      ∀ z ∈ sphericalCap x, f z i ≤ sphericalCapMaximum f x i :=
    sphericalCapMaximum_attained hUnit f hf x
  choose w hw using h
  refine ⟨w, (fun i => (hw i).1), (fun i => (hw i).2.1), ?_⟩
  intro i j
  exact (hw i).2.2 (w j) (hw j).1

/-- Literal finite-set form of the manuscript's “at most n boundary
vectors” property. The SAME set S supplies every coordinate maximum, and
all its points lie in the SAME cap used to define the extension. -/
theorem sphericalCapMaximum_finite_boundary_set
    (hN : 0 < n) (hUnit : Nonempty (UnitSphere E))
    (f : UnitSphere E → Fin n → ℝ) (hf : Continuous f)
    (x : ClosedUnitBall E) :
    ∃ (S : Finset (UnitSphere E)) (hS : S.Nonempty),
      S.card ≤ n ∧ (∀ y ∈ S, y ∈ sphericalCap x) ∧
        ∀ i, sphericalCapMaximum f x i = S.sup' hS (fun y => f y i) := by
  classical
  obtain ⟨w, hw, hAttain, hDom⟩ :=
    sphericalCapMaximum_finite_witness hUnit f hf x
  let S : Finset (UnitSphere E) := Finset.univ.image w
  have hMem (i : Fin n) : w i ∈ S :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hS : S.Nonempty := ⟨w ⟨0, hN⟩, hMem ⟨0, hN⟩⟩
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · calc
      S.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  · intro y hy
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hy
    exact hw i
  · intro i
    apply le_antisymm
    · rw [hAttain i]
      exact Finset.le_sup' (fun y => f y i) (hMem i)
    · apply Finset.sup'_le hS
      intro y hy
      obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hy
      exact hDom i j

end FairDivision.Topology
