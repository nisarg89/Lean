import FairDivision.Topology.NerveConnectivity.GluingReduction
import FairDivision.Topology.NerveConnectivity.NullHomotopyZero

/-!
# Operational finite-cover connectivity reduction

The BF topology route uses `NullConnectedSet` consistently, including through
deformation retractions. Its finite-cover theorem is derived from the one
generic induction in `GluingReduction.lean`; positive-dimensional binary
gluing remains an explicit unproved input in this module.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- The binary gluing obligation in the cube-sphere nullhomotopy predicate. -/
def OperationalBinarySimplicialGluing (V : Type v) [Fintype V] : Prop :=
  BinarySimplicialGluingFor (fun k (S : Set (stdSimplex ℝ V)) => NullConnectedSet k S)

/-- The numerical finite-cover hypotheses in the operational predicate. -/
def OperationalNerveHypotheses {ι : Type u} {V : Type v}
    [Fintype ι] [Fintype V]
    (k : ℕ) (C : ι → PreAbstractSimplicialComplex V) : Prop :=
  FiniteCoverConnectivityHypotheses
    (fun j S => NullConnectedSet j S) k
    (fun i => simplicialRealization (C i))

/-- Conditional operational nerve theorem. The binary gluing premise must be
proved before this can supply an endpoint certificate. -/
theorem operationalFiniteCover_of_binaryGluing
    {V : Type v} [Fintype V]
    (hglue : OperationalBinarySimplicialGluing V) (k : ℕ) :
    ∀ {ι : Type u} [Fintype ι] [Nonempty ι]
      (C : ι → PreAbstractSimplicialComplex V),
      OperationalNerveHypotheses k C →
      NullConnectedSet k (simplicialRealization (⨆ i, C i)) := by
  intro ι instF instN C hC
  letI : Fintype ι := instF
  letI : Nonempty ι := instN
  have hzero : ∀ {ζ : Type u} [Fintype ζ] [Nonempty ζ]
      (D : ζ → PreAbstractSimplicialComplex V),
      FiniteCoverConnectivityHypotheses
        (fun j (S : Set (stdSimplex ℝ V)) => NullConnectedSet j S) 0
        (fun i => simplicialRealization (D i)) →
      NullConnectedSet 0 (simplicialRealization (⨆ i, D i)) := by
    intro ζ _ _ D hD
    rw [simplicialRealization_iSup]
    apply (nullConnectedSet_zero_iff_isPathConnected _).2
    apply pathConnected_coverUnion
      (fun i => simplicialRealization (D i)) hD.1
    intro i
    have hs := hD.2 ({i} : Finset ζ) (Finset.singleton_nonempty i) (by simp)
    apply (nullConnectedSet_zero_iff_isPathConnected _).1
    simpa [coverIntersection] using hs
  exact finiteCover_of_binaryGluingFor
    (fun j (S : Set (stdSimplex ℝ V)) => NullConnectedSet j S)
    hzero hglue k C hC

end FairDivision.Topology.NerveConnectivity
