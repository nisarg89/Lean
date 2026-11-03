import FairDivision.Topology.VariableDummyConnectivityInduction
import FairDivision.Topology.VariableDummyUniformSlack
import FairDivision.Topology.VariableUniformBridge

/-!
# Uniform BF auxiliary-complex connectivity

This specializes the compiled variable-size induction to the parameters in
Section 3 of the BF manuscript. The binary gluing theorem remains an explicit
premise until the shared finite-cover topology development proves it.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open NerveConnectivity

/-- The uniform BF auxiliary complex has the manuscript's `(n/a - 1)`
connectivity bound, subject to the shared binary simplicial gluing theorem. -/
theorem variableUniformStock_nullConnected_of_binaryGluing
    {m : ℕ} (n q a : ℕ)
    (hglue : ∀ (D : Finset (Fin m)) (r c : Fin (n / a) → ℕ),
      OperationalBinarySimplicialGluing
        (VariableUnlabeledVertex (n / a) m D r c))
    (D E : Finset (Fin m))
    (hn : 0 < n) (ha : 0 < a) (hq : 2 ≤ q) (hdiv : a ∣ n)
    (hED : Disjoint E D)
    (hTotal : E.card + D.card = n * q) (hD : D.card ≤ n) :
    NullConnectedSet (n / a - 1)
      (simplicialRealization
        (variableStockComplex D E
          (fun _ : Fin (n / a) => a * q - 1) (fun _ => a))) := by
  have hAd := variableUniform_admissible n q a D E ha hq hdiv hTotal hD
  have hSlack := variableUniform_slack n q a D E ha hq hdiv hTotal hD
  have hPos : 0 < n / a := by
    have hMul := Nat.div_mul_cancel hdiv
    by_contra hNot
    have hz : n / a = 0 := by omega
    rw [hz] at hMul
    simp at hMul
    omega
  have hConn := variableStock_nullConnected_of_binaryGluing
    hglue D E (fun _ : Fin (n / a) => a * q - 1) (fun _ => a)
    hED hAd (by rw [hSlack]; exact hPos)
  rw [hSlack] at hConn
  exact hConn

/-- Deleting a real item leaves the uniform auxiliary complex nonempty,
including the one-position case where the claimed connectivity is `-1`. -/
theorem variableUniformStock_erase_nonempty
    {m : ℕ} (n q a : ℕ)
    (D E : Finset (Fin m)) (e : Fin m)
    (ha : 0 < a) (hq : 2 ≤ q) (hdiv : a ∣ n)
    (hED : Disjoint E D) (he : e ∈ E)
    (hTotal : E.card + D.card = n * q) (hD : D.card ≤ n)
    (hPositions : 0 < n / a) :
    Nonempty (simplicialRealization
      (variableStockComplex D (E.erase e)
        (fun _ : Fin (n / a) => a * q - 1) (fun _ => a))) := by
  have hAd := variableUniform_admissible n q a D E ha hq hdiv hTotal hD
  have hSlack := variableUniform_slack n q a D E ha hq hdiv hTotal hD
  have hPositive : 0 < variableSlack E.card D.card
      (fun _ : Fin (n / a) => a * q - 1) (fun _ => a) := by
    rw [hSlack]
    exact hPositions
  have hErased := variableIntersection_admissible_slack D E
    (fun _ : Fin (n / a) => a * q - 1) (fun _ => a)
    e he hAd hPositive
  exact variableStock_nonempty_of_admissible D (E.erase e)
    (fun _ : Fin (n / a) => a * q - 1) (fun _ => a)
    (hED.mono_left (Finset.erase_subset e E)) hErased.1

/-- When there are at least two positions, deleting one real item gives
exactly the manuscript's `(n/a - 2)` connectivity bound. -/
theorem variableUniformStock_erase_nullConnected_of_binaryGluing
    {m : ℕ} (n q a : ℕ)
    (hglue : ∀ (D : Finset (Fin m)) (r c : Fin (n / a) → ℕ),
      OperationalBinarySimplicialGluing
        (VariableUnlabeledVertex (n / a) m D r c))
    (D E : Finset (Fin m)) (e : Fin m)
    (ha : 0 < a) (hq : 2 ≤ q) (hdiv : a ∣ n)
    (hED : Disjoint E D) (he : e ∈ E)
    (hTotal : E.card + D.card = n * q) (hD : D.card ≤ n)
    (hPositions : 2 ≤ n / a) :
    NullConnectedSet (n / a - 2)
      (simplicialRealization
        (variableStockComplex D (E.erase e)
          (fun _ : Fin (n / a) => a * q - 1) (fun _ => a))) := by
  have hAd := variableUniform_admissible n q a D E ha hq hdiv hTotal hD
  have hSlack := variableUniform_slack n q a D E ha hq hdiv hTotal hD
  have hPositive : 0 < variableSlack E.card D.card
      (fun _ : Fin (n / a) => a * q - 1) (fun _ => a) := by
    rw [hSlack]
    omega
  have hErased := variableIntersection_admissible_slack D E
    (fun _ : Fin (n / a) => a * q - 1) (fun _ => a)
    e he hAd hPositive
  have hErasedPos : 0 < variableSlack (E.erase e).card D.card
      (fun _ : Fin (n / a) => a * q - 1) (fun _ => a) := by
    have hEq := hErased.2
    omega
  have hConn := variableStock_nullConnected_of_binaryGluing
    hglue D (E.erase e)
    (fun _ : Fin (n / a) => a * q - 1) (fun _ => a)
    (hED.mono_left (Finset.erase_subset e E)) hErased.1 hErasedPos
  have hIndex : variableSlack (E.erase e).card D.card
      (fun _ : Fin (n / a) => a * q - 1) (fun _ => a) - 1 = n / a - 2 := by
    have hEq := hErased.2
    omega
  rw [hIndex] at hConn
  exact hConn

/-- The full corrected auxiliary complex, with all nondummy labels available,
receives the manuscript's uniform connectivity bound. The finite-cover
gluing dependency is still an explicit parameter. -/
theorem uniformUnlabeledDummy_nullConnected_of_binaryGluing
    (n q a : ℕ)
    (hglue : ∀ (D : Finset (Fin (n * q))) (r c : Fin (n / a) → ℕ),
      OperationalBinarySimplicialGluing
        (VariableUnlabeledVertex (n / a) (n * q) D r c))
    (D : Finset (Fin (n * q)))
    (hn : 0 < n) (ha : 0 < a) (hq : 2 ≤ q) (hdiv : a ∣ n)
    (hD : D.card ≤ n) :
    NullConnectedSet (n / a - 1)
      (simplicialRealization
        (unlabeledDummyComplex (n / a) (n * q)
          (a * q - 1) a D).toPreAbstractSimplicialComplex) := by
  let E : Finset (Fin (n * q)) := Finset.univ \ D
  have hED : Disjoint E D := Finset.sdiff_disjoint
  have hDuniv : D ⊆ (Finset.univ : Finset (Fin (n * q))) :=
    Finset.subset_univ _
  have hDcard : D.card ≤ n * q := by
    simpa using Finset.card_le_card hDuniv
  have hTotal : E.card + D.card = n * q := by
    dsimp [E]
    rw [Finset.card_sdiff_of_subset hDuniv]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hConn := variableUniformStock_nullConnected_of_binaryGluing
    n q a hglue D E hn ha hq hdiv hED hTotal hD
  change NullConnectedSet (n / a - 1)
    (simplicialRealization
      (variableStockComplex D (Finset.univ \ D)
        (fun _ : Fin (n / a) => a * q - 1) (fun _ => a))) at hConn
  rw [variableStockComplex_full] at hConn
  change NullConnectedSet (n / a - 1)
    (simplicialRealization
      (unlabeledDummyComplex (n / a) (n * q)
        (a * q - 1) a D).toPreAbstractSimplicialComplex) at hConn
  exact hConn

end FairDivision.Topology
