import FairDivision.Topology.VariableDummyNonemptyInduction
import FairDivision.Topology.VariableDummyCoverIntersections
import FairDivision.Topology.NerveConnectivity.OperationalReduction

/-!
# Connectivity induction for the BF auxiliary complex

This is the corrected manuscript's finite-cover induction after its one
external topology dependency has been isolated. The theorem below has the
operational binary simplicial gluing theorem as an explicit premise. It does
not assert that premise as an axiom or close a BF existence endpoint.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open NerveConnectivity

/-- Assuming the shared positive-dimensional gluing theorem for the finite
auxiliary vertex types, every admissible BF restricted auxiliary complex
with positive slack is connected through the manuscript's claimed dimension.
The dummy-saturation and item-cover branches follow the manuscript. -/
theorem variableStock_nullConnected_of_binaryGluing {k m : ℕ}
    (hglue : ∀ (D : Finset (Fin m)) (r c : Fin k → ℕ),
      OperationalBinarySimplicialGluing
        (VariableUnlabeledVertex k m D r c))
    (D E : Finset (Fin m)) (r c : Fin k → ℕ)
    (hED : Disjoint E D)
    (hAd : VariableSlackAdmissible E.card D.card r c)
    (hPositive : 0 < variableSlack E.card D.card r c) :
    NullConnectedSet (variableSlack E.card D.card r c - 1)
      (simplicialRealization (variableStockComplex D E r c)) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (D E : Finset (Fin m)) (r c : Fin k → ℕ),
      Disjoint E D →
      VariableSlackAdmissible E.card D.card r c →
      E.card + variableRequirementTotal r = n →
      0 < variableSlack E.card D.card r c →
      NullConnectedSet (variableSlack E.card D.card r c - 1)
        (simplicialRealization (variableStockComplex D E r c))
  have hMain : ∀ n : ℕ, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro D E r c hED hAd hn hPositive
      by_cases hrZero : ∀ i : Fin k, r i = 0
      · exact variableStock_nullConnected_zero
          (D := D) (E := E) (c := c) hrZero _
      have hSome : ∃ a : Fin k, 0 < r a := by
        by_contra hNo
        apply hrZero
        intro i
        have hNot : ¬ 0 < r i := by
          intro hi
          exact hNo ⟨i, hi⟩
        omega
      by_cases hSat :
          variableUsefulDummyTotal r c ≤ D.card ∧
            0 < variableUsefulDummyTotal r c
      · let u : Fin k → ℕ := fun i => min (r i) (c i)
        have huR : ∀ i, u i ≤ r i := fun i => Nat.min_le_left _ _
        have huC : ∀ i, u i ≤ c i := fun i => Nat.min_le_right _ _
        have hBudget : (∑ i : Fin k, u i) ≤ D.card := by
          simpa [u, variableUsefulDummyTotal] using hSat.1
        have hBound : ∀ p : VariableUnlabeledVertex k m D r c,
            ∀ i, (p.1 i).2 ≤ u i := by
          intro p i
          have hcard := variableProfile_card p i
          have hcap := variableProfile_dummy_le_cap p i
          dsimp [u]
          omega
        have hSatControl := variableSaturation_admissible_slack
          E.card D.card r c hAd hSat.1
        have hRedAd : VariableSlackAdmissible E.card 0
            (fun i => r i - u i) (fun _ => 0) := hSatControl.1
        have hRedSlack : variableSlack E.card 0
            (fun i => r i - u i) (fun _ => 0) =
            variableSlack E.card D.card r c := hSatControl.2
        have hLt : E.card + variableRequirementTotal
            (fun i => r i - u i) < n := by
          have h := variableSaturation_measure_lt E.card r c hSat.2
          change E.card + variableRequirementTotal
            (fun i => r i - u i) <
              E.card + variableRequirementTotal r at h
          omega
        have hReduced : NullConnectedSet
            (variableSlack E.card 0
              (fun i => r i - u i) (fun _ => 0) - 1)
            (simplicialRealization
              (variableStockComplex (∅ : Finset (Fin m)) E
                (fun i => r i - u i) (fun _ => 0))) :=
          ih _ hLt ∅ E (fun i => r i - u i) (fun _ => 0)
            (by simp) hRedAd rfl (by simpa only [Finset.card_empty, hRedSlack] using hPositive)
        have hReducedNonempty : Nonempty
            (simplicialRealization
              (variableStockComplex (∅ : Finset (Fin m)) E
                (fun i => r i - u i) (fun _ => 0))) := hReduced.1
        obtain ⟨q0, hq0⟩ :=
          exists_variableStockVertex_of_nonempty hReducedNonempty
        let p0 := variableSaturationLiftVertex u huR huC
          hBudget hED q0 hq0
        have hTransfer := variableStock_nullConnected_of_saturation
          u huR huC hBudget hBound hED p0
          (variableSlack E.card 0
            (fun i => r i - u i) (fun _ => 0) - 1) hReduced
        rw [hRedSlack] at hTransfer
        exact hTransfer
      · have hBranch : D.card < variableUsefulDummyTotal r c ∨
            variableUsefulDummyTotal r c = 0 := by omega
        obtain ⟨a0, hra0⟩ := hSome
        have hReqPos : 0 < variableRequirementTotal r := by
          have ha : r a0 ≤ variableRequirementTotal r := by
            unfold variableRequirementTotal
            exact Finset.single_le_sum (fun i _ => Nat.zero_le _)
              (Finset.mem_univ a0)
          omega
        have hUsefulLe := variableUsefulDummyTotal_le_requirements r c
        have hEPos : 0 < E.card := by
          unfold VariableSlackAdmissible at hAd
          rcases hBranch with hlt | hzero <;> omega
        obtain ⟨e, heE⟩ := Finset.card_pos.mp hEPos
        have heD : e ∉ D := by
          intro hD
          exact (Finset.disjoint_left.mp hED) heE hD
        have hErasedControl := variableIntersection_admissible_slack
          D E r c e heE hAd hPositive
        have hErasedAd : VariableSlackAdmissible
            (E.erase e).card D.card r c := hErasedControl.1
        have hErasedNonempty : Nonempty
            (simplicialRealization
              (variableStockComplex D (E.erase e) r c)) :=
          variableStock_nonempty_of_admissible D (E.erase e) r c
            (hED.mono_left (Finset.erase_subset e E)) hErasedAd
        let ι := {a : Fin k // 0 < r a}
        letI : Nonempty ι := ⟨⟨a0, hra0⟩⟩
        let C := variableStockItemFiniteCover D E r c e ⟨a0, hra0⟩
        have hHyp : OperationalNerveHypotheses
            (variableSlack E.card D.card r c - 1) C.pieces := by
          constructor
          · exact variableStockItem_commonPoint_of_erase_nonempty
              D E r c e hErasedNonempty
          · intro J hJ hCard
            by_cases hTwo : 2 ≤ J.card
            · change NullConnectedSet _
                (coverIntersection
                  (fun a : {a : Fin k // 0 < r a} =>
                    simplicialRealization
                      (variableStockComplex D E r c ⊓
                        variableItemCoverComplex D r c e a.1)) J)
              rw [variableStockItem_coverIntersection_eq_erase
                D E r c e J hTwo]
              have hLt : (E.erase e).card +
                  variableRequirementTotal r < n := by
                have hCardErase := variableStock_erase_card_add_one E e heE
                omega
              have hErasedPositive : 0 < variableSlack
                  (E.erase e).card D.card r c := by
                have hCardJ : 2 ≤ variableSlack E.card D.card r c := by
                  omega
                have hSlack := hErasedControl.2
                omega
              have hErasedConn : NullConnectedSet
                  (variableSlack (E.erase e).card D.card r c - 1)
                  (simplicialRealization
                    (variableStockComplex D (E.erase e) r c)) :=
                ih _ hLt D (E.erase e) r c
                  (hED.mono_left (Finset.erase_subset e E))
                  hErasedAd rfl hErasedPositive
              exact hErasedConn.mono (by
                have hSlack := hErasedControl.2
                omega)
            · have hOne : J.card = 1 := by
                have hPosJ := Finset.card_pos.mpr hJ
                omega
              obtain ⟨a, hJa⟩ := Finset.card_eq_one.mp hOne
              subst J
              change NullConnectedSet _
                (coverIntersection
                  (fun b : {a : Fin k // 0 < r a} =>
                    simplicialRealization
                      (variableStockComplex D E r c ⊓
                        variableItemCoverComplex D r c e b.1)) {a})
              rw [variableStockItem_coverIntersection_singleton]
              have hForcedControl := variableForced_admissible_slack
                D E r c e heE a.1 a.2 hAd hBranch
              have hRedAd : VariableSlackAdmissible
                  (E.erase e).card D.card
                    (variableDecreasedRequirement r a.1) c :=
                hForcedControl.1
              have hLt : (E.erase e).card + variableRequirementTotal
                  (variableDecreasedRequirement r a.1) < n := by
                have hCardErase := variableStock_erase_card_add_one E e heE
                have hMeas := variableForced_measure_lt E.card r a.1
                  hEPos a.2
                omega
              have hRedPositive : 0 < variableSlack
                  (E.erase e).card D.card
                    (variableDecreasedRequirement r a.1) c := by
                rw [hForcedControl.2]
                exact hPositive
              have hReduced : NullConnectedSet
                  (variableSlack (E.erase e).card D.card
                    (variableDecreasedRequirement r a.1) c - 1)
                  (simplicialRealization
                    (variableStockComplex D (E.erase e)
                      (variableDecreasedRequirement r a.1) c)) :=
                ih _ hLt D (E.erase e)
                  (variableDecreasedRequirement r a.1) c
                  (hED.mono_left (Finset.erase_subset e E))
                  hRedAd rfl hRedPositive
              obtain ⟨q0, hq0⟩ :=
                exists_variableStockVertex_of_nonempty hReduced.1
              have hqAbs : ∀ i : Fin k, e ∉ (q0.1 i).1 := by
                intro i heq
                exact (Finset.ne_of_mem_erase (hq0 i heq)) rfl
              let p0 := variableForcedLiftVertex e heD a.1 a.2 q0 hqAbs
              have hPiece := variableStockCover_nullConnected_of_forcing
                e heD heE a.1 a.2 p0 q0
                (variableSlack (E.erase e).card D.card
                  (variableDecreasedRequirement r a.1) c - 1) hReduced
              rw [hForcedControl.2] at hPiece
              simpa using hPiece
        have hUnion := operationalFiniteCover_of_binaryGluing
          (hglue D r c) (variableSlack E.card D.card r c - 1)
          C.pieces hHyp
        change NullConnectedSet _ (simplicialRealization C.ambient)
        rw [C.realization_eq_union, ← simplicialRealization_iSup]
        exact hUnion
  exact hMain (E.card + variableRequirementTotal r)
    D E r c hED hAd rfl hPositive

end FairDivision.Topology
