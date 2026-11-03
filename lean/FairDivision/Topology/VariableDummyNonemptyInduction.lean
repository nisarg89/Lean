import FairDivision.Topology.VariableDummyInductionControl
import FairDivision.Topology.VariableDummyStockBase
import FairDivision.Topology.VariableDummyStockWitness
import FairDivision.Topology.VariableDummyConnectivityTransfer

/-!
# Nonemptiness in the BF auxiliary-complex induction

The manuscript's connectivity argument proves nonemptiness at slack zero.
This file proves nonemptiness for every admissible slack by the same two
reductions. It is independent of the finite-cover nerve theorem.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open NerveConnectivity

/-- Every admissible restricted auxiliary complex has a point, provided the
real and dummy stocks are disjoint. The induction follows the manuscript:
saturate all usable dummies if they fit, and otherwise force one real item
into a positive-size position before deleting it. -/
theorem variableStock_nonempty_of_admissible {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ)
    (hED : Disjoint E D)
    (hAd : VariableSlackAdmissible E.card D.card r c) :
    Nonempty (simplicialRealization (variableStockComplex D E r c)) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (D E : Finset (Fin m)) (r c : Fin k → ℕ),
      Disjoint E D →
      VariableSlackAdmissible E.card D.card r c →
      E.card + variableRequirementTotal r = n →
      Nonempty (simplicialRealization (variableStockComplex D E r c))
  have hMain : ∀ n : ℕ, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro D E r c hED hAd hn
      by_cases hrZero : ∀ i : Fin k, r i = 0
      · exact (variableStock_nullConnected_zero
          (D := D) (E := E) (c := c) hrZero 0).1
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
        have hRedAd : VariableSlackAdmissible E.card 0
            (fun i => r i - u i) (fun _ => 0) :=
          (variableSaturation_admissible_slack E.card D.card r c
            hAd hSat.1).1
        have hLt : E.card + variableRequirementTotal
            (fun i => r i - u i) < n := by
          have h := variableSaturation_measure_lt E.card r c hSat.2
          change E.card + variableRequirementTotal
            (fun i => r i - u i) <
              E.card + variableRequirementTotal r at h
          omega
        have hReduced : Nonempty
            (simplicialRealization
              (variableStockComplex (∅ : Finset (Fin m)) E
                (fun i => r i - u i) (fun _ => 0))) :=
          ih _ hLt ∅ E (fun i => r i - u i) (fun _ => 0)
            (by simp) hRedAd rfl
        obtain ⟨q0, hq0⟩ :=
          exists_variableStockVertex_of_nonempty hReduced
        let p0 := variableSaturationLiftVertex u huR huC
          hBudget hED q0 hq0
        exact variableStock_nonempty_of_saturation u huR huC
          hBudget hBound hED p0 hReduced
      · have hBranch : D.card < variableUsefulDummyTotal r c ∨
            variableUsefulDummyTotal r c = 0 := by omega
        obtain ⟨a, hra⟩ := hSome
        have hReqPos : 0 < variableRequirementTotal r := by
          have ha : r a ≤ variableRequirementTotal r := by
            unfold variableRequirementTotal
            exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ a)
          omega
        have hUsefulLe := variableUsefulDummyTotal_le_requirements r c
        have hEPos : 0 < E.card := by
          unfold VariableSlackAdmissible at hAd
          rcases hBranch with hlt | hzero <;> omega
        obtain ⟨e, heE⟩ := Finset.card_pos.mp hEPos
        have heD : e ∉ D := by
          intro hD
          exact (Finset.disjoint_left.mp hED) heE hD
        have hRedAd : VariableSlackAdmissible
            (E.erase e).card D.card
            (variableDecreasedRequirement r a) c :=
          (variableForced_admissible_slack D E r c e heE a hra
            hAd hBranch).1
        have hLt : (E.erase e).card + variableRequirementTotal
            (variableDecreasedRequirement r a) < n := by
          have hCard := variableStock_erase_card_add_one E e heE
          have hM := variableForced_measure_lt E.card r a hEPos hra
          omega
        have hDisj : Disjoint (E.erase e) D := by
          apply Finset.disjoint_left.mpr
          intro x hx hD
          exact (Finset.disjoint_left.mp hED)
            ((Finset.erase_subset e E) hx) hD
        have hReduced : Nonempty
            (simplicialRealization
              (variableStockComplex D (E.erase e)
                (variableDecreasedRequirement r a) c)) :=
          ih _ hLt D (E.erase e)
            (variableDecreasedRequirement r a) c hDisj hRedAd rfl
        obtain ⟨q0, hq0⟩ :=
          exists_variableStockVertex_of_nonempty hReduced
        have hqAbs : ∀ i : Fin k, e ∉ (q0.1 i).1 := by
          intro i heq
          exact (Finset.ne_of_mem_erase (hq0 i heq)) rfl
        let p0 := variableForcedLiftVertex e heD a hra q0 hqAbs
        have hPiece := variableStockCover_nonempty_of_forcing
          e heD heE a hra p0 q0 hReduced
        obtain ⟨⟨lot, hlot⟩⟩ := hPiece
        exact ⟨⟨lot, hlot.1⟩⟩
  exact hMain (E.card + variableRequirementTotal r)
    D E r c hED hAd rfl

end FairDivision.Topology
