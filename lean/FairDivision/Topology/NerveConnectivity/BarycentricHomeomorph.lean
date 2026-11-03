import FairDivision.Topology.NerveConnectivity.BarycentricStrip

/-!
# Homeomorphism of a finite complex and its barycentric subdivision

The forward map sends each face vertex to its uniform barycenter. Its inverse
weights are recovered by coordinate-level gaps. Injectivity is proved by
removing the greatest positive face in the supporting chain and inducting
on the number of positive weights.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe v

/-- The canonical barycentric realization map is injective. -/
theorem barycentricForwardSimplex_injective {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    Function.Injective (barycentricForwardSimplex (K := K)) := by
  classical
  have hind : ∀ n : ℕ,
      ∀ z z' : simplicialRealization (barycentricSubdivision K),
        (FairDivision.Topology.finiteSimplexSupport z.1).card = n →
        barycentricForwardSimplex z = barycentricForwardSimplex z' → z = z' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro z z' hn hforward
      obtain ⟨M, hM, htop⟩ := finiteChain_exists_greatest
        (FairDivision.Topology.finiteSimplexSupport z.1) z.2.1 z.2.2.2
      obtain ⟨N, hN, htop'⟩ := finiteChain_exists_greatest
        (FairDivision.Topology.finiteSimplexSupport z'.1) z'.2.1 z'.2.2.2
      have hMN : M = N := by
        calc
          M = FairDivision.Topology.finiteSimplexSupport
                (barycentricForwardSimplex z) :=
              (barycentricForward_support_eq_greatest z M hM htop).symm
          _ = FairDivision.Topology.finiteSimplexSupport
                (barycentricForwardSimplex z') :=
              congrArg FairDivision.Topology.finiteSimplexSupport hforward
          _ = N := barycentricForward_support_eq_greatest z' N hN htop'
      subst N
      have hweight : z.1.1 M = z'.1.1 M := by
        calc
          z.1.1 M = faceInverseWeight M (barycentricForwardSimplex z) :=
            (barycentricInverseWeight_greatest z M hM htop).symm
          _ = faceInverseWeight M (barycentricForwardSimplex z') := by
            rw [hforward]
          _ = z'.1.1 M :=
            barycentricInverseWeight_greatest z' M hN htop'
      let P : Finset (Finset V) := Finset.univ.erase M
      have hmass : FairDivision.Topology.finiteSimplexMass P z.1 =
          FairDivision.Topology.finiteSimplexMass P z'.1 := by
        dsimp [P]
        rw [barycentricMass_erase_eq, barycentricMass_erase_eq, hweight]
      by_cases hzero : FairDivision.Topology.finiteSimplexMass P z.1 = 0
      · have hzero' : FairDivision.Topology.finiteSimplexMass P z'.1 = 0 := by
          rw [← hmass]
          exact hzero
        apply Subtype.ext
        apply Subtype.ext
        funext F
        by_cases hFM : F = M
        · subst F
          exact hweight
        · rw [barycentric_zero_of_zero_remaining_mass z M F hzero hFM,
              barycentric_zero_of_zero_remaining_mass z' M F hzero' hFM]
      · have hnonneg : 0 ≤ FairDivision.Topology.finiteSimplexMass P z.1 := by
          unfold FairDivision.Topology.finiteSimplexMass
          exact Finset.sum_nonneg (fun F _ => z.1.2.1 F)
        have hr : 0 < FairDivision.Topology.finiteSimplexMass P z.1 :=
          lt_of_le_of_ne hnonneg (Ne.symm hzero)
        have hr' : 0 < FairDivision.Topology.finiteSimplexMass P z'.1 := by
          rw [← hmass]
          exact hr
        have hstripForward := barycentricStrip_forward_eq z z' M hr hr'
          hforward hweight
        have hsmaller : (FairDivision.Topology.finiteSimplexSupport
            (barycentricStrip z M hr).1).card < n := by
          simpa [hn] using barycentricStrip_support_card_lt z M hM hr
        have hstripEq := ih _ hsmaller
          (barycentricStrip z M hr) (barycentricStrip z' M hr')
          rfl hstripForward
        apply Subtype.ext
        apply Subtype.ext
        funext F
        by_cases hFM : F = M
        · subst F
          exact hweight
        · have hcoord := congrArg
            (fun q : simplicialRealization (barycentricSubdivision K) =>
              q.1.1 F) hstripEq
          rw [barycentricStrip_weight_of_ne z M F hr hFM,
            barycentricStrip_weight_of_ne z' M F hr' hFM] at hcoord
          rw [← hmass] at hcoord
          have hrne : FairDivision.Topology.finiteSimplexMass P z.1 ≠ 0 :=
            ne_of_gt hr
          have hc := congrArg
            (fun t : ℝ => t * FairDivision.Topology.finiteSimplexMass P z.1)
            hcoord
          dsimp [P] at hc hrne
          field_simp [hrne] at hc
          exact hc
  intro z z' hforward
  exact hind _ z z' rfl hforward


/-- Canonical homeomorphism between a finite simplicial complex and its
barycentric subdivision, both realized in finite probability simplices. -/
noncomputable def barycentricRealizationHomeomorph {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    simplicialRealization (barycentricSubdivision K) ≃ₜ
      simplicialRealization K where
  toFun := barycentricForwardMap K
  invFun := barycentricInverseMap K
  left_inv z := by
    apply barycentricForwardSimplex_injective K
    have h := barycentricForward_comp_inverse K (barycentricForwardMap K z)
    exact congrArg Subtype.val h
  right_inv := barycentricForward_comp_inverse K
  continuous_toFun := (barycentricForwardMap K).continuous
  continuous_invFun := (barycentricInverseMap K).continuous

end FairDivision.Topology.NerveConnectivity
