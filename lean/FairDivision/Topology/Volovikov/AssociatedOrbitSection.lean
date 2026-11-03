import FairDivision.Topology.Volovikov.UniversalJoinOrbitQuotient
import FairDivision.Topology.Volovikov.InvariantComplexAction

/-!
# Equivariant maps give sections over the finite join orbit space

This is the elementary bundle-theoretic half of the finite-skeleton Euler
obstruction. We construct the diagonal orbit space of the join paired with
a target and show that an equivariant map into the target gives a continuous
section over the join orbit space. No Euler class or section obstruction is
asserted here.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- The full-join action used by the extension interface agrees with the
earlier direct full-join homeomorphism. -/
theorem translateInvariant_universal_eq_join
    {m : ℕ} {G : Type*} [AddGroup G] [Fintype G]
    (a : G)
    (x : simplicialRealization (universalJoinComplex m G)) :
    translateInvariantRealization (universalJoinComplex m G)
      universalJoinComplex_invariant a x =
        translateJoinRealization a x := by
  apply Subtype.ext
  rfl

/-- The diagonal orbit relation on a finite join and a target carrying a
continuous additive group action. -/
def associatedOrbitSetoid
    (m : ℕ) (G Y : Type*)
    [AddGroup G] [Fintype G] [TopologicalSpace Y]
    (targetAction : G → Y ≃ₜ Y)
    (hAction : IsContinuousAddAction targetAction) :
    Setoid (simplicialRealization (universalJoinComplex m G) × Y) where
  r u v := ∃ a : G,
    (translateJoinRealization a u.1, targetAction a u.2) = v
  iseqv := by
    constructor
    · intro u
      refine ⟨0, ?_⟩
      exact Prod.ext (translateJoinRealization_zero u.1)
        (hAction.1 u.2)
    · intro u v huv
      obtain ⟨a, ha⟩ := huv
      have hx : translateJoinRealization a u.1 = v.1 :=
        congrArg Prod.fst ha
      have hy : targetAction a u.2 = v.2 :=
        congrArg Prod.snd ha
      refine ⟨-a, ?_⟩
      apply Prod.ext
      · calc
          translateJoinRealization (-a) v.1 =
              translateJoinRealization (-a)
                (translateJoinRealization a u.1) := by rw [hx]
          _ = translateJoinRealization ((-a) + a) u.1 :=
              (translateJoinRealization_add (-a) a u.1).symm
          _ = u.1 := by rw [neg_add_cancel, translateJoinRealization_zero]
      · calc
          targetAction (-a) v.2 =
              targetAction (-a) (targetAction a u.2) := by rw [hy]
          _ = targetAction ((-a) + a) u.2 :=
              (hAction.2 (-a) a u.2).symm
          _ = u.2 := by rw [neg_add_cancel, hAction.1]
    · intro u v w huv hvw
      obtain ⟨a, ha⟩ := huv
      obtain ⟨b, hb⟩ := hvw
      have hax : translateJoinRealization a u.1 = v.1 :=
        congrArg Prod.fst ha
      have hay : targetAction a u.2 = v.2 :=
        congrArg Prod.snd ha
      have hbx : translateJoinRealization b v.1 = w.1 :=
        congrArg Prod.fst hb
      have hby : targetAction b v.2 = w.2 :=
        congrArg Prod.snd hb
      refine ⟨b + a, ?_⟩
      apply Prod.ext
      · calc
          translateJoinRealization (b + a) u.1 =
              translateJoinRealization b
                (translateJoinRealization a u.1) :=
              translateJoinRealization_add b a u.1
          _ = translateJoinRealization b v.1 := by rw [hax]
          _ = w.1 := hbx
      · calc
          targetAction (b + a) u.2 =
              targetAction b (targetAction a u.2) :=
              hAction.2 b a u.2
          _ = targetAction b v.2 := by rw [hay]
          _ = w.2 := hby

/-- The associated orbit space of the join and target. -/
abbrev AssociatedOrbitSpace
    (m : ℕ) (G Y : Type*)
    [AddGroup G] [Fintype G] [TopologicalSpace Y]
    (targetAction : G → Y ≃ₜ Y)
    (hAction : IsContinuousAddAction targetAction) :=
  Quotient (associatedOrbitSetoid m G Y targetAction hAction)

/-- Projection of the associated orbit space to the join orbit space. -/
def associatedOrbitProjection
    (m : ℕ) (G Y : Type*)
    [AddGroup G] [Fintype G] [TopologicalSpace Y]
    (targetAction : G → Y ≃ₜ Y)
    (hAction : IsContinuousAddAction targetAction) :
    C(AssociatedOrbitSpace m G Y targetAction hAction,
      UniversalJoinOrbitSpace m G) := by
  let q : simplicialRealization (universalJoinComplex m G) × Y →
      UniversalJoinOrbitSpace m G :=
    fun u => universalJoinOrbitProjection m G u.1
  have hq : ∀ u v,
      (associatedOrbitSetoid m G Y targetAction hAction).r u v → q u = q v := by
    intro u v huv
    obtain ⟨a, ha⟩ := huv
    have hx : translateJoinRealization a u.1 = v.1 :=
      congrArg Prod.fst ha
    change universalJoinOrbitProjection m G u.1 =
      universalJoinOrbitProjection m G v.1
    rw [← hx, universalJoinOrbitProjection_translate]
  have hqc : Continuous q :=
    (universalJoinOrbitProjection m G).continuous.comp continuous_fst
  exact ⟨Quotient.lift q hq, hqc.quotient_lift hq⟩

/-- An equivariant map into the target descends to a continuous section of
the associated orbit projection. -/
def associatedSectionOfEquivariantMap
    (m : ℕ) (G Y : Type*)
    [AddGroup G] [Fintype G] [TopologicalSpace Y]
    (targetAction : G → Y ≃ₜ Y)
    (hAction : IsContinuousAddAction targetAction)
    (f : C(simplicialRealization (universalJoinComplex m G), Y))
    (hf : IsEquivariantJoinMap (universalJoinComplex m G)
      universalJoinComplex_invariant targetAction f) :
    C(UniversalJoinOrbitSpace m G,
      AssociatedOrbitSpace m G Y targetAction hAction) := by
  let q : simplicialRealization (universalJoinComplex m G) →
      AssociatedOrbitSpace m G Y targetAction hAction :=
    fun x => Quotient.mk (associatedOrbitSetoid m G Y targetAction hAction) (x, f x)
  have hq : ∀ x y,
      (universalJoinRealizationOrbitSetoid m G).r x y → q x = q y := by
    intro x y hxy
    obtain ⟨a, ha⟩ := hxy
    change Quotient.mk (associatedOrbitSetoid m G Y targetAction hAction)
        (x, f x) =
      Quotient.mk (associatedOrbitSetoid m G Y targetAction hAction)
        (y, f y)
    apply Quotient.sound
    refine ⟨a, ?_⟩
    apply Prod.ext
    · exact ha
    · change targetAction a (f x) = f y
      rw [← ha]
      simpa only [translateInvariant_universal_eq_join] using (hf a x).symm
  have hqc : Continuous q :=
    (continuous_quotient_mk'
      (s := associatedOrbitSetoid m G Y targetAction hAction)).comp
        (continuous_id.prodMk f.continuous)
  exact ⟨Quotient.lift q hq, hqc.quotient_lift hq⟩

/-- The descended map is a genuine section over the finite join orbit
space. -/
theorem associatedSectionOfEquivariantMap_section
    (m : ℕ) (G Y : Type*)
    [AddGroup G] [Fintype G] [TopologicalSpace Y]
    (targetAction : G → Y ≃ₜ Y)
    (hAction : IsContinuousAddAction targetAction)
    (f : C(simplicialRealization (universalJoinComplex m G), Y))
    (hf : IsEquivariantJoinMap (universalJoinComplex m G)
      universalJoinComplex_invariant targetAction f) :
    (associatedOrbitProjection m G Y targetAction hAction).comp
      (associatedSectionOfEquivariantMap m G Y targetAction hAction f hf) =
        ContinuousMap.id _ := by
  ext z
  induction z using Quotient.inductionOn with
  | _ x =>
      change Quotient.mk (universalJoinRealizationOrbitSetoid m G) x =
        Quotient.mk (universalJoinRealizationOrbitSetoid m G) x
      rfl

end FairDivision.Topology.Volovikov
