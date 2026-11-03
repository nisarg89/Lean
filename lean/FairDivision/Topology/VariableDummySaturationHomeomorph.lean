import FairDivision.Topology.VariableDummySaturationReduction
import FairDivision.Topology.NerveConnectivity.RealizationEquiv

/-!
# Realization of the saturated-dummy reduction

The manuscript's saturated-dummy retract is identified with the auxiliary
complex having requirements `r_i - u_i` and no dummy items. The two vertex
maps preserve the real bundles of every active face, so the generic
finite-realization transport applies.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open NerveConnectivity

/-- Once one original auxiliary vertex is available, the saturated-dummy
subcomplex and the reduced no-dummy stock complex have homeomorphic
realizations. The witness is used only to define the reverse vertex map on
vertices outside the active reduced stock. -/
noncomputable def variableSaturated_reduced_homeomorph {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (hED : Disjoint E D)
    (p0 : VariableUnlabeledVertex k m D r c) :
    (simplicialRealization (variableSaturatedComplex D E r c u)) ≃ₜ
      (simplicialRealization
        (variableStockComplex (∅ : Finset (Fin m)) E
          (fun i => r i - u i) (fun _ => 0))) := by
  classical
  let f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m (∅ : Finset (Fin m))
        (fun i => r i - u i) (fun _ => 0) :=
    variableSaturationReducedVertex u huR huC hBudget hBound
  let g : VariableUnlabeledVertex k m (∅ : Finset (Fin m))
      (fun i => r i - u i) (fun _ => 0) →
      VariableUnlabeledVertex k m D r c :=
    fun q => if h : ∀ i : Fin k, (q.1 i).1 ⊆ E then
      variableSaturationLiftVertex u huR huC hBudget hED q h
    else p0
  have hgSpec (q : VariableUnlabeledVertex k m
      (∅ : Finset (Fin m)) (fun i => r i - u i) (fun _ => 0))
      (hq : ∀ i : Fin k, (q.1 i).1 ⊆ E) (i : Fin k) :
      (g q).1 i = ((q.1 i).1, u i) := by
    change (if h : ∀ i : Fin k, (q.1 i).1 ⊆ E then
      variableSaturationLiftVertex u huR huC hBudget hED q h
      else p0).1 i = _
    simp [hq, variableSaturationLiftVertex_spec]
  have hfReal (S : Finset (VariableUnlabeledVertex k m D r c))
      (hS : S ∈ variableSaturatedComplex D E r c u)
      (p : VariableUnlabeledVertex k m D r c) (hp : p ∈ S)
      (i : Fin k) : ((f p).1 i).1 = (p.1 i).1 := by
    have hFixed := saturateVariableVertex_eq_of_saturated
      u huR huC hBudget hBound p (hS.2 p hp)
    simpa [f, hFixed] using congrArg Prod.fst
      (variableSaturationReducedVertex_spec
        u huR huC hBudget hBound p i)
  have hfDummy (p : VariableUnlabeledVertex k m D r c)
      (i : Fin k) : ((f p).1 i).2 = 0 := by
    simpa [f] using congrArg Prod.snd
      (variableSaturationReducedVertex_spec
        u huR huC hBudget hBound p i)
  have hForward : ∀ S : Finset (VariableUnlabeledVertex k m D r c),
      S ∈ variableSaturatedComplex D E r c u →
      S.image f ∈ variableStockComplex
        (∅ : Finset (Fin m)) E
        (fun i => r i - u i) (fun _ => 0) := by
    intro S hS
    have hFace : IsVariableUnlabeledFamily (S.image f) :=
      variableFace_image_of_real_preserving f S hS.1.1.2
        (hfReal S hS) (fun _ => 0)
        (fun p _ i => by simp [hfDummy p i]) (by simp)
    refine ⟨⟨Finset.image_nonempty.mpr hS.1.1.1, hFace⟩, ?_⟩
    intro q hq i
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
    subst q
    rw [hfReal S hS p hp i]
    exact hS.1.2 p hp i
  have hBackward : ∀ T : Finset
      (VariableUnlabeledVertex k m (∅ : Finset (Fin m))
        (fun i => r i - u i) (fun _ => 0)),
      T ∈ variableStockComplex (∅ : Finset (Fin m)) E
        (fun i => r i - u i) (fun _ => 0) →
      T.image g ∈ variableSaturatedComplex D E r c u := by
    intro T hT
    have hReal : ∀ q ∈ T, ∀ i : Fin k,
        ((g q).1 i).1 = (q.1 i).1 := by
      intro q hq i
      rw [hgSpec q (hT.2 q hq) i]
    have hDummy : ∀ q ∈ T, ∀ i : Fin k,
        ((g q).1 i).2 ≤ u i := by
      intro q hq i
      exact le_of_eq (congrArg Prod.snd
        (hgSpec q (hT.2 q hq) i))
    have hFace : IsVariableUnlabeledFamily (T.image g) :=
      variableFace_image_of_real_preserving g T hT.1.2
        hReal u hDummy hBudget
    refine ⟨⟨⟨Finset.image_nonempty.mpr hT.1.1, hFace⟩, ?_⟩, ?_⟩
    · intro p hp i
      obtain ⟨q, hq, hpq⟩ := Finset.mem_image.mp hp
      subst p
      rw [hReal q hq i]
      exact hT.2 q hq i
    · intro p hp i
      obtain ⟨q, hq, hpq⟩ := Finset.mem_image.mp hp
      subst p
      exact congrArg Prod.snd (hgSpec q (hT.2 q hq) i)
  have hgf : ∀ S : Finset (VariableUnlabeledVertex k m D r c),
      S ∈ variableSaturatedComplex D E r c u →
      ∀ p ∈ S, g (f p) = p := by
    intro S hS p hp
    have hq : ∀ i : Fin k, ((f p).1 i).1 ⊆ E := by
      intro i
      rw [hfReal S hS p hp i]
      exact hS.1.2 p hp i
    apply Subtype.ext
    funext i
    apply Prod.ext
    · calc
        ((g (f p)).1 i).1 = ((f p).1 i).1 := by
          rw [hgSpec (f p) hq i]
        _ = (p.1 i).1 := hfReal S hS p hp i
    · calc
        ((g (f p)).1 i).2 = u i :=
          congrArg Prod.snd (hgSpec (f p) hq i)
        _ = (p.1 i).2 := (hS.2 p hp i).symm
  have hfg : ∀ T : Finset
      (VariableUnlabeledVertex k m (∅ : Finset (Fin m))
        (fun i => r i - u i) (fun _ => 0)),
      T ∈ variableStockComplex (∅ : Finset (Fin m)) E
        (fun i => r i - u i) (fun _ => 0) →
      ∀ q ∈ T, f (g q) = q := by
    intro T hT q hq
    have hqStock := hT.2 q hq
    have hSat : ∀ i : Fin k, ((g q).1 i).2 = u i := by
      intro i
      exact congrArg Prod.snd (hgSpec q hqStock i)
    have hFixed := saturateVariableVertex_eq_of_saturated
      u huR huC hBudget hBound (g q) hSat
    apply Subtype.ext
    funext i
    apply Prod.ext
    · calc
        ((f (g q)).1 i).1 = ((g q).1 i).1 := by
          simpa [f, hFixed] using congrArg Prod.fst
            (variableSaturationReducedVertex_spec
              u huR huC hBudget hBound (g q) i)
        _ = (q.1 i).1 := by
          rw [hgSpec q hqStock i]
    · calc
        ((f (g q)).1 i).2 = 0 := hfDummy (g q) i
        _ = (q.1 i).2 := by
          have hc := variableProfile_dummy_le_cap q i
          omega
  exact realizationHomeomorphOfVertexMaps
    (variableSaturatedComplex D E r c u)
    (variableStockComplex (∅ : Finset (Fin m)) E
      (fun i => r i - u i) (fun _ => 0))
    f g hForward hBackward hgf hfg

end FairDivision.Topology
