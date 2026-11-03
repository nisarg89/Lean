import FairDivision.Topology.VariableDummyForceReduction
import FairDivision.Topology.VariableDummyProfileInsertion
import FairDivision.Topology.NerveConnectivity.RealizationEquiv

/-!
# Realization of the forced-item reduction

After the manuscript's retraction forces `e` into position `a`, deleting `e`
identifies the image with the auxiliary complex on the remaining real stock,
with only requirement `r a` decreased. The ambient finite item type remains
unchanged; its allowed real stock is `E.erase e`.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open NerveConnectivity

/-- The forced-item subcomplex is homeomorphic to the auxiliary complex
obtained by deleting `e` and decreasing the requirement at `a`. The two
fallback vertices merely totalize maps away from active faces. -/
noncomputable def variableForced_reduced_homeomorph {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D) (heE : e ∈ E)
    (a : Fin k) (hra : 0 < r a)
    (p0 : VariableUnlabeledVertex k m D r c)
    (q0 : VariableUnlabeledVertex k m D
      (variableDecreasedRequirement r a) c) :
    simplicialRealization (variableForcedItemComplex D E r c e a) ≃ₜ
      simplicialRealization
        (variableStockComplex D (E.erase e)
          (variableDecreasedRequirement r a) c) := by
  classical
  let f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D
        (variableDecreasedRequirement r a) c :=
    fun p => if h : e ∈ (p.1 a).1 then
      variableForcedReducedVertex e a hra p h else q0
  let g : VariableUnlabeledVertex k m D
      (variableDecreasedRequirement r a) c →
      VariableUnlabeledVertex k m D r c :=
    fun q => if h : ∀ i : Fin k, e ∉ (q.1 i).1 then
      variableForcedLiftVertex e heD a hra q h else p0
  have hfSpec (p : VariableUnlabeledVertex k m D r c)
      (he : e ∈ (p.1 a).1) (i : Fin k) :
      (f p).1 i =
        (if i = a then (p.1 i).1.erase e else (p.1 i).1,
          (p.1 i).2) := by
    simp [f, he, variableForcedReducedVertex_spec]
  have hgSpec (q : VariableUnlabeledVertex k m D
      (variableDecreasedRequirement r a) c)
      (he : ∀ i : Fin k, e ∉ (q.1 i).1) (i : Fin k) :
      (g q).1 i =
        (if i = a then insert e (q.1 i).1 else (q.1 i).1,
          (q.1 i).2) := by
    simp [g, he, variableForcedLiftVertex_spec]
  have hForcedAbsent (S : Finset (VariableUnlabeledVertex k m D r c))
      (hS : S ∈ variableForcedItemComplex D E r c e a)
      (p : VariableUnlabeledVertex k m D r c) (hp : p ∈ S)
      (i : Fin k) (hi : i ≠ a) : e ∉ (p.1 i).1 := by
    intro hei
    have hDisj := variableProfile_real_pairwise p a i (Ne.symm hi)
    exact (Finset.disjoint_left.mp hDisj) (hS.2 p hp) hei
  have hForward : ∀ S : Finset (VariableUnlabeledVertex k m D r c),
      S ∈ variableForcedItemComplex D E r c e a →
      S.image f ∈ variableStockComplex D (E.erase e)
        (variableDecreasedRequirement r a) c := by
    intro S hS
    have hReal : ∀ p ∈ S, ∀ i : Fin k,
        ((f p).1 i).1 ⊆ (p.1 i).1 := by
      intro p hp i
      rw [hfSpec p (hS.2 p hp) i]
      by_cases hi : i = a
      · simpa [hi] using Finset.erase_subset e (p.1 a).1
      · simp [hi]
    have hDummy : ∀ p ∈ S, ∀ i : Fin k,
        ((f p).1 i).2 ≤ (p.1 i).2 := by
      intro p hp i
      rw [hfSpec p (hS.2 p hp) i]
    have hFace : IsVariableUnlabeledFamily (S.image f) :=
      variableFace_image_of_shrinking f S hS.1.1.2 hReal hDummy
    refine ⟨⟨Finset.image_nonempty.mpr hS.1.1.1, hFace⟩, ?_⟩
    intro q hq i x hx
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
    subst q
    rw [hfSpec p (hS.2 p hp) i] at hx
    by_cases hi : i = a
    · rw [if_pos hi] at hx
      obtain ⟨hxe, hxp⟩ := Finset.mem_erase.mp hx
      exact Finset.mem_erase.mpr ⟨hxe, hS.1.2 p hp i hxp⟩
    · rw [if_neg hi] at hx
      exact Finset.mem_erase.mpr
        ⟨fun hxe => hForcedAbsent S hS p hp i hi (hxe ▸ hx),
          hS.1.2 p hp i hx⟩
  have hBackward : ∀ T : Finset (VariableUnlabeledVertex k m D
      (variableDecreasedRequirement r a) c),
      T ∈ variableStockComplex D (E.erase e)
        (variableDecreasedRequirement r a) c →
      T.image g ∈ variableForcedItemComplex D E r c e a := by
    intro T hT
    have hAbsent : ∀ q ∈ T, ∀ i : Fin k, e ∉ (q.1 i).1 := by
      intro q hq i heq
      have hStock := hT.2 q hq i heq
      exact (Finset.ne_of_mem_erase hStock) rfl
    have hReal : ∀ q ∈ T, ∀ i : Fin k,
        ((g q).1 i).1 ⊆
          if i = a then insert e (q.1 i).1 else (q.1 i).1 := by
      intro q hq i
      rw [hgSpec q (hAbsent q hq) i]
    have hDummy : ∀ q ∈ T, ∀ i : Fin k,
        ((g q).1 i).2 ≤ (q.1 i).2 := by
      intro q hq i
      rw [hgSpec q (hAbsent q hq) i]
    have hOnly : VariableItemOnlyAt T e a := by
      intro i hi hePool
      obtain ⟨_, q, hq, heq⟩ := Finset.mem_filter.mp hePool
      exact hAbsent q hq i heq
    have hFace : IsVariableUnlabeledFamily (T.image g) :=
      variableFace_image_of_inserting_at e a g T hT.1.2
        hReal hDummy hOnly
    refine ⟨⟨⟨Finset.image_nonempty.mpr hT.1.1, hFace⟩, ?_⟩, ?_⟩
    · intro p hp i x hx
      obtain ⟨q, hq, hpq⟩ := Finset.mem_image.mp hp
      subst p
      rw [hgSpec q (hAbsent q hq) i] at hx
      by_cases hi : i = a
      · rw [if_pos hi] at hx
        rcases Finset.mem_insert.mp hx with rfl | hxq
        · exact heE
        · exact (Finset.erase_subset e E) (hT.2 q hq i hxq)
      · rw [if_neg hi] at hx
        exact (Finset.erase_subset e E) (hT.2 q hq i hx)
    · intro p hp
      obtain ⟨q, hq, hpq⟩ := Finset.mem_image.mp hp
      subst p
      rw [hgSpec q (hAbsent q hq) a]
      simp
  have hgf : ∀ S : Finset (VariableUnlabeledVertex k m D r c),
      S ∈ variableForcedItemComplex D E r c e a →
      ∀ p ∈ S, g (f p) = p := by
    intro S hS p hp
    have hqStock := (hForward S hS).2 (f p)
      (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    have hqAbsent : ∀ i : Fin k, e ∉ ((f p).1 i).1 := by
      intro i heq
      exact (Finset.ne_of_mem_erase (hqStock i heq)) rfl
    apply Subtype.ext
    funext i
    apply Prod.ext
    · rw [hgSpec (f p) hqAbsent i, hfSpec p (hS.2 p hp) i]
      by_cases hi : i = a
      · subst i
        simp [hS.2 p hp]
      · simp [hi]
    · rw [hgSpec (f p) hqAbsent i, hfSpec p (hS.2 p hp) i]
  have hfg : ∀ T : Finset (VariableUnlabeledVertex k m D
      (variableDecreasedRequirement r a) c),
      T ∈ variableStockComplex D (E.erase e)
        (variableDecreasedRequirement r a) c →
      ∀ q ∈ T, f (g q) = q := by
    intro T hT q hq
    have hqAbsent : ∀ i : Fin k, e ∉ (q.1 i).1 := by
      intro i heq
      exact (Finset.ne_of_mem_erase (hT.2 q hq i heq)) rfl
    have heAt : e ∈ ((g q).1 a).1 := by
      rw [hgSpec q hqAbsent a]
      simp
    apply Subtype.ext
    funext i
    apply Prod.ext
    · rw [hfSpec (g q) heAt i, hgSpec q hqAbsent i]
      by_cases hi : i = a
      · subst i
        simp [hqAbsent a]
      · simp [hi]
    · rw [hfSpec (g q) heAt i, hgSpec q hqAbsent i]
  exact realizationHomeomorphOfVertexMaps
    (variableForcedItemComplex D E r c e a)
    (variableStockComplex D (E.erase e)
      (variableDecreasedRequirement r a) c)
    f g hForward hBackward hgf hfg

end FairDivision.Topology
