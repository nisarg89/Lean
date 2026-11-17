import FairDivision.Topology.Volovikov.UniversalJoin
import FairDivision.Topology.NerveConnectivity.RealizationEquiv

/-!
# Free continuous action on the finite universal join

The finite complex `G^{*m}` has a probability-simplex realization. Translation
of labels induces a homeomorphism of that realization. A nonzero translation
cannot fix a realized point because its positive support would then be a
nonempty translation-invariant face.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- Translation as a vertex equivalence of the finite universal join. -/
def translateJoinVertexEquiv {m : ℕ} {G : Type*} [AddGroup G]
    (a : G) : (Fin m × G) ≃ (Fin m × G) where
  toFun := translateJoinVertex a
  invFun := translateJoinVertex (-a)
  left_inv := by
    intro v
    rcases v with ⟨i, g⟩
    simp [translateJoinVertex, add_assoc]
  right_inv := by
    intro v
    rcases v with ⟨i, g⟩
    simp [translateJoinVertex, add_assoc]

/-- Translation of group labels is a homeomorphism of `G^{*m}`. -/
noncomputable def translateJoinRealization {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G] (a : G) :
    (simplicialRealization (universalJoinComplex m G)) ≃ₜ
      (simplicialRealization (universalJoinComplex m G)) := by
  classical
  apply realizationHomeomorphOfVertexEquiv
    (universalJoinComplex m G) (universalJoinComplex m G)
    (translateJoinVertexEquiv a)
  · intro S hS
    exact universalJoinFace_translate hS a
  · intro T hT
    exact universalJoinFace_translate hT (-a)

/-- Positive support commutes with a vertex equivalence. -/
theorem finiteSimplexSupport_map_equiv {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (w : stdSimplex ℝ V) :
    FairDivision.Topology.finiteSimplexSupport (stdSimplex.map e w) =
      (FairDivision.Topology.finiteSimplexSupport w).image e := by
  classical
  apply Finset.Subset.antisymm
  · exact finiteSimplexSupport_map_subset e w
  · intro q hq
    obtain ⟨v, hv, hqv⟩ := Finset.mem_image.mp hq
    have hback : w = stdSimplex.map e.symm (stdSimplex.map e w) := by
      calc
        w = stdSimplex.map id w := (stdSimplex.map_id_apply w).symm
        _ = stdSimplex.map (e.symm ∘ e) w := by
          congr 1
          funext x
          exact (e.symm_apply_apply x).symm
        _ = stdSimplex.map e.symm (stdSimplex.map e w) :=
          (stdSimplex.map_comp_apply e e.symm w).symm
    have hv' : v ∈
        (FairDivision.Topology.finiteSimplexSupport (stdSimplex.map e w)).image e.symm := by
      rw [hback] at hv
      exact finiteSimplexSupport_map_subset e.symm (stdSimplex.map e w) hv
    obtain ⟨q', hq', hq'v⟩ := Finset.mem_image.mp hv'
    have hq'e : q' = e v := by
      apply e.symm.injective
      simpa using hq'v
    rw [← hqv, ← hq'e]
    exact hq'


/-- Zero translation is the identity on the universal join realization. -/
theorem translateJoinRealization_zero {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G]
    (x : simplicialRealization (universalJoinComplex m G)) :
    translateJoinRealization (0 : G) x = x := by
  apply Subtype.ext
  change stdSimplex.map (translateJoinVertex (0 : G)) x.1 = x.1
  have hvertex : translateJoinVertex (m := m) (0 : G) = id := by
    funext v
    rcases v with ⟨i, g⟩
    simp [translateJoinVertex]
  rw [hvertex, stdSimplex.map_id_apply]

/-- Translation compositions obey the additive group law on the realization. -/
theorem translateJoinRealization_add {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G] (a b : G)
    (x : simplicialRealization (universalJoinComplex m G)) :
    translateJoinRealization (a + b) x =
      translateJoinRealization a (translateJoinRealization b x) := by
  apply Subtype.ext
  change stdSimplex.map (translateJoinVertex (a + b)) x.1 =
    stdSimplex.map (translateJoinVertex a)
      (stdSimplex.map (translateJoinVertex b) x.1)
  rw [stdSimplex.map_comp_apply]
  congr 1
  funext v
  rcases v with ⟨i, g⟩
  simp [translateJoinVertex, add_assoc]

/-- The action on the realization has no fixed point for a nonzero group
translation. This is stronger than absence of a common fixed point. -/
theorem translateJoinRealization_no_fixed {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G] (a : G) (ha : a ≠ 0)
    (x : simplicialRealization (universalJoinComplex m G)) :
    translateJoinRealization a x ≠ x := by
  intro hx
  classical
  have hsupport : translateJoinFace a
      (FairDivision.Topology.finiteSimplexSupport x.1) =
      FairDivision.Topology.finiteSimplexSupport x.1 := by
    have hval := congrArg Subtype.val hx
    change stdSimplex.map (translateJoinVertexEquiv a) x.1 = x.1 at hval
    have hs := congrArg FairDivision.Topology.finiteSimplexSupport hval
    rw [finiteSimplexSupport_map_equiv] at hs
    exact hs
  exact ha (universalJoinFace_free x.2 a hsupport)

end FairDivision.Topology.Volovikov
