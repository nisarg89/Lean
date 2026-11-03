import FairDivision.Topology.Volovikov.JoinOrbitExtension
import FairDivision.Topology.NerveConnectivity.FiniteCellOrdering

/-!
# Equivariant extension from the vertex skeleton to a finite universal join

Choose a globally smallest missing face of the invariant subcomplex. Its
proper boundary, and in fact the entire previous cardinality skeleton, is
already present. The one-orbit filling theorem then attaches all translates
of that face while preserving continuity and equivariance. Finite descent
on the list of missing faces completes the extension.

This is the geometric half of the finite-join obstruction. It does not assert
that any equivariant map to a representation sphere exists or fails to exist.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped Classical

/-- Adding an orbit of a missing face strictly reduces the finite set of
faces still absent from the full universal join. -/
theorem missingFaces_joinOrbitAttach_ssubset
    {m : ℕ} {G : Type*} [AddGroup G] [Fintype G]
    (B : PreAbstractSimplicialComplex (Fin m × G))
    (R : Finset (Fin m × G))
    (hR : R ∈ universalJoinComplex m G) (hRnot : R ∉ B) :
    missingFaces (B ⊔ joinFaceOrbitComplex R)
      (universalJoinComplex m G) ⊂
      missingFaces B (universalJoinComplex m G) := by
  classical
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro S hS
    have hSK : S ∈ universalJoinComplex m G :=
      ((mem_missingFaces_iff _ _ _).1 hS).1
    have hSnot : S ∉ B ⊔ joinFaceOrbitComplex R :=
      ((mem_missingFaces_iff _ _ _).1 hS).2
    exact (mem_missingFaces_iff _ _ _).2
      ⟨hSK, fun hSB => hSnot (Or.inl hSB)⟩
  · intro heq
    have hRmissing : R ∈ missingFaces B
        (universalJoinComplex m G) :=
      (mem_missingFaces_iff _ _ _).2 ⟨hR, hRnot⟩
    have hRadded : R ∈ B ⊔ joinFaceOrbitComplex R := by
      right
      exact ⟨hR.1, 0, by simp only [translateJoinFace_zero, subset_rfl]⟩
    have hRnotMissing : R ∉ missingFaces
        (B ⊔ joinFaceOrbitComplex R)
        (universalJoinComplex m G) := by
      intro hRmiss
      exact ((mem_missingFaces_iff _ _ _).1 hRmiss).2 hRadded
    exact hRnotMissing (heq.symm ▸ hRmissing)

/-- An equivariant map defined on the vertex skeleton extends over the
whole finite universal join when the target is connected enough for every
new simplex dimension. -/
theorem exists_equivariant_universalJoinExtension
    {m k : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (hm : m ≤ k + 2)
    (hX : NullConnectedSpace k X)
    (targetAction : G → X ≃ₜ X)
    (hAction : IsContinuousAddAction targetAction)
    (base : C(simplicialRealization
      (universalJoinSkeleton m G 1), X))
    (hbase : IsEquivariantJoinMap
      (universalJoinSkeleton m G 1)
      (universalJoinSkeleton_invariant) targetAction base) :
    ∃ f : C(simplicialRealization (universalJoinComplex m G), X),
      (∀ w : simplicialRealization (universalJoinSkeleton m G 1),
        f ⟨w.1, (simplicialRealization_mono
          (show universalJoinSkeleton m G 1 ≤
            universalJoinComplex m G from fun _ h => h.1)) w.2⟩ =
          base w) ∧
      IsEquivariantJoinMap (universalJoinComplex m G)
        (universalJoinComplex_invariant) targetAction f := by
  classical
  let K := universalJoinComplex m G
  let V := universalJoinSkeleton m G 1
  have hVK : V ≤ K := by
    intro S hS
    exact hS.1
  have aux : ∀ n : ℕ,
      ∀ (B : PreAbstractSimplicialComplex (Fin m × G))
        (hBK : B ≤ K) (hVB : V ≤ B)
        (hB : IsJoinTranslationInvariant B),
      (missingFaces B K).card = n →
      ∀ (q : C(simplicialRealization B, X)),
        IsEquivariantJoinMap B hB targetAction q →
        ∃ g : C(simplicialRealization K, X),
          (∀ w : simplicialRealization B,
            g ⟨w.1, (simplicialRealization_mono hBK) w.2⟩ = q w) ∧
          IsEquivariantJoinMap K
            (universalJoinComplex_invariant) targetAction g := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B hBK hVB hB hn q hq
      by_cases hKB : K ≤ B
      · have hEq : B = K := le_antisymm hBK hKB
        subst B
        exact ⟨q, (fun _ => rfl), hq⟩
      · obtain ⟨R, hRK, hRnot, hRne, hminimal⟩ :=
          exists_minimal_missing_face_global B K hKB
        have hRtwo : 2 ≤ R.card := by
          by_contra hnot
          have hRvertex : R ∈ V :=
            ⟨hRK, by omega⟩
          exact hRnot (hVB hRvertex)
        let j := R.card - 2
        have hcard : R.card = j + 2 := by
          dsimp [j]
          omega
        have hj : j ≤ k := by
          have hRm : R.card ≤ m := universalJoinFace_card_le hRK
          dsimp [j]
          omega
        have hOld : universalJoinSkeleton m G (j + 1) ≤ B := by
          intro S hS
          apply hminimal S hS.1
          have hScard : S.card ≤ j + 1 := hS.2
          omega
        let B' := B ⊔ joinFaceOrbitComplex R
        have hB'K : B' ≤ K :=
          sup_le hBK (joinFaceOrbitComplex_le_universalJoinComplex R hRK)
        have hVB' : V ≤ B' := le_trans hVB le_sup_left
        have hB' : IsJoinTranslationInvariant B' :=
          joinOrbitAttach_invariant B hB R
        have hsmaller : (missingFaces B' K).card < n := by
          rw [← hn]
          exact Finset.card_lt_card
            (missingFaces_joinOrbitAttach_ssubset B R hRK hRnot)
        obtain ⟨q', hq', hq'equiv⟩ :=
          exists_equivariant_joinOrbitExtension B hB hOld R hRK
            hcard hRnot hX hj targetAction hAction q hq
        obtain ⟨g, hg, hgequiv⟩ :=
          ih (missingFaces B' K).card hsmaller B'
            hB'K hVB' hB' rfl q' hq'equiv
        refine ⟨g, ?_, hgequiv⟩
        intro w
        calc
          g ⟨w.1, (simplicialRealization_mono hBK) w.2⟩ =
              q' ⟨w.1, (simplicialRealization_mono le_sup_left) w.2⟩ :=
                hg ⟨w.1, (simplicialRealization_mono le_sup_left) w.2⟩
          _ = q w := hq' w
  obtain ⟨f, hf, hfequiv⟩ :=
    aux (missingFaces V K).card V hVK (by intro S hS; exact hS)
      (universalJoinSkeleton_invariant) rfl base hbase
  exact ⟨f, hf, hfequiv⟩

end FairDivision.Topology.Volovikov
