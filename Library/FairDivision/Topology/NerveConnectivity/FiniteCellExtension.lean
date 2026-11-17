import FairDivision.Topology.NerveConnectivity.FiniteFaceFilling
import FairDivision.Topology.NerveConnectivity.FiniteVertexAttachment
import FairDivision.Topology.NerveConnectivity.FiniteCellOrdering

/-!
# Extending maps over a finite-dimensional simplicial complex

Attach missing faces in order of increasing cardinality. A new vertex gets
an arbitrary target point; every larger face is filled using the target's
operational null-connectivity. This is a generic finite-cell extension
result, independent of the fair-division complexes.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Maps from a subcomplex extend over a finite complex of dimension at
most `k + 1` when the target is null-connected through dimension `k`. -/
theorem exists_finiteComplex_mapExtension
    {V : Type v} [Fintype V]
    {X : Type u} [TopologicalSpace X]
    (K : PreAbstractSimplicialComplex V) (k : ℕ)
    (hKdim : ∀ F : Finset V, F ∈ K → F.card ≤ k + 2)
    (hX : NullConnectedSpace k X)
    (A : PreAbstractSimplicialComplex V) (hAK : A ≤ K)
    (f : C(simplicialRealization A, X)) :
    ∃ g : C(simplicialRealization K, X),
      ∀ w : simplicialRealization A,
        g ⟨w.1, (simplicialRealization_mono hAK) w.2⟩ = f w := by
  classical
  have aux : ∀ n : ℕ,
      ∀ (B : PreAbstractSimplicialComplex V) (hBK : B ≤ K),
      (missingFaces B K).card = n →
      ∀ q : C(simplicialRealization B, X),
        ∃ g : C(simplicialRealization K, X),
          ∀ w : simplicialRealization B,
            g ⟨w.1, (simplicialRealization_mono hBK) w.2⟩ = q w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B hBK hn q
      by_cases hKB : K ≤ B
      · have hEq : B = K := le_antisymm hBK hKB
        subst B
        exact ⟨q, fun _ => rfl⟩
      · obtain ⟨F, hFK, hFB, hFne, hproper⟩ :=
          exists_minimal_missing_face B K hKB
        let B' := B ⊔ fullFaceComplex F
        have hB'K : B' ≤ K :=
          sup_le hBK (fullFaceComplex_le_of_mem K F hFK)
        have hsmaller : (missingFaces B' K).card < n := by
          rw [← hn]
          exact Finset.card_lt_card
            (missingFaces_attach_ssubset B K F hFK hFB)
        obtain ⟨q', hq'⟩ :
            ∃ q' : C(simplicialRealization B', X),
              ∀ w : simplicialRealization B,
                q' ⟨w.1, (simplicialRealization_mono le_sup_left) w.2⟩ = q w := by
          by_cases hFone : F.card = 1
          · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hFone
            subst F
            simpa [B'] using
              (exists_attachVertexMap B v hFB (Classical.choice hX.1) q)
          · have hFtwo : 2 ≤ F.card := by
              have hpos : 0 < F.card := Finset.card_pos.mpr hFne
              omega
            let j := F.card - 2
            have hcard : F.card = j + 2 := by
              dsimp [j]
              omega
            have hj : j ≤ k := by
              have hbound := hKdim F hFK
              dsimp [j]
              omega
            simpa [B'] using
              (exists_attachOneFaceMap_of_nullConnected B F hFne
                hproper hFB j hcard hX hj q)
        obtain ⟨g, hg⟩ :=
          ih (missingFaces B' K).card hsmaller B' hB'K rfl q'
        refine ⟨g, ?_⟩
        intro w
        calc
          g ⟨w.1, (simplicialRealization_mono hBK) w.2⟩ =
              q' ⟨w.1, (simplicialRealization_mono le_sup_left) w.2⟩ :=
                hg ⟨w.1, (simplicialRealization_mono le_sup_left) w.2⟩
          _ = q w := hq' w
  exact aux (missingFaces A K).card A hAK rfl f

end FairDivision.Topology.NerveConnectivity
