import FairDivision.Finite.DummyRemovalPartition

/-!
# Reindexing nondummy items by a standard finite type

After deleting a finite dummy set, the real stock has `N - |D|` elements.
This module fixes an equivalence with `Fin (N - |D|)` and transports the
augmented owner map. It is purely representational: it changes item names,
not bundles or valuations.
-/

set_option autoImplicit false

namespace FairDivision.Finite

open FairDivision

/-- The nondummy items are canonically reindexed up to a chosen finite
bijection by `Fin (N - |D|)`. -/
noncomputable def realItemEquiv {N : ℕ} (D : Finset (Fin N)) :
    Fin (N - D.card) ≃
      ↥((Finset.univ : Finset (Fin N)) \ D) := by
  have hCard :
      ((Finset.univ : Finset (Fin N)) \ D).card = N - D.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D)]
    simp
  exact (Finset.equivFinOfCardEq hCard).symm

/-- Restrict an augmented allocation to its real items and rename that
stock by the standard finite type. -/
noncomputable def projectedRealAllocation {n N : ℕ}
    (A : Allocation n N) (D : Finset (Fin N)) :
    Allocation n (N - D.card) :=
  fun g => A ((realItemEquiv D g).val)

/-- Pull an augmented bundle back along the real-item equivalence. -/
noncomputable def pullbackRealBundle {N : ℕ}
    (D S : Finset (Fin N)) : Finset (Fin (N - D.card)) :=
  Finset.univ.filter (fun g => (realItemEquiv D g).val ∈ S)

/-- The bundle of the projected allocation is the pullback of its augmented
bundle. -/
theorem bundle_projectedRealAllocation {n N : ℕ}
    (A : Allocation n N) (D : Finset (Fin N)) (i : Fin n) :
    bundle (projectedRealAllocation A D) i =
      pullbackRealBundle D (bundle A i) := by
  apply Finset.ext
  intro g
  change
    (g ∈ (Finset.univ : Finset (Fin (N - D.card))).filter
      (fun g => A ((realItemEquiv D g).val) = i)) ↔
    (g ∈ (Finset.univ : Finset (Fin (N - D.card))).filter
      (fun g => (realItemEquiv D g).val ∈ bundle A i))
  simp [bundle]

/-- Pullback of a bundle ignores all dummy items. -/
theorem pullbackRealBundle_sdiff_dummy {N : ℕ}
    (D S : Finset (Fin N)) :
    pullbackRealBundle D (S \ D) = pullbackRealBundle D S := by
  ext g
  have hReal : (realItemEquiv D g).val ∉ D :=
    (Finset.mem_sdiff.mp (realItemEquiv D g).property).2
  simp [pullbackRealBundle, hReal]

/-- Pullback commutes with deleting an arbitrary augmented item set. -/
theorem pullbackRealBundle_sdiff {N : ℕ}
    (D S E : Finset (Fin N)) :
    pullbackRealBundle D (S \ E) =
      pullbackRealBundle D S \ pullbackRealBundle D E := by
  ext g
  simp [pullbackRealBundle]

/-- Reindexing preserves the cardinality of the nondummy part of a bundle. -/
theorem card_pullbackRealBundle {N : ℕ}
    (D S : Finset (Fin N)) :
    (pullbackRealBundle D S).card = (S \ D).card := by
  let e := realItemEquiv D
  let f : Fin (N - D.card) → Fin N := fun g => (e g).val
  have hf : Function.Injective f := by
    intro g h hgh
    exact e.injective (Subtype.ext hgh)
  have hImage : (pullbackRealBundle D S).image f = S \ D := by
    ext g
    constructor
    · intro hg
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
      have hS : f x ∈ S := by
        simpa [pullbackRealBundle, f, e] using
          (Finset.mem_filter.mp hx).2
      have hD : f x ∉ D :=
        (Finset.mem_sdiff.mp (e x).property).2
      exact Finset.mem_sdiff.mpr ⟨hS, hD⟩
    · intro hg
      have hgS : g ∈ S := (Finset.mem_sdiff.mp hg).1
      have hgD : g ∉ D := (Finset.mem_sdiff.mp hg).2
      let x : Fin (N - D.card) :=
        e.symm ⟨g, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hgD⟩⟩
      refine Finset.mem_image.mpr ⟨x, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change f x ∈ S
        have hx : f x = g := by
          exact congrArg Subtype.val (e.apply_symm_apply
            ⟨g, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hgD⟩⟩)
        rwa [hx]
      · change f x = g
        exact congrArg Subtype.val (e.apply_symm_apply
          ⟨g, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hgD⟩⟩)
  calc
    (pullbackRealBundle D S).card =
        ((pullbackRealBundle D S).image f).card :=
      (Finset.card_image_of_injective _ hf).symm
    _ = (S \ D).card := by rw [hImage]

/-- Pullback preserves subset inclusion. -/
theorem pullbackRealBundle_mono {N : ℕ}
    (D : Finset (Fin N)) {S T : Finset (Fin N)}
    (hST : S ⊆ T) :
    pullbackRealBundle D S ⊆ pullbackRealBundle D T := by
  intro g hg
  simp only [pullbackRealBundle, Finset.mem_filter,
    Finset.mem_univ, true_and] at hg ⊢
  exact hST hg

end FairDivision.Finite
