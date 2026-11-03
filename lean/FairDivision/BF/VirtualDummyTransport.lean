import FairDivision.Topology.UnlabeledMarginalFin
import FairDivision.Finite.DummyRemovalReindex
import FairDivision.BF.VirtualValuationSpec
import FairDivision.Topology.UnlabeledReducedMarginal

/-!
# From the common marginal placeholder to a position's actual dummy

The BF virtual valuation sees every dummy as the same zero coordinate in
`Fin (m+1)`. A compatible auxiliary face has at most one actual dummy in a
position's pool. This module changes that zero coordinate to the selected
actual label while preserving the real-item reindexing used at the final
dummy-removal step.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Topology
open FairDivision.Finite

/-- Send the virtual dummy coordinate to a chosen actual dummy, and each
real coordinate to its existing nondummy label. -/
noncomputable def actualMarginalItem {N : ℕ}
    (D : Finset (Fin N)) (dummy : Fin N) :
    Fin (N - D.card + 1) → Fin N :=
  fun a => match finSuccEquiv (N - D.card) a with
    | none => dummy
    | some g => (realItemEquiv D g).val

@[simp] theorem actualMarginalItem_zero {N : ℕ}
    (D : Finset (Fin N)) (dummy : Fin N) :
    actualMarginalItem D dummy 0 = dummy := by
  simp [actualMarginalItem, finSuccEquiv_zero]

@[simp] theorem actualMarginalItem_succ {N : ℕ}
    (D : Finset (Fin N)) (dummy : Fin N)
    (g : Fin (N - D.card)) :
    actualMarginalItem D dummy g.succ = (realItemEquiv D g).val := by
  simp [actualMarginalItem, finSuccEquiv_succ]

/-- Real labels stay outside the actual dummy set. -/
theorem actualMarginalItem_succ_not_dummy {N : ℕ}
    (D : Finset (Fin N)) (dummy : Fin N)
    (g : Fin (N - D.card)) :
    actualMarginalItem D dummy g.succ ∉ D := by
  rw [actualMarginalItem_succ]
  exact (Finset.mem_sdiff.mp (realItemEquiv D g).property).2

/-- The placeholder-and-real-label translation is injective when the chosen
actual placeholder is a dummy. -/
theorem actualMarginalItem_injective {N : ℕ}
    (D : Finset (Fin N)) (dummy : Fin N) (hdummy : dummy ∈ D) :
    Function.Injective (actualMarginalItem D dummy) := by
  intro a b hab
  cases a using Fin.cases with
  | zero =>
      cases b using Fin.cases with
      | zero => rfl
      | succ b =>
          have hnot := actualMarginalItem_succ_not_dummy D dummy b
          rw [actualMarginalItem_zero] at hab
          exact False.elim (hnot (hab ▸ hdummy))
  | succ a =>
      cases b using Fin.cases with
      | zero =>
          have hnot := actualMarginalItem_succ_not_dummy D dummy a
          rw [actualMarginalItem_zero] at hab
          exact False.elim (hnot (hab.symm ▸ hdummy))
      | succ b =>
          simp only [actualMarginalItem_succ] at hab
          have h : realItemEquiv D a = realItemEquiv D b :=
            Subtype.ext hab
          exact congrArg Fin.succ ((realItemEquiv D).injective h)

/-- Pulling an actual image back to real-item indices removes the virtual
dummy exactly, even when that dummy has an arbitrary actual label. -/
theorem pullbackRealBundle_actualMarginalItem_image {N : ℕ}
    (D : Finset (Fin N)) (dummy : Fin N) (hdummy : dummy ∈ D)
    (S : Finset (Fin (N - D.card + 1))) :
    pullbackRealBundle D (S.image (actualMarginalItem D dummy)) =
      marginalRealPart S := by
  ext g
  simp only [pullbackRealBundle, marginalRealPart, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hg
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hg
    have hga : actualMarginalItem D dummy a =
        actualMarginalItem D dummy g.succ := by
      simpa only [actualMarginalItem_succ] using heq
    exact (actualMarginalItem_injective D dummy hdummy hga) ▸ ha
  · intro hg
    exact Finset.mem_image.mpr
      ⟨g.succ, hg, actualMarginalItem_succ D dummy g⟩

/-- Relabel every item in an owner witness by an injection. This transports
its short and full bundles, deletion witnesses, and shortening certificate. -/
noncomputable def OwnerWitness.image
    {n m N q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin N) → ℝ}
    {E : Finset (Fin m)} {u : Fin n → ℝ} {owner : Fin n}
    (f : Fin m → Fin N) (hf : Function.Injective f)
    (h : OwnerWitness q dummy
      (fun j S => v j (S.image f)) E u owner) :
    OwnerWitness q (f dummy) v (E.image f) u owner := by
  classical
  refine {
    B := h.B.image f
    lowerSet := h.lowerSet.image f
    upperSet := h.upperSet.image f
    in_stock := Finset.image_subset_image h.in_stock
    size := ?_
    lower_subset := Finset.image_subset_image h.lower_subset
    upper_subset := Finset.image_subset_image h.upper_subset
    lower_size := ?_
    upper_size := ?_
    lower_bound := ?_
    owner_bound := h.owner_bound
    short_sets := ?_
    shortening := ?_
  }
  · rcases h.size with hShort | hFull
    · exact Or.inl (by simpa only [Finset.card_image_of_injective _ hf] using hShort)
    · exact Or.inr (by simpa only [Finset.card_image_of_injective _ hf] using hFull)
  · simpa only [Finset.card_image_of_injective _ hf] using h.lower_size
  · simpa only [Finset.card_image_of_injective _ hf] using h.upper_size
  · exact h.lower_bound
  · intro hShort
    have hShort' : h.B.card = q - 1 := by
      simpa only [Finset.card_image_of_injective _ hf] using hShort
    obtain ⟨hLower, hUpper⟩ := h.short_sets hShort'
    exact ⟨congrArg (fun S : Finset (Fin m) => S.image f) hLower,
      congrArg (fun S : Finset (Fin m) => S.image f) hUpper⟩
  · intro hFull hNoDummy
    have hFull' : h.B.card = q := by
      simpa only [Finset.card_image_of_injective _ hf] using hFull
    have hNoDummy' : dummy ∉ h.B := by
      intro hd
      exact hNoDummy (Finset.mem_image.mpr ⟨dummy, hd, rfl⟩)
    obtain ⟨C, hCB, hCard, hLower, hUpper⟩ :=
      h.shortening hFull' hNoDummy'
    refine ⟨C.image f, Finset.image_subset_image hCB, ?_, ?_, ?_⟩
    · simpa only [Finset.card_image_of_injective _ hf] using hCard
    · intro j
      obtain ⟨Z, hZ, hVal⟩ := hLower j
      refine ⟨Z.image f, ?_, ?_⟩
      · exact ⟨Finset.image_subset_image hZ.1,
          (by simpa only [Finset.card_image_of_injective _ hf] using hZ.2)⟩
      · simpa only [← Finset.image_sdiff C Z hf] using hVal
    · obtain ⟨Z, hZ, hVal⟩ := hUpper
      refine ⟨Z.image f, ?_, ?_⟩
      · exact ⟨Finset.image_subset_image hZ.1,
          (by simpa only [Finset.card_image_of_injective _ hf] using hZ.2)⟩
      · simpa only [← Finset.image_sdiff C Z hf] using hVal

/-- A virtual owner witness can use an actual dummy label without changing
any real-item valuation. The resulting bundle stays in the translated stock. -/
noncomputable def OwnerWitness.actualDummy
    {n N q : ℕ} (D : Finset (Fin N))
    (dummy : Fin N) (hdummy : dummy ∈ D)
    (v : Fin n → Finset (Fin (N - D.card)) → ℝ)
    (E : Finset (Fin (N - D.card + 1)))
    (u : Fin n → ℝ) (owner : Fin n)
    (h : OwnerWitness q 0
      (fun j S => v j (marginalRealPart S)) E u owner) :
    OwnerWitness q dummy
      (fun j S => v j (pullbackRealBundle D S))
      (E.image (actualMarginalItem D dummy)) u owner := by
  have hval :
      (fun j S => v j
        (pullbackRealBundle D (S.image (actualMarginalItem D dummy)))) =
      (fun j S => v j (marginalRealPart S)) := by
    funext j S
    rw [pullbackRealBundle_actualMarginalItem_image D dummy hdummy S]
  have h' : OwnerWitness q 0
      (fun j S => v j
        (pullbackRealBundle D (S.image (actualMarginalItem D dummy))))
      E u owner := by
    rw [hval]
    exact h
  simpa only [actualMarginalItem_zero] using
    (OwnerWitness.image
      (v := fun j S => v j (pullbackRealBundle D S))
      (actualMarginalItem D dummy)
      (actualMarginalItem_injective D dummy hdummy) h')

/-- To place all translated bundles in an actual position pool, it suffices
that the chosen dummy is available when zero occurs and that every supported
real coordinate has its corresponding actual item in the pool. -/
theorem actualMarginalItem_image_subset
    {N : ℕ} (D : Finset (Fin N)) (dummy : Fin N)
    (S : Finset (Fin (N - D.card + 1))) (P : Finset (Fin N))
    (hZero : (0 : Fin (N - D.card + 1)) ∈ S → dummy ∈ P)
    (hReal : ∀ g : Fin (N - D.card),
      g.succ ∈ S → (realItemEquiv D g).val ∈ P) :
    S.image (actualMarginalItem D dummy) ⊆ P := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
  cases a using Fin.cases with
  | zero => simpa only [actualMarginalItem_zero] using hZero ha
  | succ g => simpa only [actualMarginalItem_succ] using hReal g ha

/-- The admissibility guarantee of the virtual valuation supplies an actual
owner witness in any compatible pool containing the translated support union. -/
theorem virtualScore_ownerWitness_in_actualPool
    {n N q : ℕ} (D : Finset (Fin N))
    (v : Fin n → Finset (Fin (N - D.card)) → ℝ)
    (spec : VirtualValuationSpec (q := q) v)
    (x : stdSimplex ℝ (FixedFinMarginalBundle (N - D.card) (q - 1)))
    (P : Finset (Fin N))
    (dummy : Fin N) (hdummy : dummy ∈ D)
    (hStock : (finMarginalStock x).image
      (actualMarginalItem D dummy) ⊆ P)
    (owner : Fin n) :
    Nonempty (OwnerWitness q dummy
      (fun j S => v j (pullbackRealBundle D S))
      P (spec.score x) owner) := by
  obtain ⟨h⟩ := spec.admissible_score x owner
  exact ⟨(OwnerWitness.actualDummy D dummy hdummy v
    (finMarginalStock x) (spec.score x) owner h).enlarge hStock⟩

/-- Every item in the support union of a reduced marginal occurs in a
supported auxiliary vertex at that position. -/
theorem exists_source_of_reducedMarginalStock_mem {k N r : ℕ}
    {D : Finset (Fin N)}
    (x : unlabeledLotterySpace k N r 1 D) (i : Fin k)
    (g : Fin (N - D.card + 1))
    (hg : g ∈ finMarginalStock
      (unlabeledReducedMarginal i x)) :
    ∃ p ∈ unlabeledLotterySupport x.1,
      g ∈ (reducedMarginalVertex p i).1 := by
  classical
  obtain ⟨B, hB, hgB⟩ := Finset.mem_biUnion.mp hg
  obtain ⟨p, hp, hpB⟩ :=
    exists_source_of_reducedMarginal_support x i B hB
  refine ⟨p, hp, ?_⟩
  rw [hpB]
  exact hgB

end FairDivision.BF
