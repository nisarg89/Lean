import Mathlib

/-!
# Complete one-item exchange sequences inside a finite pool

This is the finite exchange-chain construction already used by BF's actual
one-skeleton paths, factored out so Section 3 uses the SAME complete sequence
before selecting its first threshold crossing. The path has precisely one
step per item of F\T, retains both endpoints, and never leaves the pool.
The two size parameters let the BF wrapper keep its exact q−1/q interface.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- The finite first subdivision retained explicitly: every neighboring
pair exchanges one item, and no label leaves the original stock. -/
structure BundleExchangeChain {α : Type*} [DecidableEq α] (r q : ℕ)
    (E F T : Finset α) where
  length : ℕ
  bundle : Fin (length + 1) → Finset α
  first : bundle 0 = F
  last : bundle (Fin.last length) = T
  card : ∀ k, (bundle k).card = r
  in_stock : ∀ r, bundle r ⊆ E
  exchange : ∀ k : Fin length,
    (bundle k.castSucc ∪ bundle k.succ).card = q

namespace BundleExchangeChain

def refl {α : Type*} [DecidableEq α] {r q : ℕ} (E F : Finset α)
    (hF : F.card = r) (hFE : F ⊆ E) : BundleExchangeChain r q E F F where
  length := 0
  bundle := fun _ => F
  first := rfl
  last := rfl
  card := fun _ => hF
  in_stock := fun _ => hFE
  exchange := fun k => Fin.elim0 k

/-- Retain the first exchange in the same induction that formerly only
retained an unequally parameterized concatenated path. -/
def prepend {α : Type*} [DecidableEq α] {r q : ℕ} {E F U T : Finset α}
    (chain : BundleExchangeChain r q E U T)
    (hF : F.card = r) (hFE : F ⊆ E)
    (hFU : (F ∪ U).card = q) : BundleExchangeChain r q E F T where
  length := chain.length + 1
  bundle := Fin.cons F chain.bundle
  first := rfl
  last := by simpa using chain.last
  card := by
    intro r
    cases r using Fin.cases with
    | zero => exact hF
    | succ r => exact chain.card r
  in_stock := by
    intro r
    cases r using Fin.cases with
    | zero => exact hFE
    | succ r => exact chain.in_stock r
  exchange := by
    intro k
    cases k using Fin.cases with
    | zero => simpa [chain.first] using hFU
    | succ k => simpa using chain.exchange k

end BundleExchangeChain

/-- Any two r-item bundles in one stock can be joined by the manuscript's
complete sequence of single-item exchanges. No valuation is inspected while
constructing this sequence. -/
theorem exists_bundle_exchange_chain
    {α : Type*} [DecidableEq α] {r q : ℕ}
    (E F T : Finset α)
    (hFull : q = r + 1)
    (hF : F.card = r) (hT : T.card = r)
    (hFE : F ⊆ E) (hTE : T ⊆ E) :
    ∃ chain : BundleExchangeChain r q E F T, chain.length = (F \ T).card := by
  classical
  have aux : ∀ c : ℕ, ∀ F : Finset α,
      F.card = r → F ⊆ E → (F \ T).card = c →
      ∃ chain : BundleExchangeChain r q E F T, chain.length = c := by
    intro c
    induction c using Nat.strong_induction_on with
    | h c ih =>
      intro F hF hFE hdiff
      by_cases hEq : F = T
      · subst F
        refine ⟨BundleExchangeChain.refl E T hT hTE, ?_⟩
        change 0 = c
        simpa only [Finset.sdiff_self, Finset.card_empty] using hdiff
      · have hFnotT : ¬F ⊆ T := by
          intro hsub
          exact hEq (Finset.eq_of_subset_of_card_le hsub
            (by rw [hF, hT]))
        have hTnotF : ¬T ⊆ F := by
          intro hsub
          exact hEq (Finset.eq_of_subset_of_card_le hsub
            (by rw [hF, hT])).symm
        obtain ⟨a, ha⟩ := (Finset.sdiff_nonempty).mpr hFnotT
        obtain ⟨b, hb⟩ := (Finset.sdiff_nonempty).mpr hTnotF
        have haF : a ∈ F := (Finset.mem_sdiff.mp ha).1
        have haT : a ∉ T := (Finset.mem_sdiff.mp ha).2
        have hbT : b ∈ T := (Finset.mem_sdiff.mp hb).1
        have hbF : b ∉ F := (Finset.mem_sdiff.mp hb).2
        let U : Finset α := insert b (F.erase a)
        have hUcard : U.card = r := by
          have hFpos : 0 < F.card := Finset.card_pos.mpr ⟨a, haF⟩
          have hbErase : b ∉ F.erase a := by
            intro hbErase
            exact hbF (Finset.mem_of_mem_erase hbErase)
          change (insert b (F.erase a)).card = r
          rw [Finset.card_insert_of_notMem hbErase,Finset.card_erase_of_mem haF,hF]
          rw [hF] at hFpos
          omega
        have hUE : U ⊆ E := by
          intro g hg
          rcases Finset.mem_insert.mp hg with hgb | hg
          · rw [hgb]
            exact hTE hbT
          · exact hFE (Finset.mem_of_mem_erase hg)
        have hUnionEq : F ∪ U = insert b F := by
          ext g
          simp only [U, Finset.mem_union, Finset.mem_insert,
            Finset.mem_erase]
          tauto
        have hUnionCard : (F ∪ U).card = q := by
          rw [hUnionEq, Finset.card_insert_of_notMem hbF, hF]
          omega
        have hdiffEq : U \ T = (F \ T).erase a := by
          ext g
          simp only [U, Finset.mem_sdiff, Finset.mem_insert,
            Finset.mem_erase]
          constructor
          · rintro ⟨h, hgT⟩
            rcases h with hgb | ⟨hga, hgF⟩
            · exact False.elim (hgT (by rw [hgb]; exact hbT))
            · exact ⟨hga, hgF, hgT⟩
          · rintro ⟨hga, hgF, hgT⟩
            exact ⟨Or.inr ⟨hga, hgF⟩, hgT⟩
        have hlt : (U \ T).card < c := by
          rw [hdiffEq, Finset.card_erase_of_mem ha, hdiff]
          have hcpos : 0 < c := by
            rw [← hdiff]
            exact Finset.card_pos.mpr ⟨a, ha⟩
          omega
        obtain ⟨chain, hlength⟩ := ih (U \ T).card hlt U hUcard hUE rfl
        refine ⟨chain.prepend hF hFE hUnionCard, ?_⟩
        change chain.length + 1 = c
        rw [hlength, hdiffEq, Finset.card_erase_of_mem ha, hdiff]
        have hcpos : 0 < c := by
          rw [← hdiff]
          exact Finset.card_pos.mpr ⟨a, ha⟩
        omega
  exact aux (F \ T).card F hF hFE rfl


/-- The entire chosen sequence, including both endpoints. It is formed
before any valuation or threshold is inspected. -/
def BundleExchangeChain.toList {α : Type*} [DecidableEq α] {r q : ℕ}
    {E F T : Finset α} (chain : BundleExchangeChain r q E F T) : List (Finset α) :=
  List.ofFn chain.bundle

@[simp] theorem BundleExchangeChain.toList_length
    {α : Type*} [DecidableEq α] {r q : ℕ} {E F T : Finset α}
    (chain : BundleExchangeChain r q E F T) : chain.toList.length = chain.length + 1 := by
  simp [BundleExchangeChain.toList]

/-- Recover the literal removed and inserted items at any step of the
complete sequence. This uses only its existing equal-size/union certificates.
-/
theorem BundleExchangeChain.step
    {α : Type*} [DecidableEq α] {r q : ℕ} {E F T : Finset α}
    (chain : BundleExchangeChain r q E F T) (hFull : q = r + 1)
    (k : Fin chain.length) :
    ∃ a ∈ chain.bundle k.castSucc, ∃ b ∈ E \ chain.bundle k.castSucc,
      chain.bundle k.succ = insert b ((chain.bundle k.castSucc).erase a) := by
  classical
  let L := chain.bundle k.castSucc
  let R := chain.bundle k.succ
  have hL : L.card = r := chain.card k.castSucc
  have hR : R.card = r := chain.card k.succ
  have hUnion : (L ∪ R).card = q := chain.exchange k
  have hLeftCard : (L \ R).card = 1 := by
    have hCount := Finset.card_sdiff_add_card L R
    omega
  have hRightCard : (R \ L).card = 1 := by
    have hCount := Finset.card_sdiff_add_card R L
    have hUnion' : (R ∪ L).card = q := by simpa only [Finset.union_comm] using hUnion
    omega
  obtain ⟨a,haDiff⟩ := Finset.card_eq_one.mp hLeftCard
  obtain ⟨b,hbDiff⟩ := Finset.card_eq_one.mp hRightCard
  have ha : a ∈ L ∧ a ∉ R := Finset.mem_sdiff.mp (by rw [haDiff]; simp)
  have hb : b ∈ R ∧ b ∉ L := Finset.mem_sdiff.mp (by rw [hbDiff]; simp)
  refine ⟨a,ha.1,b,Finset.mem_sdiff.mpr ⟨chain.in_stock k.succ hb.1,hb.2⟩,?_⟩
  change R = insert b (L.erase a)
  ext x
  simp only [Finset.mem_insert,Finset.mem_erase]
  constructor
  · intro hxR
    by_cases hxb : x = b
    · exact Or.inl hxb
    · right
      have hxL : x ∈ L := by
        by_contra hxL
        have hxDiff : x ∈ R \ L := Finset.mem_sdiff.mpr ⟨hxR,hxL⟩
        rw [hbDiff] at hxDiff
        exact hxb (Finset.mem_singleton.mp hxDiff)
      have hxa : x ≠ a := by
        intro hEq
        exact ha.2 (by rw [← hEq]; exact hxR)
      exact ⟨hxa,hxL⟩
  · rintro (hxb | ⟨hxa,hxL⟩)
    · rw [hxb]
      exact hb.1
    · by_contra hxR
      have hxDiff : x ∈ L \ R := Finset.mem_sdiff.mpr ⟨hxL,hxR⟩
      rw [haDiff] at hxDiff
      exact hxa (Finset.mem_singleton.mp hxDiff)

end FairDivision.Finite
