import FairDivision.BF.HeterogeneousAdmissibility

/-!
# BF Section 5: continuous paths between neighboring bundle scores

The two exchange paths here are exactly the ones in the manuscript's virtual
valuation lemma. A segment stays inside the coordinatewise interval between
its endpoints; the previously proved admissibility lemmas certify each bend.
The dummy-containing path has two segments, and the dummy-free path has four.
-/

set_option autoImplicit false

namespace FairDivision.BF

private theorem segment_interval {n : ℕ} {lo hi a b : Fin n → ℝ}
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi)
    (t : unitInterval) :
    lo ≤ (Path.segment a b) t ∧ (Path.segment a b) t ≤ hi := by
  have ht : (Path.segment a b) t ∈ Set.range (Path.segment a b) := ⟨t, rfl⟩
  rw [Path.range_segment] at ht
  exact (convex_Icc lo hi).segment_subset ha hb ht

private theorem path_property_trans {n : ℕ} {a b c : Fin n → ℝ}
    (P : (Fin n → ℝ) → Prop) (γ : Path a b) (δ : Path b c)
    (hγ : ∀ t, P (γ t)) (hδ : ∀ t, P (δ t)) :
    ∀ t, P ((γ.trans δ) t) := by
  intro t
  have ht : (γ.trans δ) t ∈ Set.range (γ.trans δ) := ⟨t, rfl⟩
  rw [Path.trans_range] at ht
  rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact hs ▸ hγ s
  · exact hs ▸ hδ s

/-- The manuscript's literal subdivision: halves when the union contains
its dummy, and quarters otherwise. All agents use this one vector path. -/
noncomputable def manuscriptExchangePath
    {n m : ℕ} (dummy : Fin m)
    (v : Fin n → Finset (Fin m) → ℝ) (F T : Finset (Fin m)) :
    Path (fun j => v j F) (fun j => v j T) := by
  classical
  let a : Fin n → ℝ := fun j => v j F
  let b : Fin n → ℝ := fun j => v j T
  let c : Fin n → ℝ := fun j => v j (F ∩ T)
  let top : Fin n → ℝ := fun j => max (a j) (b j)
  let first : Fin n → ℝ := fun j => max (a j) (min (b j) (c j))
  let last : Fin n → ℝ := fun j => max (b j) (min (a j) (c j))
  exact if dummy ∈ F ∪ T then
    (Path.segment a top).trans (Path.segment top b)
  else
    ((Path.segment a first).trans (Path.segment first top)).trans
      ((Path.segment top last).trans (Path.segment last b))

private theorem path_trans_half {X : Type*} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (r : Path b c) :
    (p.trans r) ⟨1 / 2, by norm_num⟩ = b := by
  rw [Path.trans_apply, dif_pos (by norm_num)]
  convert p.target using 1
  congr 1
  apply Subtype.ext
  norm_num

private theorem balanced_path_quarter {X : Type*} [TopologicalSpace X]
    {a b c d e : X} (p₁ : Path a b) (p₂ : Path b c)
    (p₃ : Path c d) (p₄ : Path d e) :
    ((p₁.trans p₂).trans (p₃.trans p₄)) ⟨1 / 4, by norm_num⟩ = b := by
  rw [Path.trans_apply, dif_pos (by norm_num)]
  convert path_trans_half p₁ p₂ using 1
  congr 1
  apply Subtype.ext
  norm_num

private theorem balanced_path_threeQuarter {X : Type*} [TopologicalSpace X]
    {a b c d e : X} (p₁ : Path a b) (p₂ : Path b c)
    (p₃ : Path c d) (p₄ : Path d e) :
    ((p₁.trans p₂).trans (p₃.trans p₄)) ⟨3 / 4, by norm_num⟩ = d := by
  rw [Path.trans_apply, dif_neg (by norm_num)]
  convert path_trans_half p₃ p₄ using 1
  congr 1
  apply Subtype.ext
  norm_num

/-- The actual common midpoint is the coordinatewise endpoint maximum. -/
theorem manuscriptExchangePath_midpoint
    {n m : ℕ} (dummy : Fin m)
    (v : Fin n → Finset (Fin m) → ℝ) (F T : Finset (Fin m)) :
    manuscriptExchangePath dummy v F T ⟨1 / 2, by norm_num⟩ =
      fun j => max (v j F) (v j T) := by
  classical
  by_cases hd : dummy ∈ F ∪ T
  · simp only [manuscriptExchangePath, if_pos hd]
    exact path_trans_half _ _
  · simp only [manuscriptExchangePath, if_neg hd]
    exact path_trans_half _ _

/-- Literal quarter-point prescription in the dummy-free case. -/
theorem manuscriptExchangePath_quarter
    {n m : ℕ} (dummy : Fin m)
    (v : Fin n → Finset (Fin m) → ℝ) (F T : Finset (Fin m))
    (hd : dummy ∉ F ∪ T) :
    manuscriptExchangePath dummy v F T ⟨1 / 4, by norm_num⟩ =
      fun j => max (v j F) (min (v j T) (v j (F ∩ T))) := by
  classical
  simp only [manuscriptExchangePath, if_neg hd]
  exact balanced_path_quarter _ _ _ _

/-- Literal three-quarter-point prescription in the dummy-free case. -/
theorem manuscriptExchangePath_threeQuarter
    {n m : ℕ} (dummy : Fin m)
    (v : Fin n → Finset (Fin m) → ℝ) (F T : Finset (Fin m))
    (hd : dummy ∉ F ∪ T) :
    manuscriptExchangePath dummy v F T ⟨3 / 4, by norm_num⟩ =
      fun j => max (v j T) (min (v j F) (v j (F ∩ T))) := by
  classical
  simp only [manuscriptExchangePath, if_neg hd]
  exact balanced_path_threeQuarter _ _ _ _

/-- The manuscript's two- or four-segment score path for neighboring
`(q-1)`-bundles. Every point is admissible using only their union. -/
theorem manuscriptExchangePath_admissible
    {n m q : ℕ} (dummy : Fin m)
    (v : Fin n → Finset (Fin m) → ℝ)
    (E F T : Finset (Fin m))
    (hq : 1 ≤ q)
    (hF : F.card = q - 1) (hT : T.card = q - 1)
    (hUnion : (F ∪ T).card = q)
    (hFE : F ⊆ E) (hTE : T ⊆ E) :
    ∀ t, IsAdmissible q dummy v E (manuscriptExchangePath dummy v F T t) := by
  let a : Fin n → ℝ := fun j => v j F
  let b : Fin n → ℝ := fun j => v j T
  let c : Fin n → ℝ := fun j => v j (F ∩ T)
  let top : Fin n → ℝ := fun j => max (a j) (b j)
  have haTop : a ≤ top := fun j => le_max_left _ _
  have hbTop : b ≤ top := fun j => le_max_right _ _
  by_cases hDummy : dummy ∈ F ∪ T
  · let p : Path a top := Path.segment a top
    let r : Path top b := Path.segment top b
    simp only [manuscriptExchangePath, if_pos hDummy]
    change ∀ t, IsAdmissible q dummy v E ((p.trans r) t)
    exact path_property_trans (fun u => IsAdmissible q dummy v E u) p r
      (by
        intro t
        have ht := segment_interval (lo := a) (hi := top)
          (a := a) (b := top) ⟨le_refl _, haTop⟩
          ⟨haTop, le_refl _⟩ t
        exact isAdmissible_dummyUnion_ascent dummy v E F T (p t)
          hq hF hT hUnion hDummy hFE hTE
          (fun j => ht.1 j) (fun j => ht.2 j))
      (by
        intro t
        have ht := segment_interval (lo := b) (hi := top)
          (a := top) (b := b) ⟨hbTop, le_refl _⟩
          ⟨le_refl _, hbTop⟩ t
        have hUnion' : (T ∪ F).card = q := by
          simpa only [Finset.union_comm] using hUnion
        have hDummy' : dummy ∈ T ∪ F := by
          simpa only [Finset.union_comm] using hDummy
        apply isAdmissible_dummyUnion_ascent dummy v E T F (r t)
          hq hT hF hUnion' hDummy' hTE hFE
        · intro j
          exact ht.1 j
        · intro j
          simpa only [top, a, b, max_comm] using ht.2 j)
  · let first : Fin n → ℝ :=
      fun j => max (a j) (min (b j) (c j))
    let last : Fin n → ℝ :=
      fun j => max (b j) (min (a j) (c j))
    have haFirst : a ≤ first := fun j => le_max_left _ _
    have hFirstTop : first ≤ top := by
      intro j
      exact max_le (le_max_left _ _)
        ((min_le_left _ _).trans (le_max_right _ _))
    have hbLast : b ≤ last := fun j => le_max_left _ _
    have hLastTop : last ≤ top := by
      intro j
      exact max_le (le_max_right _ _)
        ((min_le_left _ _).trans (le_max_left _ _))
    let p₁ : Path a first := Path.segment a first
    let p₂ : Path first top := Path.segment first top
    let p₃ : Path top last := Path.segment top last
    let p₄ : Path last b := Path.segment last b
    let P : (Fin n → ℝ) → Prop := IsAdmissible q dummy v E
    have hp₁ : ∀ t, P (p₁ t) := by
      intro t
      have ht := segment_interval (lo := a) (hi := first)
        (a := a) (b := first) ⟨le_refl _, haFirst⟩
        ⟨haFirst, le_refl _⟩ t
      exact isAdmissible_exchange_firstBend dummy v E F T (p₁ t)
        hq hF hT hUnion hFE hTE
        (fun j => ht.1 j) (fun j => ht.2 j)
    have hp₂ : ∀ t, P (p₂ t) := by
      intro t
      have ht := segment_interval (lo := first) (hi := top)
        (a := first) (b := top) ⟨le_refl _, hFirstTop⟩
        ⟨hFirstTop, le_refl _⟩ t
      exact isAdmissible_exchange_secondBend dummy v E F T (p₂ t)
        hq hF hT hUnion hFE hTE
        (fun j => ht.1 j) (fun j => ht.2 j)
    have hp₃ : ∀ t, P (p₃ t) := by
      intro t
      have ht := segment_interval (lo := last) (hi := top)
        (a := top) (b := last) ⟨hLastTop, le_refl _⟩
        ⟨le_refl _, hLastTop⟩ t
      have hUnion' : (T ∪ F).card = q := by
        simpa only [Finset.union_comm] using hUnion
      apply isAdmissible_exchange_secondBend dummy v E T F (p₃ t)
        hq hT hF hUnion' hTE hFE
      · intro j
        simpa only [last, a, b, c, Finset.inter_comm] using ht.1 j
      · intro j
        simpa only [top, a, b, max_comm] using ht.2 j
    have hp₄ : ∀ t, P (p₄ t) := by
      intro t
      have ht := segment_interval (lo := b) (hi := last)
        (a := last) (b := b) ⟨hbLast, le_refl _⟩
        ⟨le_refl _, hbLast⟩ t
      have hUnion' : (T ∪ F).card = q := by
        simpa only [Finset.union_comm] using hUnion
      apply isAdmissible_exchange_firstBend dummy v E T F (p₄ t)
        hq hT hF hUnion' hTE hFE
      · intro j
        exact ht.1 j
      · intro j
        simpa only [last, a, b, c, Finset.inter_comm] using ht.2 j
    simp only [manuscriptExchangePath, if_neg hDummy]
    change ∀ t, P (((p₁.trans p₂).trans (p₃.trans p₄)) t)
    exact path_property_trans P (p₁.trans p₂) (p₃.trans p₄)
      (path_property_trans P p₁ p₂ hp₁ hp₂)
      (path_property_trans P p₃ p₄ hp₃ hp₄)

/-- Compatibility wrapper for earlier callers. The witness is now the named
literal-quarter path, retaining all original local admissibility arguments. -/
theorem exists_admissible_exchange_path
    {n m q : ℕ} (dummy : Fin m)
    (v : Fin n → Finset (Fin m) → ℝ)
    (E F T : Finset (Fin m))
    (hq : 1 ≤ q)
    (hF : F.card = q - 1) (hT : T.card = q - 1)
    (hUnion : (F ∪ T).card = q)
    (hFE : F ⊆ E) (hTE : T ⊆ E) :
    ∃ γ : Path (fun j => v j F) (fun j => v j T),
      ∀ t, IsAdmissible q dummy v E (γ t) :=
  ⟨manuscriptExchangePath dummy v F T,
    manuscriptExchangePath_admissible dummy v E F T hq hF hT hUnion hFE hTE⟩

end FairDivision.BF
