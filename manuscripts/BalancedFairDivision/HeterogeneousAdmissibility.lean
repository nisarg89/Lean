import FairDivision.Definitions

/-!
# Admissible virtual valuation vectors for BF Section 5

This encodes the bundle, lower, upper, and shortening certificates in the
manuscript's virtual-valuation lemma. Its first closure observation says that
admissibility survives enlargement of the available item set and
coordinatewise maxima. The construction of the continuous virtual valuation
map will use these facts on higher-dimensional faces.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision

/-- For one specified owner, a vector of virtual values has a bundle in the
available stock with one lower witness for all observers and one upper
witness for the owner. A full dummy-free bundle also carries the paper's
shortening certificate. -/
structure OwnerWitness {n m : ℕ}
    (q : ℕ) (dummy : Fin m)
    (v : Fin n → Finset (Fin m) → ℝ)
    (E : Finset (Fin m)) (u : Fin n → ℝ) (owner : Fin n) where
  B : Finset (Fin m)
  lowerSet : Finset (Fin m)
  upperSet : Finset (Fin m)
  in_stock : B ⊆ E
  size : B.card = q - 1 ∨ B.card = q
  lower_subset : lowerSet ⊆ B
  upper_subset : upperSet ⊆ B
  lower_size : lowerSet.card = q - 1
  upper_size : upperSet.card = q - 1
  lower_bound : ∀ j : Fin n, v j lowerSet ≤ u j
  owner_bound : u owner ≤ v owner upperSet
  short_sets : B.card = q - 1 → lowerSet = B ∧ upperSet = B
  shortening : B.card = q → dummy ∉ B →
    ∃ C : Finset (Fin m),
      C ⊆ B ∧ C.card = q - 1 ∧
      (∀ j : Fin n, ∃ D : Finset (Fin m),
        CanDeleteOne D C ∧ v j (C \ D) ≤ u j) ∧
      (∃ D : Finset (Fin m),
        CanDeleteOne D C ∧ u owner ≤ v owner (C \ D))

/-- The virtual-value vector is admissible within `E` when every possible
owner has a certificate. -/
def IsAdmissible {n m : ℕ}
    (q : ℕ) (dummy : Fin m)
    (v : Fin n → Finset (Fin m) → ℝ)
    (E : Finset (Fin m)) (u : Fin n → ℝ) : Prop :=
  ∀ owner : Fin n, Nonempty (OwnerWitness q dummy v E u owner)

/-- A certificate remains valid if more items become available. -/
def OwnerWitness.enlarge {n m q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E E' : Finset (Fin m)} {u : Fin n → ℝ} {owner : Fin n}
    (h : OwnerWitness q dummy v E u owner) (hEE' : E ⊆ E') :
    OwnerWitness q dummy v E' u owner where
  B := h.B
  lowerSet := h.lowerSet
  upperSet := h.upperSet
  in_stock := h.in_stock.trans hEE'
  size := h.size
  lower_subset := h.lower_subset
  upper_subset := h.upper_subset
  lower_size := h.lower_size
  upper_size := h.upper_size
  lower_bound := h.lower_bound
  owner_bound := h.owner_bound
  short_sets := h.short_sets
  shortening := h.shortening

/-- Increase every lower threshold while keeping the chosen owner's
threshold fixed. The same bundle and shortening witnesses still work. -/
def OwnerWitness.weaken {n m q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Finset (Fin m)} {u w : Fin n → ℝ} {owner : Fin n}
    (h : OwnerWitness q dummy v E u owner)
    (huw : ∀ j : Fin n, u j ≤ w j) (heq : u owner = w owner) :
    OwnerWitness q dummy v E w owner where
  B := h.B
  lowerSet := h.lowerSet
  upperSet := h.upperSet
  in_stock := h.in_stock
  size := h.size
  lower_subset := h.lower_subset
  upper_subset := h.upper_subset
  lower_size := h.lower_size
  upper_size := h.upper_size
  lower_bound := fun j => (h.lower_bound j).trans (huw j)
  owner_bound := by
    calc
      w owner = u owner := heq.symm
      _ ≤ v owner h.upperSet := h.owner_bound
  short_sets := h.short_sets
  shortening := by
    intro hsize hd
    obtain ⟨C, hCB, hCsize, hlow, hup⟩ := h.shortening hsize hd
    refine ⟨C, hCB, hCsize, ?_, ?_⟩
    · intro j
      obtain ⟨D, hD, hDval⟩ := hlow j
      exact ⟨D, hD, hDval.trans (huw j)⟩
    · obtain ⟨D, hD, hDval⟩ := hup
      refine ⟨D, hD, ?_⟩
      calc
        w owner = u owner := heq.symm
        _ ≤ v owner (C \ D) := hDval

/-- Admissibility is preserved as the available stock grows. -/
theorem isAdmissible_mono {n m q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E E' : Finset (Fin m)} {u : Fin n → ℝ}
    (hEE' : E ⊆ E') (hu : IsAdmissible q dummy v E u) :
    IsAdmissible q dummy v E' u := by
  intro owner
  obtain ⟨h⟩ := hu owner
  exact ⟨h.enlarge hEE'⟩

/-- The coordinatewise maximum of two vectors admissible within the same
stock is admissible there. For each owner, use the operand attaining that
owner's maximum. -/
theorem isAdmissible_max {n m q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Finset (Fin m)} {u w : Fin n → ℝ}
    (hu : IsAdmissible q dummy v E u)
    (hw : IsAdmissible q dummy v E w) :
    IsAdmissible q dummy v E (fun j => max (u j) (w j)) := by
  intro owner
  by_cases hle : u owner ≤ w owner
  · obtain ⟨h⟩ := hw owner
    exact ⟨h.weaken (fun j => le_max_right (u j) (w j))
      (max_eq_right hle).symm⟩
  · obtain ⟨h⟩ := hu owner
    have hwu : w owner ≤ u owner := le_of_lt (lt_of_not_ge hle)
    exact ⟨h.weaken (fun j => le_max_left (u j) (w j))
      (max_eq_left hwu).symm⟩

/-- A deterministic `(q-1)`-item bundle is admissible with its actual
valuation vector. This is the vertex case of the virtual-valuation map. -/
theorem isAdmissible_vertex {n m q : ℕ} {dummy : Fin m}
    (v : Fin n → Finset (Fin m) → ℝ)
    (E F : Finset (Fin m)) (hq : 1 ≤ q)
    (hF : F.card = q - 1) (hFE : F ⊆ E) :
    IsAdmissible q dummy v E (fun j => v j F) := by
  intro owner
  refine ⟨{
    B := F
    lowerSet := F
    upperSet := F
    in_stock := hFE
    size := Or.inl hF
    lower_subset := Finset.Subset.rfl
    upper_subset := Finset.Subset.rfl
    lower_size := hF
    upper_size := hF
    lower_bound := fun _ => le_refl _
    owner_bound := le_refl _
    short_sets := fun _ => ⟨rfl, rfl⟩
    shortening := ?_
  }⟩
  intro hFull _
  omega

/-- The exact finite-maximum closure used to fill higher-dimensional faces:
for each owner, a finite maximum is attained by one operand in that owner's
coordinate, and that operand's witnesses remain valid. -/
theorem isAdmissible_finset_max
    {n m q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Finset (Fin m)}
    {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (u : ι → Fin n → ℝ)
    (hu : ∀ a ∈ s, IsAdmissible q dummy v E (u a)) :
    IsAdmissible q dummy v E
      (fun j => s.sup' hs (fun a => u a j)) := by
  intro owner
  obtain ⟨a, ha, hmax⟩ :=
    s.exists_mem_eq_sup' hs (fun a => u a owner)
  obtain ⟨h⟩ := hu a ha owner
  refine ⟨h.weaken (fun j => ?_) hmax.symm⟩
  exact Finset.le_sup' (fun a => u a j) ha

/-- The ascent from the value vector of `F` toward the coordinatewise
maximum of the values of `F` and `T` is admissible when their union contains
the dummy. This is the manuscript's simpler dummy-containing exchange path;
the non-dummy path needs the separate shortening bend. -/
theorem isAdmissible_dummyUnion_ascent
    {n m q : ℕ} (dummy : Fin m)
    (v : Fin n → Finset (Fin m) → ℝ)
    (E F T : Finset (Fin m)) (u : Fin n → ℝ)
    (hq : 1 ≤ q)
    (hF : F.card = q - 1) (hT : T.card = q - 1)
    (hUnion : (F ∪ T).card = q)
    (hDummy : dummy ∈ F ∪ T)
    (hFE : F ⊆ E) (hTE : T ⊆ E)
    (hlow : ∀ j : Fin n, v j F ≤ u j)
    (hhigh : ∀ j : Fin n, u j ≤ max (v j F) (v j T)) :
    IsAdmissible q dummy v E u := by
  intro owner
  by_cases heq : u owner = v owner F
  · refine ⟨{
      B := F
      lowerSet := F
      upperSet := F
      in_stock := hFE
      size := Or.inl hF
      lower_subset := Finset.Subset.rfl
      upper_subset := Finset.Subset.rfl
      lower_size := hF
      upper_size := hF
      lower_bound := hlow
      owner_bound := heq.le
      short_sets := fun _ => ⟨rfl, rfl⟩
      shortening := ?_
    }⟩
    intro hFull _
    omega
  · have huT : u owner ≤ v owner T := by
      by_cases hab : v owner F ≤ v owner T
      · simpa [max_eq_right hab] using hhigh owner
      · have hba : v owner T ≤ v owner F :=
          le_of_lt (lt_of_not_ge hab)
        have hua : u owner ≤ v owner F := by
          simpa [max_eq_left hba] using hhigh owner
        exact False.elim (heq (le_antisymm hua (hlow owner)))
    refine ⟨{
      B := F ∪ T
      lowerSet := F
      upperSet := T
      in_stock := Finset.union_subset hFE hTE
      size := Or.inr hUnion
      lower_subset := Finset.subset_union_left
      upper_subset := Finset.subset_union_right
      lower_size := hF
      upper_size := hT
      lower_bound := hlow
      owner_bound := huT
      short_sets := ?_
      shortening := ?_
    }⟩
    · intro hShort
      omega
    · intro _ hd
      exact False.elim (hd hDummy)

/-- The first bend of the manuscript's dummy-free exchange path. If the
virtual vector lies between the value of `F` and the bend
`a ∨ (b ∧ c)`, the full union can be shortened back to `F` whenever the
owner needs `T` for the upper witness. -/
theorem isAdmissible_exchange_firstBend
    {n m q : ℕ} (dummy : Fin m)
    (v : Fin n → Finset (Fin m) → ℝ)
    (E F T : Finset (Fin m)) (u : Fin n → ℝ)
    (hq : 1 ≤ q)
    (hF : F.card = q - 1) (hT : T.card = q - 1)
    (hUnion : (F ∪ T).card = q)
    (hFE : F ⊆ E) (hTE : T ⊆ E)
    (hlow : ∀ j : Fin n, v j F ≤ u j)
    (hhigh : ∀ j : Fin n,
      u j ≤ max (v j F) (min (v j T) (v j (F ∩ T)))) :
    IsAdmissible q dummy v E u := by
  intro owner
  by_cases heq : u owner = v owner F
  · refine ⟨{
      B := F
      lowerSet := F
      upperSet := F
      in_stock := hFE
      size := Or.inl hF
      lower_subset := Finset.Subset.rfl
      upper_subset := Finset.Subset.rfl
      lower_size := hF
      upper_size := hF
      lower_bound := hlow
      owner_bound := heq.le
      short_sets := fun _ => ⟨rfl, rfl⟩
      shortening := ?_
    }⟩
    intro hFull _
    omega
  · have hmin : u owner ≤
        min (v owner T) (v owner (F ∩ T)) := by
      by_cases hab : v owner F ≤
          min (v owner T) (v owner (F ∩ T))
      · simpa [max_eq_right hab] using hhigh owner
      · have hba : min (v owner T) (v owner (F ∩ T)) ≤
            v owner F := le_of_lt (lt_of_not_ge hab)
        have hua : u owner ≤ v owner F := by
          simpa [max_eq_left hba] using hhigh owner
        exact False.elim (heq (le_antisymm hua (hlow owner)))
    have huT : u owner ≤ v owner T :=
      hmin.trans (min_le_left _ _)
    have huInter : u owner ≤ v owner (F ∩ T) :=
      hmin.trans (min_le_right _ _)
    have hDiffCard : (F \ T).card = 1 := by
      have hcard := Finset.card_sdiff_add_card F T
      omega
    have hReduce : F \ (F \ T) = F ∩ T := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    refine ⟨{
      B := F ∪ T
      lowerSet := F
      upperSet := T
      in_stock := Finset.union_subset hFE hTE
      size := Or.inr hUnion
      lower_subset := Finset.subset_union_left
      upper_subset := Finset.subset_union_right
      lower_size := hF
      upper_size := hT
      lower_bound := hlow
      owner_bound := huT
      short_sets := ?_
      shortening := ?_
    }⟩
    · intro hShort
      omega
    · intro _ _
      refine ⟨F, Finset.subset_union_left, hF, ?_, ?_⟩
      · intro j
        refine ⟨∅, ?_, ?_⟩
        · simp [CanDeleteOne]
        · simpa using hlow j
      · refine ⟨F \ T, ?_, ?_⟩
        · exact ⟨Finset.sdiff_subset, by omega⟩
        · simpa only [hReduce] using huInter

/-- The second bend of the manuscript's dummy-free exchange path. The
shortening certificate uses `T`: each observer takes whichever of `T` and
`F ∩ T` is below the virtual value, while the owner keeps `T` for the
upper comparison. -/
theorem isAdmissible_exchange_secondBend
    {n m q : ℕ} (dummy : Fin m)
    (v : Fin n → Finset (Fin m) → ℝ)
    (E F T : Finset (Fin m)) (u : Fin n → ℝ)
    (hq : 1 ≤ q)
    (hF : F.card = q - 1) (hT : T.card = q - 1)
    (hUnion : (F ∪ T).card = q)
    (hFE : F ⊆ E) (hTE : T ⊆ E)
    (hlow : ∀ j : Fin n,
      max (v j F) (min (v j T) (v j (F ∩ T))) ≤ u j)
    (hhigh : ∀ j : Fin n, u j ≤ max (v j F) (v j T)) :
    IsAdmissible q dummy v E u := by
  have hlowF (j : Fin n) : v j F ≤ u j :=
    (le_max_left _ _).trans (hlow j)
  intro owner
  by_cases heq : u owner = v owner F
  · refine ⟨{
      B := F
      lowerSet := F
      upperSet := F
      in_stock := hFE
      size := Or.inl hF
      lower_subset := Finset.Subset.rfl
      upper_subset := Finset.Subset.rfl
      lower_size := hF
      upper_size := hF
      lower_bound := hlowF
      owner_bound := heq.le
      short_sets := fun _ => ⟨rfl, rfl⟩
      shortening := ?_
    }⟩
    intro hFull _
    omega
  · have huT : u owner ≤ v owner T := by
      by_cases hab : v owner F ≤ v owner T
      · simpa [max_eq_right hab] using hhigh owner
      · have hba : v owner T ≤ v owner F :=
          le_of_lt (lt_of_not_ge hab)
        have hua : u owner ≤ v owner F := by
          simpa [max_eq_left hba] using hhigh owner
        exact False.elim (heq (le_antisymm hua (hlowF owner)))
    have hDiffCard : (T \ F).card = 1 := by
      have hcard := Finset.card_sdiff_add_card T F
      have hTF : (T ∪ F).card = q := by
        simpa [Finset.union_comm] using hUnion
      omega
    have hReduce : T \ (T \ F) = F ∩ T := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    refine ⟨{
      B := F ∪ T
      lowerSet := F
      upperSet := T
      in_stock := Finset.union_subset hFE hTE
      size := Or.inr hUnion
      lower_subset := Finset.subset_union_left
      upper_subset := Finset.subset_union_right
      lower_size := hF
      upper_size := hT
      lower_bound := hlowF
      owner_bound := huT
      short_sets := ?_
      shortening := ?_
    }⟩
    · intro hShort
      omega
    · intro _ _
      refine ⟨T, Finset.subset_union_right, hT, ?_, ?_⟩
      · intro j
        have hmin : min (v j T) (v j (F ∩ T)) ≤ u j :=
          (le_max_right _ _).trans (hlow j)
        by_cases hbc : v j T ≤ v j (F ∩ T)
        · have hb : v j T ≤ u j := by
            simpa [min_eq_left hbc] using hmin
          refine ⟨∅, ?_, ?_⟩
          · simp [CanDeleteOne]
          · simpa using hb
        · have hcb : v j (F ∩ T) ≤ v j T :=
            le_of_lt (lt_of_not_ge hbc)
          have hc : v j (F ∩ T) ≤ u j := by
            simpa [min_eq_right hcb] using hmin
          refine ⟨T \ F, ?_, ?_⟩
          · exact ⟨Finset.sdiff_subset, by omega⟩
          · simpa only [hReduce] using hc
      · refine ⟨∅, ?_, ?_⟩
        · simp [CanDeleteOne]
        · simpa using huT

end FairDivision.BF
