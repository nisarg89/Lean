import FairDivision.Finite.SupportedPermutations

/-!
# Balance after deleting dummy columns

A supported permutation assigns every regular slot to a real item. Real
items can occupy at most one designated slot per agent, so the projected
allocation has the required cardinality bounds.
-/

set_option autoImplicit false

namespace FairDivision

/-- Choose the real item occupying a regular slot. -/
noncomputable def regularSlotItem {n m : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (AssignmentSlot n m))
    (hσ : PermRespectsDummy hn σ)
    (i : Fin n) (k : Fin (m / n)) : Fin m :=
  (regularSlot_has_real_item hn σ hσ i k).choose

theorem regularSlotItem_spec {n m : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (AssignmentSlot n m))
    (hσ : PermRespectsDummy hn σ)
    (i : Fin n) (k : Fin (m / n)) :
    σ (i, .inl k) =
      assignmentColumnEquiv n m hn (.inl (regularSlotItem hn σ hσ i k)) :=
  (regularSlot_has_real_item hn σ hσ i k).choose_spec

theorem regularSlotItem_mem_bundle {n m : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (AssignmentSlot n m))
    (hσ : PermRespectsDummy hn σ)
    (i : Fin n) (k : Fin (m / n)) :
    regularSlotItem hn σ hσ i k ∈
      bundle (slotPermAllocation hn σ) i := by
  simp only [bundle, Finset.mem_filter, Finset.mem_univ, true_and]
  exact slotPermAllocation_of_regular hn σ i k _
    (regularSlotItem_spec hn σ hσ i k)

theorem regularSlotItem_injective {n m : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (AssignmentSlot n m))
    (hσ : PermRespectsDummy hn σ)
    (i : Fin n) :
    Function.Injective (regularSlotItem hn σ hσ i) := by
  intro k l hkl
  have hs : ((i, Sum.inl k) : AssignmentSlot n m) =
      ((i, Sum.inl l) : AssignmentSlot n m) := by
    apply σ.injective
    rw [regularSlotItem_spec hn σ hσ i k,
      regularSlotItem_spec hn σ hσ i l, hkl]
  exact Sum.inl.inj (congrArg Prod.snd hs)

/-- Every projected agent receives at least `m / n` real items. -/
theorem slotPermAllocation_lower {n m : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (AssignmentSlot n m))
    (hσ : PermRespectsDummy hn σ)
    (i : Fin n) :
    m / n ≤ (bundle (slotPermAllocation hn σ) i).card := by
  have hle : Fintype.card (Fin (m / n)) ≤
      Fintype.card {g : Fin m // g ∈ bundle (slotPermAllocation hn σ) i} :=
    Fintype.card_le_of_injective
      (fun k => ⟨regularSlotItem hn σ hσ i k,
        regularSlotItem_mem_bundle hn σ hσ i k⟩)
      (by
        intro k l hkl
        exact regularSlotItem_injective hn σ hσ i
          (congrArg Subtype.val hkl))
  simpa using hle

/-- Every projected agent receives at most `m / n + 1` real items. -/
theorem slotPermAllocation_upper {n m : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (AssignmentSlot n m)) (i : Fin n) :
    (bundle (slotPermAllocation hn σ) i).card ≤ m / n + 1 := by
  have hle :
      Fintype.card {g : Fin m // g ∈ bundle (slotPermAllocation hn σ) i} ≤
        Fintype.card (Fin (m / n) ⊕ Unit) :=
    Fintype.card_le_of_injective
      (fun g =>
        (σ.symm (assignmentColumnEquiv n m hn (.inl g.val))).2)
      (by
        intro g h hgh
        have hg :
            (σ.symm (assignmentColumnEquiv n m hn (.inl g.val))).1 = i := by
          have hmem := g.property
          change g.val ∈ Finset.univ.filter
            (fun a => (σ.symm (assignmentColumnEquiv n m hn (.inl a))).1 = i) at hmem
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem
        have hh :
            (σ.symm (assignmentColumnEquiv n m hn (.inl h.val))).1 = i := by
          have hmem := h.property
          change h.val ∈ Finset.univ.filter
            (fun a => (σ.symm (assignmentColumnEquiv n m hn (.inl a))).1 = i) at hmem
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem
        have hp :
            σ.symm (assignmentColumnEquiv n m hn (.inl g.val)) =
              σ.symm (assignmentColumnEquiv n m hn (.inl h.val)) :=
          Prod.ext (hg.trans hh.symm) hgh
        have he : assignmentColumnEquiv n m hn (.inl g.val) =
            assignmentColumnEquiv n m hn (.inl h.val) := by
          simpa using congrArg σ hp
        exact Subtype.ext (Sum.inl.inj
          ((assignmentColumnEquiv n m hn).injective he)))
  simpa using hle

end FairDivision
