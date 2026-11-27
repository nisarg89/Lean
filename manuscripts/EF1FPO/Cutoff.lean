import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

/-! Replace exhaustive subset optimization by the distinct supplied cutoffs. -/

set_option autoImplicit false

namespace EF1FPO

variable {G V : Type} [DecidableEq G] [LinearOrder V]

def cutoff (goods : Finset G) (level : G → V) (g : G) : Finset G :=
  goods.filter (fun h => level h ≤ level g)

noncomputable def subsetScore (level : G → V) (cost : Finset G → V) (bundle : Finset G) : V :=
  max (cost bundle) (if h : bundle.Nonempty then bundle.sup' h level else cost bundle)

theorem cutoff_minimum (goods : Finset G) (hgoods : goods.Nonempty) (level : G → V)
    (cost : Finset G → V) (antitone : ∀ A B : Finset G, A.Nonempty → A ⊆ B → B ⊆ goods → cost B ≤ cost A)
    (hbundles : (goods.powerset.erase ∅).Nonempty) :
    (goods.powerset.erase ∅).inf' hbundles (subsetScore level cost) =
      goods.inf' hgoods (fun g => max (cost (cutoff goods level g)) (level g)) := by
  refine le_antisymm (Finset.le_inf' hgoods _ ?_) (Finset.le_inf' hbundles _ ?_)
  · intro g hg
    let selected := cutoff goods level g
    have hChosen : g ∈ selected := by simp [selected, cutoff, hg]
    have hNonempty : selected.Nonempty := ⟨g, hChosen⟩
    have hSubset : selected ⊆ goods := fun x hx => (Finset.mem_filter.mp hx).1
    have hAdmitted : selected ∈ goods.powerset.erase ∅ :=
      Finset.mem_erase.mpr ⟨hNonempty.ne_empty, Finset.mem_powerset.mpr hSubset⟩
    have hMaximum : selected.sup' hNonempty level = level g := by
      refine le_antisymm (Finset.sup'_le hNonempty _ ?_) (Finset.le_sup' level hChosen)
      exact fun x hx => (Finset.mem_filter.mp hx).2
    have hBound := Finset.inf'_le (subsetScore level cost) hAdmitted
    simpa only [subsetScore, dif_pos hNonempty, hMaximum] using hBound
  · intro chosen hChosen
    have hNonempty : chosen.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hChosen).1
    have hSubset : chosen ⊆ goods := Finset.mem_powerset.mp (Finset.mem_erase.mp hChosen).2
    obtain ⟨g, hg, hMaximum⟩ := Finset.exists_mem_eq_sup' hNonempty level
    let selected := cutoff goods level g
    have hInclude : chosen ⊆ selected := by
      intro x hx
      refine Finset.mem_filter.mpr ⟨hSubset hx, ?_⟩
      rw [← hMaximum]
      exact Finset.le_sup' level hx
    have hSelected : selected ⊆ goods := fun x hx => (Finset.mem_filter.mp hx).1
    have hCost := antitone chosen selected hNonempty hInclude hSelected
    refine (Finset.inf'_le (fun g => max (cost (cutoff goods level g)) (level g))
      (hSubset hg)).trans ?_
    rw [subsetScore, dif_pos hNonempty, hMaximum]
    exact max_le_max hCost le_rfl

end EF1FPO
