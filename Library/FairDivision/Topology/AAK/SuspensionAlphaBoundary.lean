import FairDivision.Topology.AAK.SuspensionAlphaList

/-!
# Boundary and exact dimension of the suspension normalization

The free-vertex cone identity is reused from the imported Dold chains.
For pole vertices, face compatibility excludes the opposite cone. These
identities prove the actual suspension normalization is a chain map on
lists carried by a target face. An occupied-color count then proves its
exact dimension cutoff, without assuming the input list is nondegenerate.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.SuspensionRelativeChains

open Dvoretzky.Dold
open scoped Classical

variable {R : Type*} [CommRing R] {D p : ℕ}

-- Preserve the fixed monoid/module when a supported-chain helper asks for
-- a group on the relative kernel product. This is the same group as the
-- cyclic exactness theorem, not a second construction.
local instance : AddCommGroup (NonemptyBase R D p) :=
  nonemptyCanonicalAddCommGroup (R:=R) (D:=D) (p:=p)

/-- Cone identity at one actual compatible normalized list. -/
theorem rawBoundary_wedge_alpha (v : SVertex D p) (l : List (SVertex D p))
    (h : Compatible (v::l)) :
    rawBoundary (rawWedge v (rawAlphaList (R:=R) l))=
      rawAlphaList l-rawWedge v (rawBoundary (rawAlphaList l)) := by
  cases v with
  | inl b =>
    cases b
    · have hNoNorth : Sum.inl true∉l := by
        intro hNorth
        exact h.1 ⟨List.mem_cons_of_mem _ hNorth,by simp⟩
      have hNorth := rawAlphaList_north_zero (R:=R) hNoNorth
      apply Prod.ext
      · simp [rawBoundary_apply,rawWedge_south]
      · apply Prod.ext
        · simp [rawBoundary_apply,rawWedge_south,hNorth]
        · change -bdT (rawAlphaList (R:=R) l).1=
            (rawAlphaList l).2.2-
              (bdT (rawAlphaList l).1+(rawAlphaList l).2.1+(rawAlphaList l).2.2)
          rw [hNorth]
          abel
    · have hNoSouth : Sum.inl false∉l := by
        intro hSouth
        exact h.1 ⟨by simp,List.mem_cons_of_mem _ hSouth⟩
      have hSouth := rawAlphaList_south_zero (R:=R) hNoSouth
      apply Prod.ext
      · simp [rawBoundary_apply,rawWedge_north]
      · apply Prod.ext
        · change -bdT (rawAlphaList (R:=R) l).1=
            (rawAlphaList l).2.1-
              (bdT (rawAlphaList l).1+(rawAlphaList l).2.1+(rawAlphaList l).2.2)
          rw [hSouth]
          abel
        · simp [rawBoundary_apply,rawWedge_north,hSouth]
  | inr v =>
    rcases v with ⟨i,a⟩
    have hCarry := rawAlphaList_carried (R:=R) l
    have hC := bdT_wedge (R:=R) (D:=D) (G:=Multiplicative (ZMod p)) (i,Multiplicative.ofAdd a) (rawAlphaList (R:=R) l).1
      (wedge_compatible_with_carried (R:=R) (D:=D) (p:=p)
        (c:=(rawAlphaList (R:=R) l).1) i a h hCarry.1)
    have hA := bdT_wedge (R:=R) (D:=D) (G:=Multiplicative (ZMod p)) (i,Multiplicative.ofAdd a) (rawAlphaList (R:=R) l).2.1
      (wedge_compatible_with_carried (R:=R) (D:=D) (p:=p)
        (c:=(rawAlphaList (R:=R) l).2.1) i a h hCarry.2.1)
    have hB := bdT_wedge (R:=R) (D:=D) (G:=Multiplicative (ZMod p)) (i,Multiplicative.ofAdd a) (rawAlphaList (R:=R) l).2.2
      (wedge_compatible_with_carried (R:=R) (D:=D) (p:=p)
        (c:=(rawAlphaList (R:=R) l).2.2) i a h hCarry.2.2)
    simp only [rawWedge_free,rawBoundary_apply,Prod.fst_sub,Prod.snd_sub]
    apply Prod.ext
    · change bdT (wedge (i,Multiplicative.ofAdd a) (rawAlphaList (R:=R) l).1)+
          -wedge (i,Multiplicative.ofAdd a) (rawAlphaList l).2.1+
          -wedge (i,Multiplicative.ofAdd a) (rawAlphaList l).2.2=
        (rawAlphaList l).1-wedge (i,Multiplicative.ofAdd a)
          (bdT (rawAlphaList l).1+(rawAlphaList l).2.1+(rawAlphaList l).2.2)
      rw [hC,map_add,map_add]
      abel
    · apply Prod.ext
      · change -bdT (-wedge (i,Multiplicative.ofAdd a) (rawAlphaList (R:=R) l).2.1)=
          (rawAlphaList l).2.1- -wedge (i,Multiplicative.ofAdd a) (-bdT (rawAlphaList l).2.1)
        simp only [map_neg,neg_neg,hA]
      · change -bdT (-wedge (i,Multiplicative.ofAdd a) (rawAlphaList (R:=R) l).2.2)=
          (rawAlphaList l).2.2- -wedge (i,Multiplicative.ofAdd a) (-bdT (rawAlphaList l).2.2)
        simp only [map_neg,neg_neg,hB]

/-- Normalization commutes with the actual augmented boundary on every
compatible list. -/
theorem rawBoundary_rawAlphaList (l : List (SVertex D p)) (h : Compatible l) :
    rawBoundary (rawAlphaList (R:=R) l)=rawAlpha (bdList l) := by
  induction l with
  | nil => simp only [rawAlphaList,rawBoundary_empty,bdList_nil,map_zero]
  | cons v l ih =>
    have hTail : Compatible l := h.of_subset (fun _ hm=>List.mem_cons_of_mem _ hm)
    rw [rawAlphaList,rawBoundary_wedge_alpha v l h,ih hTail,bdList_cons,
      map_sub,rawAlpha_single,one_smul,rawAlpha_consL]

/-- Relative normalization is the SAME chain map followed by the proved
north-pole quotient. -/
theorem boundary_alpha_single (l : List (SVertex D p)) (h : Compatible l) :
    boundary (alpha (Finsupp.single l (1:R)))=alpha (bdList l) := by
  rw [alpha_single,one_smul,←toRelative_boundary,rawBoundary_rawAlphaList l h]
  rfl

theorem boundary_alpha_of_supported (c : Dvoretzky.Dold.Chain R (SVertex D p))
    (hc : c∈Finsupp.supported R R {l : List (SVertex D p) | Compatible l}) :
    boundary (alpha c)=alpha (bd c) := by
  exact eq_on_supported (M:=Relative R D p)
    ((boundary (R:=R) (D:=D) (p:=p)).comp (alpha (R:=R) (D:=D) (p:=p)))
    ((alpha (R:=R) (D:=D) (p:=p)).comp (bd (R:=R) (E:=SVertex D p)))
    (fun l hl=>by
      simpa only [LinearMap.comp_apply,bd_single,one_smul] using
        (boundary_alpha_single (R:=R) l hl)) hc

/-- Number of occupied free colors, before adding either suspension pole. -/
def occupied (s : Smp D (Multiplicative (ZMod p))) : ℕ :=
  (Finset.univ.filter (fun i=>(s i).isSome)).card

theorem occupied_le (s : Smp D (Multiplicative (ZMod p))) : occupied s≤D := by
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin D)

@[simp] theorem occupied_empty : occupied (emptyS : Smp D (Multiplicative (ZMod p)))=0 := by
  simp [occupied,emptyS]

/-- The imported wedge only inserts into a previously empty color. -/
theorem occupied_update (s : Smp D (Multiplicative (ZMod p))) (i : Fin D)
    (a : Multiplicative (ZMod p)) (hi : s i=none) :
    occupied (Function.update s i (some a))=occupied s+1 := by
  have hSet : Finset.univ.filter (fun j=>(Function.update s i (some a) j).isSome)=
      insert i (Finset.univ.filter (fun j=>(s j).isSome)) := by
    ext j
    by_cases hji : j=i
    · subst j
      simp
    · simp [hji,Function.update_of_ne hji]
  rw [occupied,hSet,Finset.card_insert_of_notMem (by simp [hi])]
  rfl

/-- Every output base simplex has the original list length, whereas each
cone base has one fewer vertex. Repeated vertices simply yield zero terms. -/
theorem rawAlphaList_degrees (l : List (SVertex D p)) :
    (∀s∈(rawAlphaList (R:=R) l).1.support,occupied s=l.length) ∧
    (∀s∈(rawAlphaList (R:=R) l).2.1.support,occupied s+1=l.length) ∧
    (∀s∈(rawAlphaList (R:=R) l).2.2.support,occupied s+1=l.length) := by
  induction l with
  | nil =>
    refine ⟨?_,by simp [rawAlphaList,rawEmpty],by simp [rawAlphaList,rawEmpty]⟩
    intro s hs
    have hs' : s=emptyS := Finset.mem_singleton.mp (Finsupp.support_single_subset hs)
    subst s
    exact occupied_empty
  | cons v l ih =>
    cases v with
    | inl b =>
      cases b
      · refine ⟨by simp [rawAlphaList,rawWedge_south],by simp [rawAlphaList,rawWedge_south],?_⟩
        intro s hs
        have h := ih.1 s hs
        simpa only [List.length_cons] using congrArg (fun n=>n+1) h
      · refine ⟨by simp [rawAlphaList,rawWedge_north],?_,by simp [rawAlphaList,rawWedge_north]⟩
        intro s hs
        have h := ih.1 s hs
        simpa only [List.length_cons] using congrArg (fun n=>n+1) h
    | inr v =>
      rcases v with ⟨i,a⟩
      refine ⟨?_,?_,?_⟩
      · intro s hs
        obtain ⟨t,ht,hti,rfl⟩:=mem_support_wedge hs
        rw [occupied_update _ _ _ hti,ih.1 t ht,List.length_cons]
      · intro s hs
        have hs' : s∈(wedge (i,Multiplicative.ofAdd a) (rawAlphaList (R:=R) l).2.1).support := by
          simpa only [rawAlphaList,rawWedge_free,Finsupp.support_neg] using hs
        obtain ⟨t,ht,hti,rfl⟩:=mem_support_wedge hs'
        rw [occupied_update _ _ _ hti]
        have h := ih.2.1 t ht
        simp only [List.length_cons]
        omega
      · intro s hs
        have hs' : s∈(wedge (i,Multiplicative.ofAdd a) (rawAlphaList (R:=R) l).2.2).support := by
          simpa only [rawAlphaList,rawWedge_free,Finsupp.support_neg] using hs
        obtain ⟨t,ht,hti,rfl⟩:=mem_support_wedge hs'
        rw [occupied_update _ _ _ hti]
        have h := ih.2.2 t ht
        simp only [List.length_cons]
        omega

/-- The suspension has dimension D, so lists with more than D+1 vertices
normalize to zero. This is proved for the actual raw normalization. -/
theorem rawAlphaList_eq_zero_of_length {l : List (SVertex D p)} (hLength : D+1<l.length) :
    rawAlphaList (R:=R) l=0 := by
  have hDegree := rawAlphaList_degrees (R:=R) l
  have zero_of_degree (c : Base R D p) (h : ∀s∈c.support,D<occupied s) : c=0 := by
    apply Finsupp.ext
    intro s
    by_contra hs
    have hMem : s∈c.support := Finsupp.mem_support_iff.mpr hs
    exact (not_lt_of_ge (occupied_le s)) (h s hMem)
  apply Prod.ext
  · apply zero_of_degree
    intro s hs
    rw [hDegree.1 s hs]
    omega
  · apply Prod.ext
    · apply zero_of_degree
      intro s hs
      have h := hDegree.2.1 s hs
      omega
    · apply zero_of_degree
      intro s hs
      have h := hDegree.2.2 s hs
      omega

theorem alpha_single_eq_zero_of_length {l : List (SVertex D p)} (hLength : D+1<l.length) :
    alpha (Finsupp.single l (1:R))=0 := by
  rw [alpha_single,one_smul,rawAlphaList_eq_zero_of_length hLength,map_zero]

theorem alpha_eq_zero_of_supported_length (c : Dvoretzky.Dold.Chain R (SVertex D p))
    (hc : c∈Finsupp.supported R R {l : List (SVertex D p) | D+1<l.length}) : alpha c=0 := by
  exact eq_on_supported (M:=Relative R D p) (alpha (R:=R) (D:=D) (p:=p))
    (0 : Dvoretzky.Dold.Chain R (SVertex D p) →ₗ[R] Relative R D p)
    (fun l hl=>by
      simpa only [LinearMap.zero_apply] using
        (alpha_single_eq_zero_of_length (R:=R) hl)) hc

end FairDivision.Topology.AAK.SuspensionRelativeChains
