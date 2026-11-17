import FairDivision.Topology.AAK.SuspensionRawChains
import FairDivision.Topology.AAK.BipyramidBarycentricClassifier
import FairDivision.Topology.Chain.OrderedPrism

/-!
# Actual normalization of suspension vertex lists

Normalize the free vertices with the imported oriented wedge. A north or
south vertex forms the corresponding cone, with the pole placed first.
Moving a free vertex past that pole contributes the required minus sign.
Thus a compatible list gives an actual raw suspension chain; its projection
is the relative target chain used by Dold's argument.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.SuspensionRelativeChains

open Dvoretzky.Dold
open ZeroFreeBipyramid
open scoped Classical

variable {R : Type*} [CommRing R] {D p : ℕ}

abbrev SVertex (D p : ℕ) := SuspensionVertex D (ZMod p)

/-- Add a north cone vertex to a base chain. -/
def northInsertion : Base R D p→ₗ[R]Raw R D p :=
  (0 : Base R D p→ₗ[R]Base R D p).prod (LinearMap.id.prod 0)

/-- Add a south cone vertex to a base chain. -/
def southInsertion : Base R D p→ₗ[R]Raw R D p :=
  (0 : Base R D p→ₗ[R]Base R D p).prod ((0 : Base R D p→ₗ[R]Base R D p).prod LinearMap.id)

/-- Oriented wedge on suspension vertices. A pole wedges only the base
component; free vertices cross a leading pole with sign minus. -/
def rawWedge : SVertex D p→Module.End R (Raw R D p)
  | Sum.inl true=>northInsertion ∘ₗ LinearMap.fst R (Base R D p) (Base R D p×Base R D p)
  | Sum.inl false=>southInsertion ∘ₗ LinearMap.fst R (Base R D p) (Base R D p×Base R D p)
  | Sum.inr (i,a)=>
      let W : Module.End R (Base R D p) := wedge (R := R) (i,Multiplicative.ofAdd a)
      W.prodMap ((-W).prodMap (-W))

@[simp] theorem rawWedge_north (z : Raw R D p) :
    rawWedge (Sum.inl true) z=(0,z.1,0) := rfl

@[simp] theorem rawWedge_south (z : Raw R D p) :
    rawWedge (Sum.inl false) z=(0,0,z.1) := rfl

@[simp] theorem rawWedge_free (i : Fin D) (a : ZMod p) (z : Raw R D p) :
    rawWedge (Sum.inr (i,a)) z=(wedge (i,Multiplicative.ofAdd a) z.1,
      -wedge (i,Multiplicative.ofAdd a) z.2.1,-wedge (i,Multiplicative.ofAdd a) z.2.2) := rfl

/-- Normalized raw chain of an actual suspension vertex list. -/
def rawAlphaList : List (SVertex D p)→Raw R D p
  | []=>rawEmpty
  | v::l=>rawWedge v (rawAlphaList l)

/-- The two augmented pole singletons have their literal raw cone forms. -/
@[simp] theorem rawAlphaList_north_singleton :
    rawAlphaList (R:=R) (D:=D) (p:=p) [pole true]=rawNorth := rfl

@[simp] theorem rawAlphaList_south_singleton :
    rawAlphaList (R:=R) (D:=D) (p:=p) [pole false]=rawSouth := rfl

/-- Once either pole has been inserted, the base component is zero. A second
pole therefore gives the zero raw chain, even before the relative quotient.
This also covers repeated poles without any nondegeneracy assumption. -/
@[simp] theorem rawAlphaList_two_poles (a b : Bool) (l : List (SVertex D p)) :
    rawAlphaList (R:=R) (pole a::pole b::l)=0 := by
  cases a <;> cases b <;> rfl

/-- Linear extension to the imported augmented ordered-chain model. -/
def rawAlpha : Dvoretzky.Dold.Chain R (SVertex D p)→ₗ[R]Raw R D p :=
  Finsupp.linearCombination R rawAlphaList

/-- The actual relative normalization, after ordinary list normalization. -/
def alpha : Dvoretzky.Dold.Chain R (SVertex D p)→ₗ[R]Relative R D p :=
  toRelative ∘ₗ rawAlpha

@[simp] theorem rawAlpha_single (l : List (SVertex D p)) (c : R) :
    rawAlpha (Finsupp.single l c)=c•rawAlphaList l := by simp [rawAlpha]

@[simp] theorem alpha_single (l : List (SVertex D p)) (c : R) :
    alpha (Finsupp.single l c)=c•toRelative (rawAlphaList l) := by
  simp [alpha]

/-- The quotient removes the augmentation and the north singleton but
retains precisely the south singleton. These are the actual endpoint chains
used by the finite prism, with their coefficients fixed to one. -/
@[simp] theorem alpha_empty :
    alpha (Finsupp.single ([] : List (SVertex D p)) (1:R))=0 := by
  rw [alpha_single,one_smul,rawAlphaList,toRelative_empty]

@[simp] theorem alpha_north_singleton :
    alpha (Finsupp.single [(pole true : SVertex D p)] (1:R))=0 := by
  rw [alpha_single,one_smul,rawAlphaList_north_singleton,toRelative_north]

@[simp] theorem alpha_south_singleton :
    alpha (Finsupp.single [(pole false : SVertex D p)] (1:R))=southPole := by
  rw [alpha_single,one_smul,rawAlphaList_south_singleton,toRelative_south]

theorem rawAlpha_consL (v : SVertex D p) (c : Dvoretzky.Dold.Chain R (SVertex D p)) :
    rawAlpha (consL v c)=rawWedge v (rawAlpha c) := by
  have h : rawAlpha (R := R) ∘ₗ consL v=rawWedge v ∘ₗ rawAlpha := by
    apply chain_hom_ext
    intro l
    simp [rawAlphaList]
  exact LinearMap.congr_fun h c

/-- The free labels carried by a list. Pole vertices contribute no labels. -/
def carried (l : List (SVertex D p)) : Submodule R (Base R D p) :=
  Finsupp.supported R R {s | ∀i a,s i=some a→Sum.inr (i,a.toAdd)∈l}

theorem carried_mono {l k : List (SVertex D p)} (h : ∀v∈l,v∈k) :
    carried (R:=R) l≤carried k :=
  Finsupp.supported_mono (fun _ hs i a ha=>h _ (hs i a ha))

theorem carried_empty (l : List (SVertex D p)) : (empty : Base R D p)∈carried l := by
  apply Finsupp.single_mem_supported
  intro i a ha
  simp [emptyS] at ha

/-- An actual oriented wedge adds only its displayed free vertex to the
carrier. This is imported support-of-wedge plus a coordinate-update check. -/
theorem carried_wedge (i : Fin D) (a : ZMod p) (l : List (SVertex D p))
    {c : Base R D p} (hc : c∈carried l) :
    wedge (i,Multiplicative.ofAdd a) c∈carried (Sum.inr (i,a)::l) := by
  unfold carried at hc ⊢
  rw [Finsupp.mem_supported]
  intro s hs
  obtain ⟨t,ht,_hti,rfl⟩:=mem_support_wedge hs
  intro j b hb
  by_cases hji : j=i
  · subst j
    have hb' : Multiplicative.ofAdd a=b := Option.some.inj (by simpa using hb)
    subst b
    simp
  · rw [Function.update_of_ne hji] at hb
    exact List.mem_cons_of_mem _ ((Finsupp.mem_supported R c).mp hc ht j b hb)

/-- All three components have free labels from the SAME input list. -/
theorem rawAlphaList_carried (l : List (SVertex D p)) :
    (rawAlphaList (R:=R) l).1∈carried l ∧
    (rawAlphaList (R:=R) l).2.1∈carried l ∧
    (rawAlphaList (R:=R) l).2.2∈carried l := by
  induction l with
  | nil => exact ⟨carried_empty [],Submodule.zero_mem _,Submodule.zero_mem _⟩
  | cons v l ih =>
    have hmono : carried (R:=R) l≤carried (v::l) :=
      carried_mono (fun _ h=>List.mem_cons_of_mem _ h)
    cases v with
    | inl b =>
      cases b
      · exact ⟨Submodule.zero_mem _,Submodule.zero_mem _,hmono ih.1⟩
      · exact ⟨Submodule.zero_mem _,hmono ih.1,Submodule.zero_mem _⟩
    | inr v =>
      exact ⟨carried_wedge v.1 v.2 l ih.1,
        Submodule.neg_mem _ (carried_wedge v.1 v.2 l ih.2.1),
        Submodule.neg_mem _ (carried_wedge v.1 v.2 l ih.2.2)⟩

/-- No north vertex means no north-cone term, including after cancellations. -/
theorem rawAlphaList_north_zero {l : List (SVertex D p)} (h : Sum.inl true∉l) :
    (rawAlphaList (R:=R) l).2.1=0 := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    have hTail : Sum.inl true∉l := fun hm=>h (List.mem_cons_of_mem _ hm)
    cases v with
    | inl b =>
      cases b
      · rfl
      · exact (h (by simp)).elim
    | inr v =>
      change -wedge (v.1,Multiplicative.ofAdd v.2) (rawAlphaList (R:=R) l).2.1=0
      rw [ih hTail,map_zero,neg_zero]

theorem rawAlphaList_south_zero {l : List (SVertex D p)} (h : Sum.inl false∉l) :
    (rawAlphaList (R:=R) l).2.2=0 := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    have hTail : Sum.inl false∉l := fun hm=>h (List.mem_cons_of_mem _ hm)
    cases v with
    | inl b =>
      cases b
      · exact (h (by simp)).elim
      · rfl
    | inr v =>
      change -wedge (v.1,Multiplicative.ofAdd v.2) (rawAlphaList (R:=R) l).2.2=0
      rw [ih hTail,map_zero,neg_zero]

/-- Face consistency for a list, allowing repeated vertices until the
orientation normalization removes degeneracies. -/
def Compatible (l : List (SVertex D p)) : Prop :=
  ¬(Sum.inl true∈l ∧Sum.inl false∈l) ∧
  ∀i : Fin D,∀a b : ZMod p,Sum.inr (i,a)∈l→Sum.inr (i,b)∈l→a=b

theorem Compatible.of_subset {l k : List (SVertex D p)} (h : Compatible l)
    (hk : ∀v∈k,v∈l) : Compatible k :=
  ⟨fun hp=>h.1 ⟨hk _ hp.1,hk _ hp.2⟩,
    fun i a b ha hb=>h.2 i a b (hk _ ha) (hk _ hb)⟩

/-- A list carried by an actual suspension face has precisely the required
color/pole consistency. -/
theorem compatible_of_face {l : List (SVertex D p)} {F : Finset (SVertex D p)}
    (hF : F∈suspensionJoinComplex D (ZMod p)) (hl : ∀v∈l,v∈F) : Compatible l :=
  ⟨fun h=>hF.2.1 ⟨hl _ h.1,hl _ h.2⟩,
    fun i a b ha hb=>hF.2.2 i a b (hl _ ha) (hl _ hb)⟩

/-- Any free color already present in a carried chain agrees with the new
vertex, so the imported oriented cone identity applies. -/
theorem wedge_compatible_with_carried (i : Fin D) (a : ZMod p)
    {l : List (SVertex D p)} (h : Compatible (Sum.inr (i,a)::l))
    {c : Base R D p} (hc : c∈carried l) :
    ∀s∈c.support,s i=none ∨s i=some (Multiplicative.ofAdd a) := by
  unfold carried at hc
  intro s hs
  by_cases hn : s i=none
  · exact Or.inl hn
  · obtain ⟨b,hb⟩:=Option.ne_none_iff_exists'.mp hn
    have hMem := (Finsupp.mem_supported R c).mp hc hs i b hb
    have heq : a=b.toAdd := h.2 i a b.toAdd (by simp) (List.mem_cons_of_mem _ hMem)
    right
    rw [hb]
    exact congrArg some (by simpa using (congrArg Multiplicative.ofAdd heq).symm)

end FairDivision.Topology.AAK.SuspensionRelativeChains
