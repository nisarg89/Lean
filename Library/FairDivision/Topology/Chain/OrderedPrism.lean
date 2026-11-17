import RequestProject.Dvoretzky.Dold.Main

/-!
# The ordered-chain prism in the imported Dold chain model

Mathlib supplies categorical simplicial chain homotopies. The imported Dold
obstruction instead uses its concrete augmented `List E →₀ R` chain model.
This adapter writes the usual prism in THAT model, reusing the imported
boundary, cone identities, and linear-extension principle. It proves the
literal identity `∂P + P∂ = g_* - f_*`, including the empty augmentation list.

The relative AAK argument uses this operator after a sufficiently fine
subdivision of the source-time prism. No transversality or zero-count
invariance is asserted by this algebraic adapter.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Chain

open Dvoretzky.Dold

variable {R E F : Type*} [CommRing R]

/-- Recursive form of the usual alternating sum over the prism's staircase
simplexes. Each nonempty input list acquires one extra vertex. -/
def prismList (f g : E→F) : List E→Dvoretzky.Dold.Chain R F
  | [] => 0
  | x::l => consL (f x) (actL g (Finsupp.single (x::l) 1)-prismList f g l)

/-- Linear extension of the actual list prism. -/
def prism (f g : E→F) : Dvoretzky.Dold.Chain R E→ₗ[R]Dvoretzky.Dold.Chain R F :=
  Finsupp.linearCombination R (prismList f g)

@[simp] theorem prism_single (f g : E→F) (l : List E) (c : R) :
    prism f g (Finsupp.single l c)=c •prismList f g l := by
  simp [prism]

@[simp] theorem prism_nil (f g : E→F) :
    prism f g (Finsupp.single [] (1:R))=0 := by
  simp [prismList]

/-- Cone recursion survives linear extension without an indexing convention
for the individual staircase terms. -/
theorem prism_consL (f g : E→F) (x : E) (c : Dvoretzky.Dold.Chain R E) :
    prism f g (consL x c)=consL (f x) (actL g (consL x c)-prism f g c) := by
  have h : prism (R := R) f g ∘ₗ consL x=
      consL (f x) ∘ₗ (actL g ∘ₗ consL x-prism f g) := by
    apply chain_hom_ext
    intro l
    simp [prismList]
  exact LinearMap.congr_fun h c

/-- Boundary of one staircase prism, with all endpoint and side faces. -/
theorem bd_prismList (f g : E→F) (l : List E) :
    bd (prismList (R:=R) f g l)+prism f g (bdList l)=
      actL g (Finsupp.single l 1)-actL f (Finsupp.single l 1) := by
  induction l with
  | nil => simp [prismList]
  | cons x l ih =>
    have hInner : bd (prismList (R:=R) f g l)=
        (actL g (Finsupp.single l 1)-actL f (Finsupp.single l 1))-
          prism f g (bdList l) := eq_sub_of_add_eq ih
    simp only [prismList,bd_consL,map_sub,←actL_bd,bd_single,one_smul,
      bdList_cons,prism_consL,actL_consL]
    rw [hInner]
    simp only [map_sub, prism_single, one_smul, actL_single, consL_single, List.map_cons]
    abel

/-- The augmented chain homotopy identity in the exact chain representation
used by the external equivariant obstruction. -/
theorem bd_prism (f g : E→F) (c : Dvoretzky.Dold.Chain R E) :
    bd (prism f g c)+prism f g (bd c)=actL g c-actL f c := by
  have h : bd ∘ₗ prism (R := R) f g+prism f g ∘ₗ bd=actL g-actL f := by
    apply chain_hom_ext
    intro l
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.sub_apply,
      prism_single,one_smul,bd_single] using bd_prismList (R:=R) f g l
  exact LinearMap.congr_fun h c

/-- Each output list uses only images of input vertices. This is the support
fact needed to keep every staircase simplex inside its geometric prism. -/
theorem prismList_mem_supported (f g : E→F) (l : List E) :
    prismList (R:=R) f g l∈Finsupp.supported R R
      {w : List F | ∀v∈w,∃x∈l,v=f x ∨ v=g x} := by
  induction l with
  | nil => exact Submodule.zero_mem _
  | cons x l ih =>
    let S : Set (List F) := {w | ∀v∈w,∃y∈x::l,v=f y ∨v=g y}
    have hFull : consL (f x) (actL g (Finsupp.single (x::l) (1:R)))∈
        Finsupp.supported R R S := by
      rw [actL_single,consL_single]
      apply Finsupp.single_mem_supported
      intro v hv
      rcases List.mem_cons.mp hv with h|h
      · exact ⟨x,by simp,Or.inl h⟩
      · obtain ⟨y,hy,rfl⟩:=List.mem_map.mp h
        exact ⟨y,hy,Or.inr rfl⟩
    have hSide : consL (f x) (prismList (R:=R) f g l)∈
        Finsupp.supported R R S := by
      apply map_mem_supported (consL (f x)) (Finsupp.supported R R S) ?_ ih
      intro w hw
      rw [consL_single]
      apply Finsupp.single_mem_supported
      intro v hv
      rcases List.mem_cons.mp hv with h|h
      · exact ⟨x,by simp,Or.inl h⟩
      · obtain ⟨y,hy,hyv⟩:=hw v h
        exact ⟨y,by simp [hy],hyv⟩
    simpa only [prismList,map_sub] using Submodule.sub_mem _ hFull hSide

end FairDivision.Topology.Chain
