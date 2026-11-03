import FairDivision.Topology.Chain.OrderedPrism

/-!
# Naturality and degree of the actual ordered prism

These are compatibility proofs for the imported augmented list-chain model.
They reuse the same recursive prism and its existing support proof. In
particular, an equivariant pair of vertex maps yields an equivariant prism
on chains supported by the invariant geometric source, and every nonzero
prism list has exactly one more vertex than its input list.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Chain

open Dvoretzky.Dold

variable {R E F A B : Type*} [CommRing R]

theorem prismList_congr_on_list (f g f' g' : E→F) (l : List E)
    (hf : ∀x∈l,f x=f' x) (hg : ∀x∈l,g x=g' x) :
    prismList (R:=R) f g l=prismList f' g' l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hfx:=hf x (by simp)
    have hgx:=hg x (by simp)
    have htail:=ih (fun y hy=>hf y (by simp [hy])) (fun y hy=>hg y (by simp [hy]))
    have hmap : (x::l).map g=(x::l).map g' :=
      List.map_congr_left (fun y hy=>hg y hy)
    simp only [prismList,actL_single]
    rw [hfx,hmap,htail]

theorem prismList_map_domain (a : A→E) (f g : E→F) (l : List A) :
    prismList (R:=R) f g (l.map a)=prismList (f∘a) (g∘a) l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons,prismList,actL_single,List.map_map,ih,Function.comp_apply]

theorem actL_prismList (b : F→B) (f g : E→F) (l : List E) :
    actL b (prismList (R:=R) f g l)=prismList (b∘f) (b∘g) l := by
  induction l with
  | nil => simp [prismList]
  | cons x l ih =>
    simp only [prismList,actL_consL,map_sub,actL_single,List.map_map,ih,Function.comp_apply]

theorem prismList_naturality (a : E→E) (b : F→F) (f g : E→F) (l : List E)
    (hf : ∀x∈l,f (a x)=b (f x)) (hg : ∀x∈l,g (a x)=b (g x)) :
    prismList (R:=R) f g (l.map a)=actL b (prismList f g l) := by
  rw [prismList_map_domain,actL_prismList]
  exact prismList_congr_on_list _ _ _ _ l hf hg

/-- Naturality needs equivariance only on the actual source set supporting
this chain; malformed or unused ambient points are irrelevant. -/
theorem prism_naturality_on_supported (a : E→E) (b : F→F) (f g : E→F)
    {S : Set E} (hf : ∀x∈S,f (a x)=b (f x)) (hg : ∀x∈S,g (a x)=b (g x))
    {c : Dvoretzky.Dold.Chain R E}
    (hc : c∈Finsupp.supported R R {l : List E|∀x∈l,x∈S}) :
    prism f g (actL a c)=actL b (prism f g c) := by
  apply eq_on_supported (prism f g ∘ₗ actL a) (actL b ∘ₗ prism f g) ?_ hc
  intro l hl
  simp only [LinearMap.comp_apply,actL_single,prism_single,one_smul]
  exact prismList_naturality a b f g l (fun x hx=>hf x (hl x hx))
    (fun x hx=>hg x (hl x hx))

/-- The ordinary prism raises the exact list degree by one, including
repeated vertices. The augmentation input has zero prism. -/
theorem prismList_supported_length (f g : E→F) (l : List E) :
    prismList (R:=R) f g l∈Finsupp.supported R R
      {w : List F|w.length=l.length+1} := by
  induction l with
  | nil => exact Submodule.zero_mem _
  | cons x l ih =>
    let S : Set (List F):={w|w.length=(x::l).length+1}
    have hFull : consL (f x) (actL g (Finsupp.single (x::l) (1:R)))∈
        Finsupp.supported R R S := by
      rw [actL_single,consL_single]
      apply Finsupp.single_mem_supported
      simp [S]
    have hSide : consL (f x) (prismList (R:=R) f g l)∈Finsupp.supported R R S := by
      apply map_mem_supported (consL (f x)) (Finsupp.supported R R S) ?_ ih
      intro w hw
      rw [consL_single]
      apply Finsupp.single_mem_supported
      simpa [S,List.length_cons] using congrArg Nat.succ hw
    simpa only [prismList,map_sub] using Submodule.sub_mem _ hFull hSide

theorem prism_supported_length (f g : E→F) (q : ℕ)
    {c : Dvoretzky.Dold.Chain R E}
    (hc : c∈Finsupp.supported R R {l : List E|l.length=q}) :
    prism f g c∈Finsupp.supported R R {w : List F|w.length=q+1} := by
  apply map_mem_supported (prism f g) _ ?_ hc
  intro l hl
  change l.length = q at hl
  rw [prism_single,one_smul]
  simpa only [hl] using prismList_supported_length (R:=R) f g l

/-- If all endpoint images of one source list lie in a target face, then
every staircase simplex of that prism lies in the same face. -/
theorem prismList_supported_face (f g : E→F) (l : List E) (S : Finset F)
    (hf : ∀x∈l,f x∈S) (hg : ∀x∈l,g x∈S) :
    prismList (R:=R) f g l∈Finsupp.supported R R {w : List F|∀v∈w,v∈S} := by
  apply Finsupp.supported_mono ?_ (prismList_mem_supported f g l)
  intro w hw v hv
  obtain ⟨x,hx,hv⟩:=hw v hv
  rcases hv with hv|hv
  · rw [hv]
    exact hf x hx
  · rw [hv]
    exact hg x hx

end FairDivision.Topology.Chain
