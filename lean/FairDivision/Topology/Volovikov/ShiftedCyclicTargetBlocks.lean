import FairDivision.Topology.Volovikov.ShiftedCyclicSupportMatrices
import FairDivision.Topology.Volovikov.OddPrimeTwistedJoinChains

/-!
# The actual occupied-color decomposition of the oriented target

A join simplex has an occupied-color set S and one Z/p label at every
color in S. Twisted translations preserve S. This file supplies literal
restriction and assembly maps, identifies every nonempty block with the
label-function module from the generic matrix argument, and assembles
its two exactness witnesses. The only exceptional block is the empty
simplex, retained explicitly as the augmentation term.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Volovikov.ShiftedCyclicTargetBlocks

open scoped BigOperators
open Dvoretzky.Dold
open OddPrimeTwistedJoinChains
open CyclicLabelBlockExactness (Labels action)
open ShiftedCyclicSupportMatrices (GenericField weights)

variable {p r D : ℕ} [Fact p.Prime]

abbrev K (p r : ℕ) := GenericField p r
abbrev Target (p r D : ℕ) := TChain (K p r) D (Label p)

/-- The literal occupied-color set, including the empty set. -/
def occupied (s : Smp D (Label p)) : Finset (Fin D) := by
  classical
  exact Finset.univ.filter (fun j=>(s j).isSome)

/-- Build the actual simplex with support S and additive labels b. -/
def simplex (S : Finset (Fin D)) (b : Labels p S) : Smp D (Label p) := by
  classical
  exact fun j=>if hj:j∈S then some (Multiplicative.ofAdd (b ⟨j,hj⟩)) else none

/-- Read additive labels; getD is evaluated only at occupied colors. -/
def labels (s : Smp D (Label p)) : Labels p (occupied s) :=
  fun j=>Multiplicative.toAdd ((s j.1).getD 1)

@[simp] theorem occupied_simplex (S : Finset (Fin D)) (b : Labels p S) :
    occupied (simplex S b)=S := by
  classical
  ext j
  simp [occupied,simplex]

@[simp] theorem occupied_empty : occupied (emptyS : Smp D (Label p))=∅ := by
  classical
  ext j
  simp [occupied,emptyS]

@[simp] theorem simplex_empty (b : Labels p (∅ : Finset (Fin D))) :
    simplex ∅ b=(emptyS : Smp D (Label p)) := by
  classical
  funext j
  simp [simplex,emptyS]

@[simp] theorem simplex_labels (s : Smp D (Label p)) :
    simplex (occupied s) (labels s)=s := by
  classical
  funext j
  cases h:s j with
  | none=>simp [simplex,occupied,h]
  | some l=>simp [simplex,occupied,labels,h]

/-- Equality transport of the support changes only a label function's
domain proof. The underlying occupied color is unchanged. -/
private theorem transport_labels_apply {S T : Finset (Fin D)} (h : S=T)
    (b : Labels p S) (j : T) :
    (h ▸b) j=b ⟨j.val,h.symm ▸j.property⟩ := by
  cases h
  rfl

/-- Dependent label equality, stated with its actual support transport. -/
theorem labels_simplex (S : Finset (Fin D)) (b : Labels p S) :
    (occupied_simplex S b) ▸ labels (simplex S b)=b := by
  classical
  funext j
  rw [transport_labels_apply]
  simpa only [labels,simplex,dif_pos j.property,Option.getD_some,
    toAdd_ofAdd]

theorem empty_of_occupied_empty (s : Smp D (Label p)) (h : occupied s=∅) :
    s=emptyS := by
  classical
  funext j
  change s j=none
  have hj : j∉occupied s := by
    rw [h]
    exact Finset.notMem_empty j
  cases hs:s j with
  | none=>rfl
  | some l=>
      exfalso
      apply hj
      simp only [occupied,Finset.mem_filter,Finset.mem_univ,true_and,hs,
        Option.isSome_some]

/-- Literal block coefficients of an actual oriented chain. -/
def block (S : Finset (Fin D)) : Target p r D→ₗ[K p r](Labels p S→K p r) where
  toFun c:=fun b=>c (simplex S b)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

@[simp] theorem block_apply (S : Finset (Fin D)) (c : Target p r D) (b : Labels p S) :
    block S c b=c (simplex S b) := rfl

/-- Assemble one chosen coefficient function for every occupied-color set. -/
def assemble (F : (S : Finset (Fin D))→Labels p S→K p r) : Target p r D :=
  (Finsupp.linearEquivFunOnFinite (K p r) (K p r) (Smp D (Label p))).symm
    (fun s=>F (occupied s) (labels s))

@[simp] theorem assemble_apply
    (F : (S : Finset (Fin D))→Labels p S→K p r) (s : Smp D (Label p)) :
    assemble F s=F (occupied s) (labels s) := by
  exact congrFun
    ((Finsupp.linearEquivFunOnFinite (K p r) (K p r) (Smp D (Label p))).apply_symm_apply
      (fun t=>F (occupied t) (labels t))) s

/-- Evaluation across the literal occupied-support equality. This is
ordinary equality elimination, with the label domain transported explicitly;
no simplifier is asked to identify dependent finite-subtype domains. -/
private theorem supportValue_transport
    (F : (S : Finset (Fin D))→Labels p S→K p r)
    {S T : Finset (Fin D)} (h : S=T) (b : Labels p S) :
    F S b=F T (h ▸b) := by
  cases h
  rfl

@[simp] theorem block_assemble
    (F : (S : Finset (Fin D))→Labels p S→K p r) (S : Finset (Fin D)) :
    block S (assemble F)=F S := by
  classical
  funext b
  simp only [block_apply,assemble_apply]
  have hS:=occupied_simplex S b
  have hLabels:=labels_simplex S b
  exact (supportValue_transport F hS (labels (simplex S b))).trans
    (congrArg (F S) hLabels)

/-- The support's genuine generator shifts, with the original color
indices retained by the subtype. -/
def restricted (ε : Fin r→Fin D→ZMod p) (S : Finset (Fin D)) : Fin r→Labels p S :=
  fun q j=>ε q j.1

theorem simplex_shift (S : Finset (Fin D)) (b : Labels p S)
    (ε : Fin D→ZMod p) :
    twistS (-ε) (simplex S b)=simplex S (b+fun j=>ε j.1) := by
  classical
  funext j
  by_cases hj:j∈S
  · simp [twistS,simplex,hj,←ofAdd_add]
  · simp [twistS,simplex,hj]

/-- Exact coefficient pullback; the PLUS sign is indispensable for odd p. -/
theorem block_twist (S : Finset (Fin D)) (ε : Fin D→ZMod p) (c : Target p r D) :
    block S (twistL ε c)=action (fun j : S=>ε j.1) (block S c) := by
  funext b
  rw [block_apply,twistL_apply,simplex_shift]
  rfl

/-- One common generic displacement acting on all actual target chains. -/
def displacement (ε : Fin r→Fin D→ZMod p) : Module.End (K p r) (Target p r D) :=
  ShiftedCyclicAlgebra.displacement (weights (p:=p) (r:=r)) (fun q=>twistL (ε q))

def blockDisplacement (ε : Fin r→Fin D→ZMod p) (S : Finset (Fin D)) :
    Module.End (K p r) (Labels p S→K p r) :=
  ShiftedCyclicAlgebra.displacement (weights (p:=p) (r:=r))
    (fun q=>action (restricted ε S q))

theorem block_displacement (ε : Fin r→Fin D→ZMod p)
    (S : Finset (Fin D)) (c : Target p r D) :
    block S (displacement ε c)=blockDisplacement ε S (block S c) := by
  classical
  simp only [displacement,blockDisplacement,ShiftedCyclicAlgebra.displacement,
    LinearMap.sum_apply,map_sum,LinearMap.smul_apply,map_smul,
    LinearMap.sub_apply,map_sub,Module.End.one_apply,block_twist]
  rfl

theorem block_power (ε : Fin r→Fin D→ZMod p)
    (S : Finset (Fin D)) (n : ℕ) (c : Target p r D) :
    block S (((displacement ε)^n) c)=((blockDisplacement ε S)^n) (block S c) := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [pow_succ',Module.End.mul_apply,block_displacement,ih,
      pow_succ',Module.End.mul_apply]

@[simp] theorem twistS_empty (ε : Fin D→ZMod p) :
    twistS ε (emptyS : Smp D (Label p))=emptyS := by
  funext j
  rfl

@[simp] theorem twist_empty_coefficient (ε : Fin D→ZMod p) (c : Target p r D) :
    twistL ε c emptyS=c emptyS := by
  rw [twistL_apply,twistS_empty]

/-- The empty block is augmentation, not a free cyclic label block. -/
theorem displacement_empty (ε : Fin r→Fin D→ZMod p) (c : Target p r D) :
    displacement ε c emptyS=0 := by
  classical
  simp [displacement,ShiftedCyclicAlgebra.displacement,LinearMap.sum_apply,
    LinearMap.smul_apply,LinearMap.sub_apply,Module.End.one_apply]

theorem displacement_power_empty (ε : Fin r→Fin D→ZMod p) (n : ℕ) (hn : 0<n)
    (c : Target p r D) : ((displacement ε)^n) c emptyS=0 := by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [pow_succ',Module.End.mul_apply,displacement_empty]

/-- Reassemble actual local preimages, separating ONLY the empty simplex.
The proof uses every actual simplex coefficient and covers every degree. -/
theorem preimage_of_blocks
    (A : Module.End (K p r) (Target p r D))
    (Ablock : (S : Finset (Fin D))→Module.End (K p r) (Labels p S→K p r))
    (hBlock : ∀S c,block S (A c)=Ablock S (block S c))
    (hEmpty : ∀c,A c emptyS=0) (z : Target p r D)
    (hPreimage : ∀S : Finset (Fin D),S.Nonempty→∃w,Ablock S w=block S z) :
    ∃e : Target p r D,z=A e+z emptyS•Finsupp.single emptyS 1 := by
  classical
  let localPreimage (S : Finset (Fin D)) : Labels p S→K p r:=
    if h:S.Nonempty then Classical.choose (hPreimage S h) else 0
  have hLocal (S : Finset (Fin D)) (hS : S.Nonempty) :
      Ablock S (localPreimage S)=block S z := by
    simp only [localPreimage,dif_pos hS]
    exact Classical.choose_spec (hPreimage S hS)
  let e:=assemble localPreimage
  refine ⟨e,?_⟩
  apply Finsupp.ext
  intro s
  by_cases hS:(occupied s).Nonempty
  · have h:=congrFun (hLocal (occupied s) hS) (labels s)
    have hA:=congrFun (hBlock (occupied s) e) (labels s)
    simp only [e,block_assemble] at hA
    have hs : s≠emptyS := by
      intro hs
      simpa only [hs,occupied_empty,Finset.not_nonempty_empty] using hS
    simp only [block_apply,simplex_labels] at h hA
    simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,
      Finsupp.single_apply,if_neg hs.symm,mul_zero,add_zero]
    exact h.symm.trans hA.symm
  · have hs:s=emptyS:=empty_of_occupied_empty s (Finset.not_nonempty_iff_eq_empty.mp hS)
    subst s
    simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,
      Finsupp.single_eq_same,mul_one,hEmpty,zero_add]

/-- Concrete generic exactness modulo the empty simplex, first direction.
No local preimage or rank assumptions remain in this theorem. -/
theorem displacement_kernel_preimage (ε : Fin r→Fin D→ZMod p)
    (hCharacters : ∀j : Fin D,∃q : Fin r,ε q j≠0)
    (z : Target p r D) (hz : displacement ε z=0) :
    ∃e : Target p r D,z=((displacement ε)^(p-1)) e+
      z emptyS•Finsupp.single emptyS 1 := by
  apply preimage_of_blocks ((displacement ε)^(p-1))
    (fun S=>(blockDisplacement ε S)^(p-1))
    (fun S c=>block_power ε S (p-1) c)
    (fun c=>displacement_power_empty ε (p-1)
      (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt) c) z
  intro S hS
  have hJ : Nonempty S:=Finset.nonempty_coe_sort.mpr hS
  have hExact:=(ShiftedCyclicSupportMatrices.displacement_exact (restricted ε S) hJ
    (fun j=>hCharacters j.1)).1
  change LinearMap.range ((blockDisplacement ε S)^(p-1))=
    LinearMap.ker (blockDisplacement ε S) at hExact
  have hZero : blockDisplacement ε S (block S z)=0 := by
    rw [←block_displacement,hz,map_zero]
  have hMember : block S z∈LinearMap.range ((blockDisplacement ε S)^(p-1)) := by
    rw [hExact]
    exact hZero
  exact hMember

/-- The reverse concrete exactness direction, using the SAME generic
operator and the SAME occupied-color decomposition. -/
theorem displacement_power_kernel_preimage (ε : Fin r→Fin D→ZMod p)
    (hCharacters : ∀j : Fin D,∃q : Fin r,ε q j≠0)
    (z : Target p r D) (hz : ((displacement ε)^(p-1)) z=0) :
    ∃e : Target p r D,z=displacement ε e+z emptyS•Finsupp.single emptyS 1 := by
  apply preimage_of_blocks (displacement ε) (blockDisplacement ε)
    (block_displacement ε) (displacement_empty ε) z
  intro S hS
  have hJ : Nonempty S:=Finset.nonempty_coe_sort.mpr hS
  have hExact:=(ShiftedCyclicSupportMatrices.displacement_exact (restricted ε S) hJ
    (fun j=>hCharacters j.1)).2
  change LinearMap.range (blockDisplacement ε S)=
    LinearMap.ker ((blockDisplacement ε S)^(p-1)) at hExact
  have hZero : ((blockDisplacement ε S)^(p-1)) (block S z)=0 := by
    rw [←block_power,hz,map_zero]
  have hMember : block S z∈LinearMap.range (blockDisplacement ε S) := by
    rw [hExact]
    exact hZero
  exact hMember

end FairDivision.Topology.Volovikov.ShiftedCyclicTargetBlocks
