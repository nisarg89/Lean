import FairDivision.Topology.Volovikov.ShiftedCyclicSource
import FairDivision.Topology.Volovikov.ShiftedCyclicTarget
import RequestProject.Dvoretzky.Dold.Main

/-!
# Equivariant simplicial approximation for the actual shifted actions

The geometric map is equivariant for the genuine elementary-abelian
generators. Vertex selection is proved equivariant for their colorwise
cyclic label shifts, retaining inverse signs. The resulting linear chain
map commutes with their common scalar-weighted shifted operator and its
alternating norm/difference sequence on the actual supported chains.

The consistency estimate is the same uniform-continuity estimate used
in the imported Dold proof, now with independent source and target label
sets and with the actual generic coefficient field.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Volovikov.ShiftedCyclicApproximation

open scoped BigOperators
open Dvoretzky Dvoretzky.Dold
open OddPrimeTwistedJoinChains
open OddPrimeTensorSource (Group generator)
open ShiftedCyclicSupportMatrices (GenericField weights)

variable {p r N D : ℕ} [Fact p.Prime]

/-- Pullback action on the target realization; vertices move oppositely. -/
def pointShift (ε : Fin D→ZMod p) (y : Fin D→Label p→ℝ) : Fin D→Label p→ℝ :=
  fun j h=>y j (h*Multiplicative.ofAdd (ε j))

def vertexShift (ε : Fin D→ZMod p) (v : Fin D×Label p) : Fin D×Label p :=
  (v.1,v.2*Multiplicative.ofAdd (-ε v.1))

theorem twistS_none_iff (ε : Fin D→ZMod p) (s : Smp D (Label p)) (j : Fin D) :
    twistS ε s j=none ↔ s j=none := by
  simp [twistS]

/-- The generic oriented wedge formula, with ALL boundary signs retained. -/
theorem wedgeS_twist {R : Type*} [CommRing R]
    (ε : Fin D→ZMod p) (v : Fin D×Label p) (s : Smp D (Label p)) :
    (wedgeS (vertexShift ε v) (twistS ε s) : TChain R D (Label p))=
      twistL ε (wedgeS v s) := by
  classical
  simp only [wedgeS,vertexShift,twistS_none_iff]
  split_ifs
  · rw [map_smul,twistL_single,sgnP_twistS,twistS_update]
    rfl
  · simp

theorem wedge_twist {R : Type*} [CommRing R]
    (ε : Fin D→ZMod p) (v : Fin D×Label p) (c : TChain R D (Label p)) :
    wedge (vertexShift ε v) (twistL ε c)=twistL ε (wedge v c) := by
  have h :
      (wedge (vertexShift ε v)∘ₗtwistL ε :
        TChain R D (Label p)→ₗ[R]TChain R D (Label p))=
      twistL ε∘ₗwedge v :=
    tchain_hom_ext (fun s=>by simp [wedgeS_twist])
  exact LinearMap.congr_fun h c

theorem alpha_map_vertexShift {R : Type*} [CommRing R]
    (ε : Fin D→ZMod p) (l : List (Fin D×Label p)) :
    (alpha (l.map (vertexShift ε)) : TChain R D (Label p))=twistL ε (alpha l) := by
  induction l with
  | nil=>simp [alpha,twistL_empty]
  | cons v l ih=>rw [List.map_cons,alpha,alpha,ih,wedge_twist]

section Selection

variable (Φ : (Fin N→Group p r→ℝ)→Fin (D+1)→Label p→ℝ)

/-- Canonical vertex selection respects a colorwise cyclic pullback.
No self-inverse identification is used at odd primes. -/
theorem vertex_selection_shift {x : Fin N→Group p r→ℝ}
    (g : Group p r) (ε : Fin (D+1)→ZMod p)
    (hx : Φ x∈GroupJoin (Label p) (D+1))
    (hEq : Φ (joinAct g x)=pointShift ε (Φ x)) :
    vtxSel Φ (joinAct g x)=vertexShift ε (vtxSel Φ x) := by
  classical
  have hS : selSet Φ (joinAct g x)=selSet Φ x := by
    ext j
    simp only [selSet,Finset.mem_filter,Finset.mem_univ,true_and,hEq,pointShift]
    constructor
    · rintro ⟨h,hh⟩
      exact ⟨h*Multiplicative.ofAdd (ε j),hh⟩
    · rintro ⟨h,hh⟩
      refine ⟨h*Multiplicative.ofAdd (-ε j),?_⟩
      simpa only [mul_assoc,←ofAdd_add,neg_add_cancel,
        ofAdd_zero,mul_one] using hh
  have hne:=selSet_nonempty Φ hx
  have hne' : (selSet Φ (joinAct g x)).Nonempty:=hS.symm▸hne
  have hmin : (selSet Φ (joinAct g x)).min' hne'=(selSet Φ x).min' hne := by
    apply le_antisymm
    · exact Finset.min'_le _ _ (by rw [hS];exact Finset.min'_mem _ hne)
    · exact Finset.min'_le _ _ (by rw [←hS];exact Finset.min'_mem _ hne')
  have hmem : ∃h,(1 : ℝ)/(D+1)≤Φ x ((selSet Φ x).min' hne) h := by
    have h:=Finset.min'_mem _ hne
    simpa only [selSet,Finset.mem_filter,Finset.mem_univ,true_and] using h
  have hmem' : ∃h,(1 : ℝ)/(D+1)≤
      Φ (joinAct g x) ((selSet Φ (joinAct g x)).min' hne') h := by
    have h:=Finset.min'_mem _ hne'
    simpa only [selSet,Finset.mem_filter,Finset.mem_univ,true_and] using h
  simp only [vtxSel,dif_pos hne,dif_pos hne',dif_pos hmem,dif_pos hmem',vertexShift]
  refine Prod.ext hmin ?_
  have key (c : Label p) (hc : (1 : ℝ)/(D+1)≤
      Φ (joinAct g x) ((selSet Φ (joinAct g x)).min' hne') c) :
      c=hmem.choose*Multiplicative.ofAdd (-ε ((selSet Φ x).min' hne)) := by
    have h₂:=hmem.choose_spec
    rw [hEq,hmin] at hc
    change (1 : ℝ)/(D+1)≤Φ x ((selSet Φ x).min' hne)
      (c*Multiplicative.ofAdd (ε ((selSet Φ x).min' hne))) at hc
    have hpos : (0 : ℝ)<1/(D+1):=by positivity
    have hLabels:=hx.2.1 _ _ _
      (ne_of_gt (lt_of_lt_of_le hpos hc)) (ne_of_gt (lt_of_lt_of_le hpos h₂))
    calc
      c=(c*Multiplicative.ofAdd (ε ((selSet Φ x).min' hne)))*
          Multiplicative.ofAdd (-ε ((selSet Φ x).min' hne)) := by
        simp [mul_assoc,←ofAdd_add]
      _=hmem.choose*Multiplicative.ofAdd (-ε ((selSet Φ x).min' hne)) :=
        congrArg (fun l=>l*Multiplicative.ofAdd (-ε ((selSet Φ x).min' hne))) hLabels
  exact key _ hmem'.choose_spec

/-- The existing Dold consistency estimate with distinct finite label
sets; this is independent of the chain coefficient field. -/
theorem consistent_of_close
    (hmaps : ∀x∈GroupJoin (Group p r) N,Φ x∈GroupJoin (Label p) (D+1))
    {δ : ℝ}
    (hδ : ∀x∈GroupJoin (Group p r) N,∀y∈GroupJoin (Group p r) N,
      dist x y<δ→dist (Φ x) (Φ y)<1/(2*(D+1)))
    {l : List (Fin N→Group p r→ℝ)}
    (hJoin : ∀y∈l,y∈GroupJoin (Group p r) N)
    (hClose : ∀y∈l,∀z∈l,dist y z<δ) : Consistent (l.map (vtxSel Φ)) := by
  intro a ha b hb hab
  obtain ⟨x,hx,rfl⟩:=List.mem_map.mp ha
  obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hb
  have h₁:=vtxSel_spec Φ (hmaps x (hJoin x hx))
  have h₂:=vtxSel_spec Φ (hmaps y (hJoin y hy))
  rw [hab] at h₁
  have hc : dist (Φ x (vtxSel Φ y).1 (vtxSel Φ y).2)
      (Φ y (vtxSel Φ y).1 (vtxSel Φ y).2)<1/(2*(D+1)) :=
    lt_of_le_of_lt ((dist_le_pi_dist _ _ _).trans (dist_le_pi_dist _ _ _))
      (hδ x (hJoin x hx) y (hJoin y hy) (hClose x hx y hy))
  rw [Real.dist_eq] at hc
  have hpos : (0 : ℝ)<1/(D+1):=by positivity
  have hOther : 0<Φ x (vtxSel Φ y).1 (vtxSel Φ y).2 := by
    have hLower:=(abs_lt.mp hc).1
    have hHalf : (1 : ℝ)/(2*(D+1))=(1/(D+1))/2:=by field_simp
    rw [hHalf] at hLower
    linarith
  exact Prod.ext hab ((hmaps x (hJoin x hx)).2.1 _ _ _
    (ne_of_gt (lt_of_lt_of_le hpos h₁)) (ne_of_gt hOther))

end Selection

section ChainMap

abbrev Coefficient (p r : ℕ) := GenericField p r
abbrev Source (p r N : ℕ) [Fact p.Prime] :=
  ShiftedCyclicSource.SourceChain p r N (Coefficient p r)

variable (Φ : (Fin N→Group p r→ℝ)→Fin (D+1)→Label p→ℝ)

def psi : Source p r N→ₗ[Coefficient p r]TChain (Coefficient p r) (D+1) (Label p) :=
  alphaL∘ₗactL (vtxSel Φ)

@[simp] theorem psi_single (l : List (Fin N→Group p r→ℝ)) :
    psi Φ (Finsupp.single l 1)=alpha (l.map (vtxSel Φ)) := by simp [psi]

theorem psi_boundary {c : Source p r N}
    (hc : c∈Finsupp.supported (Coefficient p r) (Coefficient p r)
      {l | Consistent (l.map (vtxSel Φ))}) :
    psi Φ (bd c)=bdT (psi Φ c) := by
  apply eq_on_supported (psi Φ∘ₗbd) (bdT∘ₗpsi Φ) (fun l hl=>?_) hc
  simp only [LinearMap.coe_comp,Function.comp_apply,bd_single,one_smul,psi,
    actL_bdList,actL_single,alphaL_single]
  exact (bdT_alpha (R:=Coefficient p r) hl).symm

variable (ε : Fin r→Fin (D+1)→ZMod p)
    (hMaps : ∀x∈GroupJoin (Group p r) N,Φ x∈GroupJoin (Label p) (D+1))
    (hEq : ∀q : Fin r,∀x∈GroupJoin (Group p r) N,
      Φ (joinAct (generator (p:=p) q) x)=pointShift (ε q) (Φ x))

include hMaps hEq

theorem psi_generator (q : Fin r) {c : Source p r N}
    (hc : c∈Finsupp.supported (Coefficient p r) (Coefficient p r)
      {l | ∀y∈l,y∈GroupJoin (Group p r) N}) :
    psi Φ (ShiftedCyclicSource.generatorAction p r N (Coefficient p r) q c)=
      twistL (ε q) (psi Φ c) := by
  apply eq_on_supported
    (psi Φ∘ₗShiftedCyclicSource.generatorAction p r N (Coefficient p r) q)
    (twistL (ε q)∘ₗpsi Φ) (fun l hl=>?_) hc
  change psi Φ (actL (joinAct (generator (p:=p) q)) (Finsupp.single l 1))=
    twistL (ε q) (psi Φ (Finsupp.single l 1))
  simp only [actL_single,psi_single]
  rw [←alpha_map_vertexShift]
  simp only [List.map_map]
  congr 1
  exact List.map_congr_left (fun y hy=>
    vertex_selection_shift Φ _ (ε q) (hMaps y (hl y hy)) (hEq q y (hl y hy)))

theorem psi_shifted {c : Source p r N}
    (hc : c∈Finsupp.supported (Coefficient p r) (Coefficient p r)
      {l | ∀y∈l,y∈GroupJoin (Group p r) N}) :
    psi Φ (ShiftedCyclicSource.shifted p r N (Coefficient p r)
      (weights (p:=p) (r:=r)) c)=ShiftedCyclicTarget.shifted ε (psi Φ c) := by
  classical
  simp only [ShiftedCyclicSource.shifted,ShiftedCyclicTarget.shifted,
    ShiftedCyclicTargetBlocks.displacement,ShiftedCyclicAlgebra.shifted,
    ShiftedCyclicAlgebra.displacement,LinearMap.add_apply,Module.End.one_apply,
    LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.sub_apply,map_add,map_sum,map_smul,map_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [psi_generator Φ ε hMaps hEq q hc]

theorem source_shift_supported {c : Source p r N}
    (hc : c∈Finsupp.supported (Coefficient p r) (Coefficient p r)
      {l | ∀y∈l,y∈GroupJoin (Group p r) N}) :
    ShiftedCyclicSource.shifted p r N (Coefficient p r)
      (weights (p:=p) (r:=r)) c∈Finsupp.supported (Coefficient p r) (Coefficient p r)
        {l | ∀y∈l,y∈GroupJoin (Group p r) N} := by
  apply ShiftedCyclicSource.shifted_mem_supported p r N (Coefficient p r) _ ?_ hc
  intro q l hl y hy
  obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hy
  exact joinAct_mem _ (hl x hx)

theorem psi_shifted_power (n : ℕ) {c : Source p r N}
    (hc : c∈Finsupp.supported (Coefficient p r) (Coefficient p r)
      {l | ∀y∈l,y∈GroupJoin (Group p r) N}) :
    psi Φ (((ShiftedCyclicSource.shifted p r N (Coefficient p r)
      (weights (p:=p) (r:=r)))^n) c)=
      ((ShiftedCyclicTarget.shifted ε)^n) (psi Φ c) := by
  have hSupport : ∀k : ℕ,((ShiftedCyclicSource.shifted p r N (Coefficient p r)
      (weights (p:=p) (r:=r)))^k) c∈
      Finsupp.supported (Coefficient p r) (Coefficient p r)
        {l | ∀y∈l,y∈GroupJoin (Group p r) N} := by
    intro k
    induction k with
    | zero=>simpa using hc
    | succ k ih=>
        rw [pow_succ',Module.End.mul_apply]
        exact source_shift_supported Φ ε hMaps hEq ih
  induction n with
  | zero=>rfl
  | succ n ih=>rw [pow_succ',Module.End.mul_apply,
      psi_shifted Φ ε hMaps hEq (hSupport n),ih,pow_succ',Module.End.mul_apply]

theorem psi_rho (k : ℕ) {c : Source p r N}
    (hc : c∈Finsupp.supported (Coefficient p r) (Coefficient p r)
      {l | ∀y∈l,y∈GroupJoin (Group p r) N}) :
    psi Φ (ShiftedCyclicSource.rho p r N (Coefficient p r)
      (weights (p:=p) (r:=r)) k c)=
      altOp (normOp (ShiftedCyclicTarget.shifted ε) p)
        (1-ShiftedCyclicTarget.shifted ε) k (psi Φ c) := by
  unfold ShiftedCyclicSource.rho altOp
  split_ifs
  · simp only [normOp_apply,map_sum]
    exact Finset.sum_congr rfl (fun i hi=>psi_shifted_power Φ ε hMaps hEq i hc)
  · simp only [LinearMap.sub_apply,Module.End.one_apply,map_sub]
    rw [psi_shifted Φ ε hMaps hEq hc]

end ChainMap

end FairDivision.Topology.Volovikov.ShiftedCyclicApproximation
