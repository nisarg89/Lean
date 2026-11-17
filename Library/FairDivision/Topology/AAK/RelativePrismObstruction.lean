import FairDivision.Topology.AAK.ZeroFreePrismSelection
import FairDivision.Topology.AAK.SuspensionAlphaAction
import FairDivision.Topology.AAK.SuspensionAlphaBoundary
import FairDivision.Topology.Chain.OrderedPrismPath

/-!
# The actual relative suspended-join prism obstruction

The finite-grid selectors are constructed from continuous homotopies in
`SuspendedJoinPrismSelection`. This file maps their actual ordered prisms
through the proved raw-to-relative normalization. The finite time sum
supplies a Dold sequence: its first boundary is the retained south pole,
its successive boundaries are the norm/difference recurrence, and its last
term is zero by the actual suspended-target dimension. The imported Dold
algebra, with the already proved relative exactness, gives the contradiction.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.RelativePrismObstruction

open Dvoretzky Dvoretzky.Dold
open FairDivision.Topology.Chain
open SuspendedJoinPrismSelection ZeroFreeBipyramid
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

/-- Use the same monoid-preserving kernel group as the actual relative
Dold exactness theorem. -/
local instance : AddCommGroup (SuspensionRelativeChains.NonemptyBase (ZMod p) (p-1) p) :=
  SuspensionRelativeChains.nonemptyCanonicalAddCommGroup (R:=ZMod p) (D:=p-1) (p:=p)

abbrev C := Dvoretzky.Dold.Chain (ZMod p) (SourceSpace p)
abbrev T := SuspensionRelativeChains.Relative (ZMod p) (p-1) p

/-- Use the aligned group's operations in the literal prism equations too;
otherwise the direct product instances select the older subtype operations. -/
local instance relativeCanonicalNeg : Neg (T p) :=
  (inferInstance : AddCommGroup (T p)).toNeg

local instance relativeCanonicalSub : Sub (T p) :=
  (inferInstance : AddCommGroup (T p)).toSub

/-- Concrete finite data already provided by the geometric selection theorem. -/
structure Data where
  steps : ℕ
  positive : 0<steps
  subdivisions : ℕ
  sel : Fin (steps+1)→SourceSpace p→TargetVertex p
  south : ∀x∈GroupJoin (Multiplicative (ZMod p)) p,sel 0 x=pole false
  north : ∀x∈GroupJoin (Multiplicative (ZMod p)) p,sel (Fin.last steps) x=pole true
  equivariant : ∀j g x,x∈GroupJoin (Multiplicative (ZMod p)) p→
    sel j (joinAct g x)=suspensionTranslate (-g.toAdd) (sel j x)
  good : ∀k≤p-1,∀l∈(fineChain p subdivisions k).support,
    l.length=k+1 ∧ (∀x∈l,x∈GroupJoin (Multiplicative (ZMod p)) p) ∧
    ∀j : Fin steps,PrismFace p (sel j.castSucc) (sel j.succ) l

/-- Apply the actual relative normalization to the actual finite prism sum. -/
def prismMap (d : Data p) : C p→ₗ[ZMod p]T p :=
  SuspensionRelativeChains.alpha ∘ₗ prismPath d.sel

/-- The only target boundary compatibility needed is proved for each actual
staircase list from its containing suspension face. -/
theorem prismPath_compatible (d : Data p) (k : ℕ) (hk : k≤p-1) :
    prismPath d.sel (fineChain p d.subdivisions k)∈
      Finsupp.supported (ZMod p) (ZMod p)
        {l : List (TargetVertex p)|SuspensionRelativeChains.Compatible l} := by
  simp only [prismPath,LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro j _
  apply map_mem_supported (prism (d.sel j.castSucc) (d.sel j.succ)) _ ?_
    (show fineChain p d.subdivisions k∈Finsupp.supported (ZMod p) (ZMod p)
      {l : List (SourceSpace p)|l∈(fineChain p d.subdivisions k).support} from
        (Finsupp.mem_supported (ZMod p) (fineChain p d.subdivisions k)).mpr (fun _ h=>h))
  intro l hl
  rw [prism_single,one_smul]
  let F := (l.map (d.sel j.castSucc)++l.map (d.sel j.succ)).toFinset
  have hFace : F∈suspensionJoinComplex (p-1) (ZMod p) := (d.good k hk l hl).2.2 j
  have hP := prismList_supported_face (R:=ZMod p)
    (d.sel j.castSucc) (d.sel j.succ) l F
    (fun x hx=>List.mem_toFinset.mpr
      (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨x,hx,rfl⟩))))
    (fun x hx=>List.mem_toFinset.mpr
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨x,hx,rfl⟩))))
  exact Finsupp.supported_mono
    (fun l hl=>SuspensionRelativeChains.compatible_of_face hFace hl) hP

/-- The finite time-grid boundary identity survives actual relative
normalization on every fine source chain used in the Dold sequence. -/
theorem boundary_prismMap (d : Data p) (k : ℕ) (hk : k≤p-1) :
    SuspensionRelativeChains.boundary (prismMap p d (fineChain p d.subdivisions k))+
      prismMap p d (bd (fineChain p d.subdivisions k))=
    SuspensionRelativeChains.alpha (actL (d.sel (Fin.last d.steps))
      (fineChain p d.subdivisions k))-
    SuspensionRelativeChains.alpha (actL (d.sel 0) (fineChain p d.subdivisions k)) := by
  change SuspensionRelativeChains.boundary
      (SuspensionRelativeChains.alpha (prismPath d.sel (fineChain p d.subdivisions k)))+
    SuspensionRelativeChains.alpha (prismPath d.sel (bd (fineChain p d.subdivisions k)))=_
  rw [SuspensionRelativeChains.boundary_alpha_of_supported _ (prismPath_compatible p d k hk),
    ←map_add,bd_prismPath,map_sub]

/-- The same relative prism commutes with the concrete imported generator on
chains carried by the actual source join. -/
theorem prismMap_Td (d : Data p) {c : C p}
    (hc : c∈Finsupp.supported (ZMod p) (ZMod p)
      {l : List (SourceSpace p)|∀x∈l,x∈GroupJoin (Multiplicative (ZMod p)) p}) :
    prismMap p d (Td p c)=(SuspensionRelativeChains.generator (R := ZMod p) (D := p-1) (p := p)) (prismMap p d c) := by
  change SuspensionRelativeChains.alpha (prismPath d.sel (actL (joinAct (gen p)) c))=_
  rw [prismPath_naturality_on_supported (joinAct (gen p))
    (suspensionTranslate (-1 : ZMod p)) d.sel
    (fun j x hx=>by simpa [gen] using d.equivariant j (gen p) x hx) hc]
  exact SuspensionRelativeChains.alpha_translate _

theorem prismMap_Td_pow (d : Data p) (i : ℕ) {c : C p}
    (hc : c∈Finsupp.supported (ZMod p) (ZMod p)
      {l : List (SourceSpace p)|∀x∈l,x∈GroupJoin (Multiplicative (ZMod p)) p}) :
    prismMap p d (((Td (N:=p) p)^i) c)=
      ((SuspensionRelativeChains.generator (R := ZMod p) (D := p-1) (p := p))^i)
        (prismMap p d c) := by
  have hmem : ∀i : ℕ,((Td (N:=p) p)^i) c∈Finsupp.supported (ZMod p) (ZMod p)
      {l : List (SourceSpace p)|∀x∈l,x∈GroupJoin (Multiplicative (ZMod p)) p} := by
    intro i
    induction i with
    | zero => simpa using hc
    | succ i ih =>
      rw [pow_succ',Module.End.mul_apply]
      apply Td_mem_supported (N:=p) p
        (s:={l : List (SourceSpace p)|∀x∈l,x∈GroupJoin (Multiplicative (ZMod p)) p}) ?_ ih
      intro l hl
      change ∀x∈l.map (joinAct (gen p)),x∈GroupJoin (Multiplicative (ZMod p)) p
      intro x hx
      obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hx
      exact joinAct_mem _ (hl y hy)
  induction i with
  | zero => simp only [pow_zero,Module.End.one_apply]
  | succ i ih =>
    rw [pow_succ',Module.End.mul_apply,prismMap_Td p d (hmem i),ih,
      pow_succ',Module.End.mul_apply]

theorem prismMap_rho (d : Data p) (k : ℕ) {c : C p}
    (hc : c∈Finsupp.supported (ZMod p) (ZMod p)
      {l : List (SourceSpace p)|∀x∈l,x∈GroupJoin (Multiplicative (ZMod p)) p}) :
    prismMap p d (rho p k c)=
      altOp (R := ZMod p) (M := T p) (normOp (R := ZMod p) (M := T p) (SuspensionRelativeChains.generator (R := ZMod p) (D := p-1) (p := p)) p)
        ((1 : Module.End (ZMod p) (T p)) - (SuspensionRelativeChains.generator (R := ZMod p) (D := p-1) (p := p))) k (prismMap p d c) := by
  unfold rho altOp
  split_ifs
  · simp only [normOp_apply,map_sum]
    exact Finset.sum_congr rfl (fun i _=>prismMap_Td_pow p d i hc)
  · simp only [LinearMap.sub_apply,Module.End.one_apply,map_sub]
    rw [prismMap_Td p d hc]

/-- Imported source recurrence after the SAME common subdivision. -/
theorem fineChain_boundary_succ (r k : ℕ) :
    bd (fineChain p r (k+1))=rho p k (fineChain p r k) := by
  change bd (((sd : Module.End (ZMod p) (C p))^r) (cseq (N:=p) p (k+1)))=_
  calc
    bd (((sd : Module.End (ZMod p) (C p))^r) (cseq (N:=p) p (k+1)))=
        ((sd : Module.End (ZMod p) (C p))^r) (bd (cseq (N:=p) p (k+1))) := by
      simpa only [Module.End.mul_apply] using
        LinearMap.congr_fun (commute_bd_sdPow (N:=p) p r).eq (cseq (N:=p) p (k+1))
    _=((sd : Module.End (ZMod p) (C p))^r) (rho (N:=p) p k (cseq (N:=p) p k)) := by
      rw [bd_cseq_succ]
    _=rho p k (((sd : Module.End (ZMod p) (C p))^r) (cseq (N:=p) p k)) := by
      simpa only [Module.End.mul_apply] using
        LinearMap.congr_fun (commute_sd_rho (N:=p) p k r).eq (cseq (N:=p) p k)

private theorem sd_singleton (x : SourceSpace p) :
    sd (Finsupp.single [x] (1:ZMod p))=Finsupp.single [x] 1 := by
  rw [sd_single,one_smul,sdList_cons]
  simp [bary,bdList_cons,sd_single,sdList_nil]

/-- The first source vertex is unchanged by barycentric subdivision. -/
theorem fineChain_zero (r : ℕ) :
    fineChain p r 0=Finsupp.single [vtxPt p 0 (1:Multiplicative (ZMod p))] 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (sd^(r+1)) (cseq p 0)=_
    rw [pow_succ',Module.End.mul_apply]
    change sd (fineChain p r 0)=_
    rw [ih,sd_singleton]

/-- A constant north list is zero in the north-relative quotient, including
its empty augmentation and every degenerate higher simplex. -/
theorem alpha_constant_north (l : List (SourceSpace p)) :
    SuspensionRelativeChains.alpha
      (Finsupp.single (l.map (fun _=>pole true : SourceSpace p→TargetVertex p)) (1:ZMod p))=0 := by
  cases l with
  | nil => exact SuspensionRelativeChains.alpha_empty
  | cons x l =>
    cases l with
    | nil => exact SuspensionRelativeChains.alpha_north_singleton
    | cons y l =>
      simp only [List.map_cons,SuspensionRelativeChains.alpha_single,one_smul,
        SuspensionRelativeChains.rawAlphaList_two_poles,map_zero]

/-- A constant south list of at least two vertices is degenerate. -/
theorem alpha_constant_south (l : List (SourceSpace p)) (hl : 2≤l.length) :
    SuspensionRelativeChains.alpha
      (Finsupp.single (l.map (fun _=>pole false : SourceSpace p→TargetVertex p)) (1:ZMod p))=0 := by
  cases l with
  | nil => simp at hl
  | cons x l =>
    cases l with
    | nil => simp at hl
    | cons y l =>
      simp only [List.map_cons,SuspensionRelativeChains.alpha_single,one_smul,
        SuspensionRelativeChains.rawAlphaList_two_poles,map_zero]

private theorem endpoint_north_zero (d : Data p) (k : ℕ) (hk : k≤p-1) :
    SuspensionRelativeChains.alpha
      (actL (d.sel (Fin.last d.steps)) (fineChain p d.subdivisions k))=0 := by
  apply eq_on_supported (M:=T p)
    ((SuspensionRelativeChains.alpha (R:=ZMod p) (D:=p-1) (p:=p)).comp
      (actL (R:=ZMod p) (d.sel (Fin.last d.steps))))
    (0 : C p →ₗ[ZMod p] T p) ?_
    (show fineChain p d.subdivisions k∈Finsupp.supported (ZMod p) (ZMod p)
      {l : List (SourceSpace p)|l∈(fineChain p d.subdivisions k).support} from
      (Finsupp.mem_supported (ZMod p) (fineChain p d.subdivisions k)).mpr (fun _ h=>h))
  intro l hl
  have hMap : l.map (d.sel (Fin.last d.steps))=l.map (fun _=>pole true) :=
    List.map_congr_left (fun x hx=>d.north x ((d.good k hk l hl).2.1 x hx))
  simp only [LinearMap.comp_apply,actL_single,LinearMap.zero_apply,hMap]
  exact alpha_constant_north p l

private theorem endpoint_south_zero (d : Data p) (k : ℕ) (hk : k≤p-1) (hpos : 0<k) :
    SuspensionRelativeChains.alpha (actL (d.sel 0) (fineChain p d.subdivisions k))=0 := by
  apply eq_on_supported (M:=T p)
    ((SuspensionRelativeChains.alpha (R:=ZMod p) (D:=p-1) (p:=p)).comp
      (actL (R:=ZMod p) (d.sel 0)))
    (0 : C p →ₗ[ZMod p] T p) ?_
    (show fineChain p d.subdivisions k∈Finsupp.supported (ZMod p) (ZMod p)
      {l : List (SourceSpace p)|l∈(fineChain p d.subdivisions k).support} from
      (Finsupp.mem_supported (ZMod p) (fineChain p d.subdivisions k)).mpr (fun _ h=>h))
  intro l hl
  have hMap : l.map (d.sel 0)=l.map (fun _=>pole false) :=
    List.map_congr_left (fun x hx=>d.south x ((d.good k hk l hl).2.1 x hx))
  simp only [LinearMap.comp_apply,actL_single,LinearMap.zero_apply,hMap]
  exact alpha_constant_south p l (by have := (d.good k hk l hl).1; omega)

/-- The first relative prism has boundary minus the retained south pole. -/
theorem boundary_prism_first (d : Data p) :
    SuspensionRelativeChains.boundary (prismMap p d (fineChain p d.subdivisions 0))=
      -SuspensionRelativeChains.southPole := by
  have h := boundary_prismMap p d 0 (by omega)
  have hFirst : bd (fineChain p d.subdivisions 0)=Finsupp.single [] 1 := by
    rw [fineChain_zero]
    simp [bdList_cons]
  have hPEmpty : prismMap p d (Finsupp.single [] (1:ZMod p))=0 := by
    simp only [prismMap,LinearMap.comp_apply,prismPath,LinearMap.sum_apply,
      prism_nil,Finset.sum_const_zero,map_zero]
  have hSouth : SuspensionRelativeChains.alpha
      (actL (d.sel 0) (fineChain p d.subdivisions 0))=
      SuspensionRelativeChains.southPole := by
    rw [fineChain_zero,actL_single]
    have hV : VList p 0 [vtxPt p 0 (1:Multiplicative (ZMod p))] := ⟨fun _=>1,by simp⟩
    have hJ := hV.hull_subset (Fact.out : p.Prime).pos
      (mem_hull_of_mem (List.mem_singleton_self _))
    rw [List.map_singleton,d.south _ hJ]
    exact SuspensionRelativeChains.alpha_south_singleton
  rw [hFirst,hPEmpty,add_zero,endpoint_north_zero p d 0 (by omega),hSouth,zero_sub] at h
  exact h

/-- The top prism vanishes because its lists have p+1 vertices, while the
actual target suspension has only p possible vertices per simplex. -/
theorem prism_last_zero (d : Data p) :
    prismMap p d (fineChain p d.subdivisions (p-1))=0 := by
  apply SuspensionRelativeChains.alpha_eq_zero_of_supported_length
  have hLen : fineChain p d.subdivisions (p-1)∈Finsupp.supported (ZMod p) (ZMod p)
      {l : List (SourceSpace p)|l.length=(p-1)+1} := by
    rw [Finsupp.mem_supported]
    intro l hl
    exact (d.good (p-1) le_rfl l hl).1
  have hP := prismPath_supported_length d.sel ((p-1)+1) hLen
  exact Finsupp.supported_mono (fun l hl=>by dsimp at hl ⊢; omega) hP

/-- The actual sign-corrected Dold sequence. -/
def sequence (d : Data p) (k : ℕ) : T p :=
  (-1 : ZMod p)^(k+1) •prismMap p d (fineChain p d.subdivisions k)

theorem sequence_first (d : Data p) :
    SuspensionRelativeChains.boundary (sequence p d 0)=SuspensionRelativeChains.southPole := by
  simp only [sequence,zero_add,pow_one,map_smul,boundary_prism_first]
  apply Prod.ext
  · apply Subtype.ext
    change (-1 : ZMod p) • ((-1 : ZMod p) •
      (0 : SuspensionRelativeChains.Base (ZMod p) (p-1) p))=0
    rw [smul_zero,smul_zero]
  · apply Prod.ext
    · apply Subtype.ext
      change (-1 : ZMod p) • ((-1 : ZMod p) •
        (0 : SuspensionRelativeChains.Base (ZMod p) (p-1) p))=0
      rw [smul_zero,smul_zero]
    · change (-1 : ZMod p) •
        -(SuspensionRelativeChains.empty : SuspensionRelativeChains.Base (ZMod p) (p-1) p)=
        SuspensionRelativeChains.empty
      exact (neg_smul_neg (1 : ZMod p)
        (SuspensionRelativeChains.empty : SuspensionRelativeChains.Base (ZMod p) (p-1) p)).trans
        (one_smul _ _)

theorem sequence_boundary (d : Data p) (k : ℕ) (hk : k<p-1) :
    SuspensionRelativeChains.boundary (sequence p d (k+1))=
      altOp (R := ZMod p) (M := T p) (normOp (R := ZMod p) (M := T p) (SuspensionRelativeChains.generator (R := ZMod p) (D := p-1) (p := p)) p)
        ((1 : Module.End (ZMod p) (T p)) - (SuspensionRelativeChains.generator (R := ZMod p) (D := p-1) (p := p))) k (sequence p d k) := by
  have h := boundary_prismMap p d (k+1) (by omega)
  rw [endpoint_north_zero p d (k+1) (by omega),endpoint_south_zero p d (k+1) (by omega)
    (by omega),sub_zero,fineChain_boundary_succ] at h
  have hc : fineChain p d.subdivisions k∈Finsupp.supported (ZMod p) (ZMod p)
      {l : List (SourceSpace p)|∀x∈l,x∈GroupJoin (Multiplicative (ZMod p)) p} := by
    rw [Finsupp.mem_supported]
    intro l hl
    exact (d.good k (by omega) l hl).2.1
  rw [prismMap_rho p d k hc] at h
  have hBoundary := eq_neg_of_add_eq_zero_left h
  simp only [sequence,map_smul]
  rw [hBoundary,smul_neg,←neg_smul]
  congr 1
  rw [show k+1+1=(k+1)+1 by omega,pow_succ]
  ring

/-- Concrete finite-data contradiction, with all relative target exactness
already proved by the imported fundamental-domain projection. -/
theorem impossible (d : Data p) : False := by
  apply SuspensionRelativeChains.no_sequence (R:=ZMod p) (D:=p-1) (p:=p)
    (p-1) (sequence p d) (sequence_first p d)
    (fun k hk=>sequence_boundary p d k hk)
  simp [sequence,prism_last_zero]

/-- No continuous equivariant pole-to-pole homotopy exists in this actual
suspended free join. Every geometric and algebraic premise is constructed. -/
theorem no_pole_homotopy
    (H : C(unitInterval × Source p, Target p))
    (hSouth : ∀x,H (0,x)=suspensionPole (p-1) (ZMod p) false)
    (hNorth : ∀x,H (1,x)=suspensionPole (p-1) (ZMod p) true)
    (heq : ∀g t x,H (t,sourceAct p g x)=
      suspensionRelabel p (-g.toAdd) (H (t,x))) : False := by
  obtain ⟨K,hK,r,sel,hS,hN,hEq,hGood⟩ :=
    exists_fine_prism_selection p H hSouth hNorth heq
  exact impossible p ⟨K,hK,r,sel,hS,hN,hEq,hGood⟩

/-- The full continuous prime-cyclic sign-reversal zero theorem on the
p-fold join, obtained from the actual pole/prism obstruction. -/
theorem cyclic_sign_reversal_has_zero
    (H : C(Source p × unitInterval, ZMod p→ℝ))
    (hneg : ∀x v,H (x,0) v<0) (hpos : ∀x v,0<H (x,1) v)
    (heq : ∀g x t,H (sourceAct p g x,t)=
      permuteVector (cyclicPerm (-g.toAdd)) (H (x,t))) :
    ∃q,H q=0 := by
  by_contra hn
  have hNonzero : ∀q,H q≠0 := by simpa only [not_exists] using hn
  exact no_pole_homotopy p (fromZeroFree p H hNonzero hneg hpos)
    (fromZeroFree_south p H hNonzero hneg hpos)
    (fromZeroFree_north p H hNonzero hneg hpos)
    (fromZeroFree_equivariant p H hNonzero hneg hpos heq)

end FairDivision.Topology.AAK.RelativePrismObstruction
