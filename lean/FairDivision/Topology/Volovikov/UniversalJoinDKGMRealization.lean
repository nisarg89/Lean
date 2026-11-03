import FairDivision.Topology.Volovikov.UniversalJoinRealization
import RequestProject.Dvoretzky.ElemAb.Main

/-!
# Exact coordinates for the imported DKGM group joins

The local realization uses probability vectors on `(color,label)` pairs.
DKGM uses the same numbers curried as `color → label → ℝ`. The homeomorphism
below only curries/uncurries those coordinates and changes the additive type
tag. It neither subdivides nor changes the number of join factors.

The pinned upstream `GroupJoin` is defined for `G : Type`, so adapters
that mention it use that same universe. Every finite coordinate group in
the BF applications has this type; the purely local coordinate formula
remains universe-polymorphic.

The action convention is explicit: local additive translation by a pulls
coordinates back along h↦−a+h, whereas the upstream right-translation
`joinAct (ofAdd (−a))` pulls back along h↦h−a. They agree for the finite
abelian groups used here. The minus sign is retained, including odd primes.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- The subtype realization used by the pinned upstream theorem. -/
abbrev DKGMJoinSpace (N : ℕ) (G : Type) [Fintype G] :=
  ↥(Dvoretzky.GroupJoin (Multiplicative G) N)

/-- Curry the actual barycentric weights, with no change of coordinates. -/
def universalJoinDKGMCoordinates {N : ℕ} {G : Type*} [Fintype G]
    (x : simplicialRealization (universalJoinComplex N G)) :
    Fin N → Multiplicative G → ℝ :=
  fun i h => x.1.1 (i,h.toAdd)

private theorem universalJoinDKGMCoordinates_mem {N : ℕ} {G : Type} [Fintype G]
    (x : simplicialRealization (universalJoinComplex N G)) :
    universalJoinDKGMCoordinates x ∈ Dvoretzky.GroupJoin (Multiplicative G) N := by
  classical
  refine ⟨fun i h => x.1.2.1 (i,h.toAdd),?_,?_⟩
  · intro i h h' hh hh'
    apply Multiplicative.toAdd.injective
    apply x.2.2 i h.toAdd h'.toAdd
    · exact (FairDivision.Topology.mem_finiteSimplexSupport_iff x.1 _).2
        (lt_of_le_of_ne (x.1.2.1 _) (Ne.symm hh))
    · exact (FairDivision.Topology.mem_finiteSimplexSupport_iff x.1 _).2
        (lt_of_le_of_ne (x.1.2.1 _) (Ne.symm hh'))
  · calc
      (∑ i,∑ h,universalJoinDKGMCoordinates x i h) =
          ∑ i : Fin N,∑ g : G,x.1.1 (i,g) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Fintype.sum_equiv Multiplicative.toAdd _ _ (fun h => rfl)
      _ = ∑ v : Fin N × G,x.1.1 v := (Fintype.sum_prod_type _).symm
      _ = 1 := x.1.2.2

/-- Uncurry the upstream weights into the local probability simplex. -/
def dkgmJoinSimplex {N : ℕ} {G : Type} [Fintype G]
    (x : DKGMJoinSpace N G) : stdSimplex ℝ (Fin N × G) :=
  ⟨fun v => x.1 v.1 (Multiplicative.ofAdd v.2),
    (fun v => x.2.1 v.1 (Multiplicative.ofAdd v.2)),by
      calc
        (∑ v : Fin N × G,x.1 v.1 (Multiplicative.ofAdd v.2)) =
            ∑ i : Fin N,∑ g : G,x.1 i (Multiplicative.ofAdd g) := Fintype.sum_prod_type _
        _ = ∑ i : Fin N,∑ h : Multiplicative G,x.1 i h := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Fintype.sum_equiv Multiplicative.ofAdd _ _ (fun g => rfl)
        _ = 1 := x.2.2.2⟩

private theorem dkgmJoinSimplex_mem {N : ℕ} {G : Type} [Fintype G]
    (x : DKGMJoinSpace N G) :
    dkgmJoinSimplex x ∈ simplicialRealization (universalJoinComplex N G) := by
  classical
  refine ⟨FairDivision.Topology.finiteSimplexSupport_nonempty _,?_⟩
  intro i g h hg hh
  apply Multiplicative.ofAdd.injective
  apply x.2.2.1 i (Multiplicative.ofAdd g) (Multiplicative.ofAdd h)
  · exact ne_of_gt ((FairDivision.Topology.mem_finiteSimplexSupport_iff _ _).1 hg)
  · exact ne_of_gt ((FairDivision.Topology.mem_finiteSimplexSupport_iff _ _).1 hh)

/-- Exact local/upstream realization homeomorphism. It also covers N=0:
both probability-one realizations are empty in that case. -/
noncomputable def universalJoinDKGMHomeomorph (N : ℕ) (G : Type) [Fintype G] :
    simplicialRealization (universalJoinComplex N G) ≃ₜ DKGMJoinSpace N G where
  toFun x := ⟨universalJoinDKGMCoordinates x,universalJoinDKGMCoordinates_mem x⟩
  invFun x := ⟨dkgmJoinSimplex x,dkgmJoinSimplex_mem x⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    rfl
  right_inv x := by
    apply Subtype.ext
    funext i h
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro h
    exact (continuous_apply (i,h.toAdd)).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    exact (continuous_apply_apply v.1 (Multiplicative.ofAdd v.2)).comp
      continuous_subtype_val

@[simp] theorem universalJoinDKGMHomeomorph_apply {N : ℕ} {G : Type} [Fintype G]
    (x : simplicialRealization (universalJoinComplex N G)) (i : Fin N) (h : Multiplicative G) :
    (universalJoinDKGMHomeomorph N G x).1 i h=x.1.1 (i,h.toAdd) := rfl

@[simp] theorem universalJoinDKGMHomeomorph_symm_apply {N : ℕ} {G : Type} [Fintype G]
    (x : DKGMJoinSpace N G) (v : Fin N × G) :
    ((universalJoinDKGMHomeomorph N G).symm x).1.1 v=
      x.1 v.1 (Multiplicative.ofAdd v.2) := rfl

/-- The local pushforward translation has the expected inverse-coordinate
formula. This is independent of either no-map theorem. -/
theorem translateJoinRealization_coordinate {N : ℕ} {G : Type*}
    [AddGroup G] [Fintype G] (a : G)
    (x : simplicialRealization (universalJoinComplex N G)) (i : Fin N) (g : G) :
    (translateJoinRealization a x).1.1 (i,g)=x.1.1 (i,-a+g) := by
  classical
  let e:=translateJoinVertexEquiv (m:=N) a
  have hFiber : Finset.univ.filter (fun v : Fin N × G => e v=(i,g))={e.symm (i,g)} := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · intro h
      exact e.injective (h.trans (e.apply_symm_apply _).symm)
    · intro h
      rw [h,e.apply_symm_apply]
  change (FunOnFinite.linearMap ℝ ℝ e x.1.1) (i,g)=_
  rw [FunOnFinite.linearMap_apply_apply,hFiber]
  simp [e,translateJoinVertexEquiv,translateJoinVertex]

/-- Upstream group translation, as a continuous map of its join subtype. -/
noncomputable def dkgmJoinTranslate {N : ℕ} {G : Type} [AddGroup G] [Fintype G]
    (a : G) : C(DKGMJoinSpace N G,DKGMJoinSpace N G) where
  toFun x := ⟨Dvoretzky.joinAct (Multiplicative.ofAdd a) x.1,
    Dvoretzky.joinAct_mem (Multiplicative.ofAdd a) x.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro h
    exact (continuous_apply_apply i (h*Multiplicative.ofAdd a)).comp
      continuous_subtype_val

/-- Right translation upstream is negative additive translation locally. -/
theorem universalJoinDKGMHomeomorph_translate {N : ℕ} {G : Type}
    [AddCommGroup G] [Fintype G] (a : G)
    (x : simplicialRealization (universalJoinComplex N G)) :
    universalJoinDKGMHomeomorph N G (translateJoinRealization a x)=
      dkgmJoinTranslate (-a) (universalJoinDKGMHomeomorph N G x) := by
  apply Subtype.ext
  funext i h
  change (translateJoinRealization a x).1.1 (i,h.toAdd)=
    x.1.1 (i,h.toAdd + -a)
  rw [translateJoinRealization_coordinate,add_comm (-a) h.toAdd]

/-- The inverse bridge has the same sign convention. -/
theorem universalJoinDKGMHomeomorph_symm_translate {N : ℕ} {G : Type}
    [AddCommGroup G] [Fintype G] (a : G) (x : DKGMJoinSpace N G) :
    (universalJoinDKGMHomeomorph N G).symm (dkgmJoinTranslate a x)=
      translateJoinRealization (-a) ((universalJoinDKGMHomeomorph N G).symm x) := by
  apply (universalJoinDKGMHomeomorph N G).injective
  rw [universalJoinDKGMHomeomorph_translate]
  simp

/-- View any local continuous map as a continuous map on the exact source
subtype appearing in the imported Dold/elementary-abelian statements. -/
noncomputable def universalJoinDKGMContinuousMap {N : ℕ} {G : Type} {Y : Type*}
    [Fintype G] [TopologicalSpace Y]
    (f : C(simplicialRealization (universalJoinComplex N G),Y)) : C(DKGMJoinSpace N G,Y) :=
  f.comp ((universalJoinDKGMHomeomorph N G).symm :
    C(DKGMJoinSpace N G,simplicialRealization (universalJoinComplex N G)))

/-- An ambient function whose restriction is a prescribed subtype map.
Only its source restriction must be continuous; the upstream theorem asks
for ContinuousOn, so the arbitrary value outside the join is harmless. -/
noncomputable def dkgmJoinAmbientExtension {N : ℕ} {G : Type} {Y : Type*} [Fintype G]
    [TopologicalSpace Y] (default : Y) (f : C(DKGMJoinSpace N G,Y)) :
    (Fin N → Multiplicative G → ℝ) → Y := by
  classical
  exact fun x => if hx : x∈Dvoretzky.GroupJoin (Multiplicative G) N then f ⟨x,hx⟩ else default

@[simp] theorem dkgmJoinAmbientExtension_on_source {N : ℕ} {G : Type} {Y : Type*} [Fintype G]
    [TopologicalSpace Y] (default : Y) (f : C(DKGMJoinSpace N G,Y))
    {x : Fin N → Multiplicative G → ℝ} (hx : x∈Dvoretzky.GroupJoin (Multiplicative G) N) :
    dkgmJoinAmbientExtension default f x=f ⟨x,hx⟩ := by
  simp [dkgmJoinAmbientExtension,hx]

theorem dkgmJoinAmbientExtension_continuousOn {N : ℕ} {G : Type} {Y : Type*} [Fintype G]
    [TopologicalSpace Y] (default : Y) (f : C(DKGMJoinSpace N G,Y)) :
    ContinuousOn (dkgmJoinAmbientExtension default f) (Dvoretzky.GroupJoin (Multiplicative G) N) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : (Dvoretzky.GroupJoin (Multiplicative G) N).domRestrict
      (dkgmJoinAmbientExtension default f)=f := by
    funext x
    exact dkgmJoinAmbientExtension_on_source default f x.2
  rw [h]
  exact f.continuous

/-- Direct local-source ambient adapter for the imported theorem. -/
noncomputable def universalJoinDKGMAmbientMap {N : ℕ} {G : Type} {Y : Type*} [Fintype G]
    [TopologicalSpace Y] (default : Y)
    (f : C(simplicialRealization (universalJoinComplex N G),Y)) :
    (Fin N → Multiplicative G → ℝ) → Y :=
  dkgmJoinAmbientExtension default (universalJoinDKGMContinuousMap f)

theorem universalJoinDKGMAmbientMap_continuousOn {N : ℕ} {G : Type} {Y : Type*} [Fintype G]
    [TopologicalSpace Y] (default : Y)
    (f : C(simplicialRealization (universalJoinComplex N G),Y)) :
    ContinuousOn (universalJoinDKGMAmbientMap default f)
      (Dvoretzky.GroupJoin (Multiplicative G) N) :=
  dkgmJoinAmbientExtension_continuousOn default _

@[simp] theorem universalJoinDKGMAmbientMap_on_source {N : ℕ} {G : Type} {Y : Type*} [Fintype G]
    [TopologicalSpace Y] (default : Y)
    (f : C(simplicialRealization (universalJoinComplex N G),Y)) (x : DKGMJoinSpace N G) :
    universalJoinDKGMAmbientMap default f x.1=f ((universalJoinDKGMHomeomorph N G).symm x) := by
  simp [universalJoinDKGMAmbientMap,universalJoinDKGMContinuousMap]

/-- Equivariance transport from the local source; the target action may be
any family of maps. No target no-map or representation premise is hidden. -/
theorem universalJoinDKGMAmbientMap_equivariant {N : ℕ} {G : Type} {Y : Type*}
    [AddCommGroup G] [Fintype G] [TopologicalSpace Y]
    (default : Y) (target : G → Y → Y)
    (f : C(simplicialRealization (universalJoinComplex N G),Y))
    (hf : ∀ a x,f (translateJoinRealization a x)=target a (f x))
    (a : G) {x : Fin N → Multiplicative G → ℝ}
    (hx : x∈Dvoretzky.GroupJoin (Multiplicative G) N) :
    universalJoinDKGMAmbientMap default f (Dvoretzky.joinAct (Multiplicative.ofAdd a) x)=
      target (-a) (universalJoinDKGMAmbientMap default f x) := by
  let point : DKGMJoinSpace N G:=⟨x,hx⟩
  have hTrans:=universalJoinDKGMHomeomorph_symm_translate a point
  change universalJoinDKGMAmbientMap default f (dkgmJoinTranslate a point).1=
    target (-a) (universalJoinDKGMAmbientMap default f point.1)
  rw [universalJoinDKGMAmbientMap_on_source,universalJoinDKGMAmbientMap_on_source,hTrans]
  exact hf (-a) _

end FairDivision.Topology.Volovikov
