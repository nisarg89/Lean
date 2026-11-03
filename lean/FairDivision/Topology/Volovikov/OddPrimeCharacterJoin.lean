import FairDivision.Topology.Volovikov.OddPrimeCharacterExtrema
import RequestProject.Dvoretzky.Dold.Main

/-!
# A concrete two-color cyclic join map for character circles

Products of positive real-coordinate differences select the unique
maximum and minimum charts proved in OddPrimeCharacterExtrema. Each color
has at most one active group label, and at least one color is active away
from zero. All weights are finite products of continuous real functions.
The construction commutes with the character action exactly.

Joining q such circles produces an actual map to 2q copies of Z/p, so
upstream's chain-level cyclic Dold theorem gives a sharp dimensional
obstruction for any collection of q nontrivial cyclic characters.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Volovikov.OddPrimeCharacterJoin

open scoped BigOperators
open OddPrimeCharacterExtrema

private def difference (lower : Bool) (u v : ℂ) : ℝ :=
  if lower then v.re-u.re else u.re-v.re

/-- `false` selects a strict maximum; `true` selects a strict minimum.
The diagonal factor is one, so singleton/empty-product conventions do not
insert a discontinuity. -/
def weight {p : ℕ} [NeZero p] (ψ : AddChar (ZMod p) ℂ)
    (z : ℂ) (lower : Bool) (g : ZMod p) : ℝ :=
  ∏h : ZMod p,if h=g then 1 else max 0 (difference lower (orbit ψ z g) (orbit ψ z h))

theorem weight_nonnegative {p : ℕ} [NeZero p]
    (ψ : AddChar (ZMod p) ℂ) (z : ℂ) (lower : Bool) (g : ZMod p) :
    0≤weight ψ z lower g := by
  classical
  apply Finset.prod_nonneg
  intro h hh
  split_ifs
  · norm_num
  · exact le_max_left _ _

/-- A nonzero weight certifies all of its strict comparisons. -/
theorem strict_of_weight_ne_zero {p : ℕ} [NeZero p]
    (ψ : AddChar (ZMod p) ℂ) (z : ℂ) (lower : Bool) (g : ZMod p)
    (hg : weight ψ z lower g≠0) (h : ZMod p) (hne : h≠g) :
    0<difference lower (orbit ψ z g) (orbit ψ z h) := by
  classical
  have hf := Finset.prod_ne_zero_iff.mp hg h (Finset.mem_univ h)
  simp only [if_neg hne] at hf
  have hpos : 0< max 0 (difference lower (orbit ψ z g) (orbit ψ z h)) :=
    lt_of_le_of_ne (le_max_left _ _) (Ne.symm hf)
  simpa only [lt_max_iff,lt_self_iff_false,false_or] using hpos

/-- Different labels never have positive mass in the same color. -/
theorem weight_unique {p : ℕ} [NeZero p]
    (ψ : AddChar (ZMod p) ℂ) (z : ℂ) (lower : Bool) (g h : ZMod p)
    (hg : weight ψ z lower g≠0) (hh : weight ψ z lower h≠0) : g=h := by
  by_contra hne
  have ha:=strict_of_weight_ne_zero ψ z lower g hg h (Ne.symm hne)
  have hb:=strict_of_weight_ne_zero ψ z lower h hh g hne
  cases lower <;> simp only [difference,Bool.false_eq_true,if_false,if_true] at ha hb <;> linarith

/-- The scalar origin contributes no mass. Prime order supplies a second
label, so at least one actual off-diagonal factor vanishes. -/
@[simp] theorem weight_zero {p : ℕ} [Fact p.Prime]
    (ψ : AddChar (ZMod p) ℂ) (lower : Bool) (g : ZMod p) :
    weight ψ 0 lower g=0 := by
  classical
  obtain ⟨h,hne⟩:=exists_ne g
  apply Finset.prod_eq_zero (Finset.mem_univ h)
  simp [hne,difference,orbit]

/-- An odd-prime character circle always activates one actual chart. -/
theorem exists_positive_weight (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ≠0) {z : ℂ} (hz : z≠0) :
    ∃lower : Bool,∃g : ZMod p,0<weight ψ z lower g := by
  classical
  obtain ⟨g,hMaximum|hMinimum⟩:=exists_strict_extremum p hp ψ hψ hz
  · refine ⟨false,g,?_⟩
    apply Finset.prod_pos
    intro h hh
    split_ifs with hne
    · norm_num
    · have hd:=hMaximum h hne
      simp only [difference,Bool.false_eq_true,if_false]
      exact lt_max_of_lt_right (sub_pos.mpr hd)
  · refine ⟨true,g,?_⟩
    apply Finset.prod_pos
    intro h hh
    split_ifs with hne
    · norm_num
    · have hd:=hMinimum h hne
      simp only [difference,if_true]
      exact lt_max_of_lt_right (sub_pos.mpr hd)

/-- Multiplying by the character value translates the actual label. -/
theorem weight_character_mul {p : ℕ} [NeZero p]
    (ψ : AddChar (ZMod p) ℂ) (z : ℂ) (lower : Bool) (a g : ZMod p) :
    weight ψ (ψ a*z) lower g=weight ψ z lower (g+a) := by
  classical
  unfold weight
  apply Fintype.prod_equiv (Equiv.addRight a)
  intro h
  have hOrbit (k : ZMod p) : orbit ψ (ψ a*z) k=orbit ψ z (k+a) := by
    simp [orbit,ψ.map_add_eq_mul,mul_assoc]
  rw [hOrbit,hOrbit]
  by_cases hEq : h=g
  · simp [hEq]
  · simp [hEq]

theorem weight_continuous {p : ℕ} [NeZero p]
    (ψ : AddChar (ZMod p) ℂ) (lower : Bool) (g : ZMod p) :
    Continuous (fun z : ℂ=>weight ψ z lower g) := by
  classical
  unfold weight
  apply continuous_finset_prod
  intro h hh
  split_ifs
  · exact continuous_const
  · unfold difference
    cases lower <;>
      exact continuous_const.max
        ((Complex.continuous_re.comp (continuous_const.mul continuous_id)).sub
          (Complex.continuous_re.comp (continuous_const.mul continuous_id)))

/-- The two colors for each character are given one fixed finite index
set; this is only a reindexing, not an extra target color. -/
noncomputable def colorEquiv (q : ℕ) : (Fin q×Bool)≃Fin (q+q) :=
  (Fintype.equivFin (Fin q×Bool)).trans (finCongr (by
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    omega))

def total {p q : ℕ} [NeZero p] (ψ : Fin q→AddChar (ZMod p) ℂ)
    (z : Fin q→ℂ) : ℝ :=
  ∑c : Fin q×Bool,∑g : ZMod p,weight (ψ c.1) (z c.1) c.2 g

def joinMap {p q : ℕ} [NeZero p] (ψ : Fin q→AddChar (ZMod p) ℂ)
    (z : Fin q→ℂ) : Fin (q+q)→Multiplicative (ZMod p)→ℝ :=
  fun j g=>let c:=(colorEquiv q).symm j
    weight (ψ c.1) (z c.1) c.2 g.toAdd/total ψ z

theorem total_positive (p q : ℕ) [Fact p.Prime] (hp : p≠2)
    (ψ : Fin q→AddChar (ZMod p) ℂ) (hψ : ∀i,ψ i≠0)
    (z : Fin q→ℂ) (hz : z≠0) : 0<total ψ z := by
  classical
  obtain ⟨i,hi⟩ : ∃i : Fin q,z i≠0 := by
    by_contra h
    push_neg at h
    exact hz (funext h)
  obtain ⟨b,g,hg⟩:=exists_positive_weight p hp (ψ i) (hψ i) hi
  apply hg.trans_le
  apply (Finset.single_le_sum
    (fun h _=>weight_nonnegative (ψ i) (z i) b h) (Finset.mem_univ g)).trans
  exact Finset.single_le_sum
    (fun c _=>Finset.sum_nonneg (fun h _=>weight_nonnegative (ψ c.1) (z c.1) c.2 h))
    (Finset.mem_univ (i,b))

theorem joinMap_mem (p q : ℕ) [Fact p.Prime] (hp : p≠2)
    (ψ : Fin q→AddChar (ZMod p) ℂ) (hψ : ∀i,ψ i≠0)
    (z : Fin q→ℂ) (hz : z≠0) :
    joinMap ψ z∈Dvoretzky.GroupJoin (Multiplicative (ZMod p)) (q+q) := by
  classical
  have hT:=total_positive p q hp ψ hψ z hz
  refine ⟨?_,?_,?_⟩
  · intro j g
    exact div_nonneg (weight_nonnegative _ _ _ _) hT.le
  · intro j g h hg hh
    apply Multiplicative.toAdd.injective
    let c:=(colorEquiv q).symm j
    apply weight_unique (ψ c.1) (z c.1) c.2 g.toAdd h.toAdd
    · intro hw
      apply hg
      change weight (ψ c.1) (z c.1) c.2 g.toAdd/total ψ z=0
      rw [hw,zero_div]
    · intro hw
      apply hh
      change weight (ψ c.1) (z c.1) c.2 h.toAdd/total ψ z=0
      rw [hw,zero_div]
  · unfold joinMap
    simp only [←Finset.sum_div]
    have hSum : (∑j : Fin (q+q),∑g : Multiplicative (ZMod p),
        weight (ψ ((colorEquiv q).symm j).1)
          (z ((colorEquiv q).symm j).1) ((colorEquiv q).symm j).2 g.toAdd)=total ψ z := by
      calc
        _ = ∑c : Fin q×Bool,∑g : Multiplicative (ZMod p),
            weight (ψ c.1) (z c.1) c.2 g.toAdd :=
          Fintype.sum_equiv (colorEquiv q).symm _ _ (fun j=>rfl)
        _ = total ψ z := by
          apply Finset.sum_congr rfl
          intro c hc
          exact Fintype.sum_equiv Multiplicative.toAdd _ _ (fun g=>rfl)
    rw [hSum,div_self hT.ne']

theorem total_character_mul {p q : ℕ} [NeZero p]
    (ψ : Fin q→AddChar (ZMod p) ℂ) (z : Fin q→ℂ) (a : ZMod p) :
    total ψ (fun i=>ψ i a*z i)=total ψ z := by
  classical
  unfold total
  apply Finset.sum_congr rfl
  intro c hc
  simp only [weight_character_mul]
  exact Fintype.sum_equiv (Equiv.addRight a) _ _ (fun g=>rfl)

theorem joinMap_character_mul {p q : ℕ} [NeZero p]
    (ψ : Fin q→AddChar (ZMod p) ℂ) (z : Fin q→ℂ) (a : ZMod p) :
    joinMap ψ (fun i=>ψ i a*z i)=
      Dvoretzky.joinAct (Multiplicative.ofAdd a) (joinMap ψ z) := by
  funext j g
  simp [joinMap,Dvoretzky.joinAct,weight_character_mul,total_character_mul]

/-- Continuity only excludes the actual zero vector, at which no chart
normalization is needed. No angle branches enter the map. -/
theorem joinMap_continuousOn {p q : ℕ} [NeZero p]
    (ψ : Fin q→AddChar (ZMod p) ℂ) :
    ContinuousOn (joinMap ψ) {z | total ψ z≠0} := by
  have hTotal : Continuous (total ψ) := by
    apply continuous_finset_sum
    intro c hc
    apply continuous_finset_sum
    intro g hg
    exact (weight_continuous (ψ c.1) c.2 g).comp (continuous_apply c.1)
  apply continuousOn_pi.mpr
  intro j
  apply continuousOn_pi.mpr
  intro g
  exact (((weight_continuous _ _ _).comp (continuous_apply _)).continuousOn).div
    hTotal.continuousOn (fun z hz=>hz)

/-- The pinned cyclic Dold theorem with an arbitrary positive target
color count. This is just the successor reindexing of its D+1 notation. -/
theorem dold_join_positive_target (p : ℕ) [Fact p.Prime]
    {N M : ℕ} (hM : 0<M) (hDimension : M<N)
    (Φ : (Fin N→Multiplicative (ZMod p)→ℝ)→Fin M→Multiplicative (ZMod p)→ℝ)
    (hc : ContinuousOn Φ (Dvoretzky.GroupJoin _ N))
    (hm : ∀x∈Dvoretzky.GroupJoin _ N,Φ x∈Dvoretzky.GroupJoin _ M)
    (he : ∀a,∀x∈Dvoretzky.GroupJoin _ N,
      Φ (Dvoretzky.joinAct a x)=Dvoretzky.joinAct a (Φ x)) : False := by
  cases M with
  | zero => omega
  | succ D => exact Dvoretzky.Dold.dold_join p hDimension Φ hc hm he

/-- The chain-level cyclic Dold obstruction for q nontrivial complex
character coordinates. Both the scalar chart construction and the
continuous-to-chain obstruction have proofs. -/
theorem no_equivariant_map (p q N : ℕ) [Fact p.Prime] (hp : p≠2)
    (hq : 0<q) (hDimension : q+q<N)
    (ψ : Fin q→AddChar (ZMod p) ℂ) (hψ : ∀i,ψ i≠0)
    (F : (Fin N→Multiplicative (ZMod p)→ℝ)→Fin q→ℂ)
    (hContinuous : ContinuousOn F (Dvoretzky.GroupJoin _ N))
    (hNonzero : ∀x∈Dvoretzky.GroupJoin _ N,F x≠0)
    (hEquivariant : ∀a : ZMod p,∀x∈Dvoretzky.GroupJoin _ N,
      F (Dvoretzky.joinAct (Multiplicative.ofAdd a) x)=fun i=>ψ i a*F x i) : False := by
  let Φ:=fun x=>joinMap ψ (F x)
  apply dold_join_positive_target p (by omega : 0<q+q) hDimension Φ
  · apply (joinMap_continuousOn ψ).comp hContinuous
    intro x hx
    exact (total_positive p q hp ψ hψ (F x) (hNonzero x hx)).ne'
  · intro x hx
    exact joinMap_mem p q hp ψ hψ (F x) (hNonzero x hx)
  · intro a x hx
    change joinMap ψ (F (Dvoretzky.joinAct a x))=
      Dvoretzky.joinAct a (joinMap ψ (F x))
    have hAction:=hEquivariant a.toAdd x hx
    simp only [ofAdd_toAdd] at hAction
    rw [hAction]
    simpa only [ofAdd_toAdd] using joinMap_character_mul ψ (F x) a.toAdd

end FairDivision.Topology.Volovikov.OddPrimeCharacterJoin
