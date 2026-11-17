import FairDivision.Topology.Volovikov.OddPrimeCharacterJoin
import FairDivision.Topology.Volovikov.ShiftedCyclicJoinObstruction
import FairDivision.Topology.Volovikov.ElementaryAbelianCharacters

/-!
# The two-color character-circle chart for general elementary-abelian actions

Reuse the actual cyclic chart pointwise, now allowing each coordinate to
receive a DIFFERENT label shift from a genuine source generator. The
common scalar character ψ is the canonical character indexed by 1. The
coefficient-vector parametrization already in the project identifies each
generator scalar exactly; no cohomological character interpretation is
needed for this adapter.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Volovikov.OddPrimeElementaryCharacterJoin

open scoped BigOperators
open Dvoretzky
open OddPrimeCharacterJoin
open OddPrimeTensorSource (Group generator)
open ShiftedCyclicApproximation (pointShift)

variable {p q r N : ℕ} [Fact p.Prime]

/-- One fixed faithful cyclic character, shared by all coordinate charts. -/
def baseCharacter (p : ℕ) [NeZero p] : AddChar (ZMod p) ℂ :=AddChar.zmodAddEquiv 1

theorem baseCharacter_nontrivial (p : ℕ) [Fact p.Prime] : baseCharacter p≠0 := by
  intro h
  have hZero : (AddChar.zmodAddEquiv : ZMod p≃+AddChar (ZMod p) ℂ) 0=0:=map_zero _
  exact one_ne_zero ((AddChar.zmodAddEquiv : ZMod p≃+AddChar (ZMod p) ℂ).injective
    (h.trans hZero.symm))

/-- The canonical pairing is multiplication in Z/p before the circle
exponential. This records its symmetry with 1 explicitly. -/
theorem canonical_character_at_one (a : ZMod p) :
    (AddChar.zmodAddEquiv a) (1 : ZMod p)=baseCharacter p a := by
  simp only [baseCharacter,AddChar.zmodAddEquiv_apply]
  change (↑((AddChar.zmod p a) (1 : ZMod p)) : ℂ)=
    (↑((AddChar.zmod p (1 : ZMod p)) a) : ℂ)
  congr 1
  simp only [AddChar.zmod,AddChar.compAddMonoidHom_apply,AddChar.coe_mk,
    AddMonoidHom.comp_apply,AddMonoidHom.coe_mulLeft,mul_one,one_mul]
  rfl

/-- Different character coordinates may shift by different amounts. -/
theorem total_coordinatewise_mul
    (ψ : Fin q→AddChar (ZMod p) ℂ) (z : Fin q→ℂ) (a : Fin q→ZMod p) :
    total ψ (fun i=>ψ i (a i)*z i)=total ψ z := by
  classical
  unfold total
  apply Finset.sum_congr rfl
  intro c hc
  simp only [weight_character_mul]
  exact Fintype.sum_equiv (Equiv.addRight (a c.1)) _ _ (fun g=>rfl)

theorem joinMap_coordinatewise_mul
    (ψ : Fin q→AddChar (ZMod p) ℂ) (z : Fin q→ℂ) (a : Fin q→ZMod p) :
    OddPrimeCharacterJoin.joinMap ψ (fun i=>ψ i (a i)*z i)=
      pointShift (fun j=>a ((colorEquiv q).symm j).1) (OddPrimeCharacterJoin.joinMap ψ z) := by
  funext j g
  simp [OddPrimeCharacterJoin.joinMap,pointShift,weight_character_mul,total_coordinatewise_mul]

/-- The concrete general-rank character-circle obstruction. Its proof
supplies the target join map itself and all of its generic chain inputs. -/
theorem no_equivariant_map (p r q N : ℕ) [Fact p.Prime] (hp : p≠2)
    (hq : 0<q) (hDimension : q+q<N)
    (a : Fin q→Fin r→ZMod p) (hNontrivial : ∀i,a i≠0)
    (F : (Fin N→Group p r→ℝ)→Fin q→ℂ)
    (hContinuous : ContinuousOn F (GroupJoin (Group p r) N))
    (hNonzero : ∀x∈GroupJoin (Group p r) N,F x≠0)
    (hEquivariant : ∀k : Fin r,∀x∈GroupJoin (Group p r) N,
      F (joinAct (generator (p:=p) k) x)=fun i=>baseCharacter p (a i k)*F x i) : False := by
  classical
  let ψ : Fin q→AddChar (ZMod p) ℂ:=fun _=>baseCharacter p
  let ε : Fin r→Fin (q+q)→ZMod p:=fun k j=>a ((colorEquiv q).symm j).1 k
  let Φ:=fun x=>OddPrimeCharacterJoin.joinMap ψ (F x)
  refine ShiftedCyclicJoinObstruction.no_twisted_join_map_positive p r
    (by omega : 0<q+q) hDimension ε ?_ Φ ?_ ?_ ?_
  · intro j
    by_contra h
    push_neg at h
    apply hNontrivial ((colorEquiv q).symm j).1
    exact funext h
  · apply (joinMap_continuousOn ψ).comp hContinuous
    intro x hx
    exact (total_positive p q hp ψ (fun _=>baseCharacter_nontrivial p)
      (F x) (hNonzero x hx)).ne'
  · intro x hx
    exact joinMap_mem p q hp ψ (fun _=>baseCharacter_nontrivial p) (F x) (hNonzero x hx)
  · intro k x hx
    change OddPrimeCharacterJoin.joinMap ψ (F (joinAct (generator (p:=p) k) x))=_
    rw [hEquivariant k x hx]
    exact joinMap_coordinatewise_mul ψ (F x) (fun i=>a i k)

end FairDivision.Topology.Volovikov.OddPrimeElementaryCharacterJoin
