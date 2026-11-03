import FairDivision.Topology.UnlabeledActionLaws
import FairDivision.Topology.Volovikov.PositionAction
import FairDivision.Topology.Volovikov.InvariantComplexAction

/-! The already proved position relabelings, now packaged as actual source
homeomorphisms for the external equivariant transfer theorem. Dummy items
remain unlabeled throughout: this uses exactly the prior auxiliaryRelabel
map and its prior inverse/composition/continuity proofs. -/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Any position permutation acts by a homeomorphism of the corrected
unlabeled-dummy lottery space. -/
noncomputable def auxiliaryRelabelHomeomorph {k m r c : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k)) :
    unlabeledLotterySpace k m r c D ≃ₜ unlabeledLotterySpace k m r c D where
  toFun:=auxiliaryRelabel σ
  invFun:=auxiliaryRelabel σ.symm
  left_inv:=by
    intro x
    change auxiliaryRelabel (σ⁻¹) (auxiliaryRelabel σ x)=x
    rw [←auxiliaryRelabel_mul,inv_mul_cancel,auxiliaryRelabel_one]
  right_inv:=by
    intro x
    change auxiliaryRelabel σ (auxiliaryRelabel (σ⁻¹) x)=x
    rw [←auxiliaryRelabel_mul,mul_inv_cancel,auxiliaryRelabel_one]
  continuous_toFun:=auxiliaryRelabel_continuous σ
  continuous_invFun:=auxiliaryRelabel_continuous σ.symm

@[simp] theorem auxiliaryRelabelHomeomorph_apply {k m r c : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k))
    (x : unlabeledLotterySpace k m r c D) :
    auxiliaryRelabelHomeomorph σ x=auxiliaryRelabel σ x:=rfl

/-- The regular p-torus position action, using the existing corrected
auxiliary source and the existing pTorusPositionPerm definition. -/
noncomputable def pTorusAuxiliaryAction (p rank m r c : ℕ) [NeZero p]
    (D : Finset (Fin m)) (g : Fin rank → ZMod p) :
    unlabeledLotterySpace (p^rank) m r c D ≃ₜ
      unlabeledLotterySpace (p^rank) m r c D :=
  auxiliaryRelabelHomeomorph (pTorusPositionPerm p rank g)

/-- The source homeomorphisms satisfy precisely the action laws required
by the existing universal-join transfer, with no new connectivity premise. -/
theorem pTorusAuxiliaryAction_action (p rank m r c : ℕ) [NeZero p]
    (D : Finset (Fin m)) :
    Volovikov.IsContinuousAddAction (pTorusAuxiliaryAction p rank m r c D):=by
  constructor
  ·intro x
   change auxiliaryRelabel (pTorusPositionPerm p rank 0) x=x
   rw [show pTorusPositionPerm p rank 0=1 from
     Volovikov.regularPositionPerm_zero (pTorusPositionEquiv p rank)]
   exact auxiliaryRelabel_one x
  ·intro a b x
   change auxiliaryRelabel (pTorusPositionPerm p rank (a+b)) x=
     auxiliaryRelabel (pTorusPositionPerm p rank a)
       (auxiliaryRelabel (pTorusPositionPerm p rank b) x)
   rw [Volovikov.pTorusPositionPerm_add,auxiliaryRelabel_mul]

end FairDivision.Topology
