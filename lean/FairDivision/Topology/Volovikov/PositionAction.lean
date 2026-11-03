import FairDivision.Topology.Volovikov.ContinuousAction

/-!
# Translation action laws

The p-torus translations compose as an additive group action on the labeled
positions. The resulting coordinate action on the reduced sphere is
continuous and has no common fixed point.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

/-- Transported zero translation is the identity position permutation. -/
theorem regularPositionPerm_zero {n : ℕ} {G : Type*}
    [AddCommGroup G] (e : Fin n ≃ G) :
    regularPositionPerm e 0 = 1 := by
  ext i
  simp [regularPositionPerm_apply]

/-- Transported translations compose according to addition. -/
theorem regularPositionPerm_add {n : ℕ} {G : Type*}
    [AddCommGroup G] (e : Fin n ≃ G) (g h : G) :
    regularPositionPerm e (g + h) =
      regularPositionPerm e g * regularPositionPerm e h := by
  apply Equiv.ext
  intro i
  apply e.injective
  simp [regularPositionPerm_apply, Equiv.Perm.mul_apply, add_assoc]

/-- The p-torus position permutations form an additive action. -/
theorem pTorusPositionPerm_add (p r : ℕ) [NeZero p]
    (g h : Fin r → ZMod p) :
    pTorusPositionPerm p r (g + h) =
      pTorusPositionPerm p r g * pTorusPositionPerm p r h :=
  regularPositionPerm_add (pTorusPositionEquiv p r) g h


/-- Coordinate relabeling respects composition of position permutations. -/
theorem relabelReducedSphere_mul {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (z : ReducedSphere n) :
    relabelReducedSphere (σ * τ) z =
      relabelReducedSphere σ (relabelReducedSphere τ z) := by
  apply Subtype.ext
  funext i
  rfl

/-- The p-torus acts on the reduced sphere by coordinate relabeling. -/
theorem pTorusSphere_add (p r : ℕ) [NeZero p]
    (g h : Fin r → ZMod p) (z : ReducedSphere (p ^ r)) :
    relabelReducedSphere (pTorusPositionPerm p r (g + h)) z =
      relabelReducedSphere (pTorusPositionPerm p r g)
        (relabelReducedSphere (pTorusPositionPerm p r h) z) := by
  rw [pTorusPositionPerm_add, relabelReducedSphere_mul]

/-- Zero translation fixes every point of the reduced sphere. -/
theorem pTorusSphere_zero (p r : ℕ) [NeZero p]
    (z : ReducedSphere (p ^ r)) :
    relabelReducedSphere (pTorusPositionPerm p r 0) z = z := by
  rw [show pTorusPositionPerm p r 0 = 1 from
    regularPositionPerm_zero (pTorusPositionEquiv p r)]
  apply Subtype.ext
  funext i
  rfl

/-- Translation by a p-torus element acts continuously on the reduced sphere. -/
theorem pTorusSphere_continuous (p r : ℕ) [NeZero p]
    (g : Fin r → ZMod p) :
    Continuous (relabelReducedSphere (pTorusPositionPerm p r g) :
      ReducedSphere (p ^ r) → ReducedSphere (p ^ r)) :=
  relabelReducedSphere_continuous _

end FairDivision.Topology.Volovikov
