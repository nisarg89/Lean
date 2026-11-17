import FairDivision.Definitions

/-!
# Statement definitions for BF Section 7

These are arbitrary BUNDLE valuations, as in BF. The shared FE IsSwapEF
predicate is additive and permits one item per direction; it does not
state the more general t-swap theorem here. Human statement review covers
these definitions and the final sharp-threshold theorem statements.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- Every bundle has exactly the prescribed cardinality q. -/
def HasEqualBundleSize {n m : ℕ} (A : Allocation n m) (q : ℕ) : Prop :=
  ∀i : Fin n,(bundle A i).card=q

/-- BF's t-swap guarantee compares BOTH resulting bundles under the
envious agent's valuation. A genuine swap uses equally many, at least
one and at most t, items in the two directions. -/
def IsTSwapEF {n m : ℕ} (t : ℕ) (v : Fin n→Finset (Fin m)→ℝ)
    (A : Allocation n m) : Prop :=
  ∀i j : Fin n,v i (bundle A i)<v i (bundle A j)→
    ∃X Y : Finset (Fin m),X⊆bundle A i ∧Y⊆bundle A j ∧
      1≤X.card ∧X.card=Y.card ∧X.card≤t ∧
      v i ((bundle A j\Y)∪X)≤v i ((bundle A i\X)∪Y)

/-- EFX for arbitrary bundle valuations: removing ANY actual item from
the envied bundle makes its value at most the agent's unchanged value. -/
def IsBundleEFX {n m : ℕ} (v : Fin n→Finset (Fin m)→ℝ)
    (A : Allocation n m) : Prop :=
  ∀i j : Fin n,∀g∈bundle A j,v i ((bundle A j).erase g)≤v i (bundle A i)

/-- The normalized property in the Section 7 negative example. -/
def IsNormalized {m : ℕ} (v : Finset (Fin m)→ℝ) : Prop :=v ∅=0

/-- The finite-set submodular inequality, with no additivity hypothesis. -/
def IsBundleSubmodular {m : ℕ} (v : Finset (Fin m)→ℝ) : Prop :=
  ∀S T,v (S∪T)+v (S∩T)≤v S+v T

end FairDivision.BF
