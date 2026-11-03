import FairDivision.BF.HeterogeneousExchangePath
import FairDivision.Finite.BundleExchangeChain
import FairDivision.Topology.UniformPathConcatenation

/-!
# BF Section 5: paths between arbitrary equal-size bundles

For an edge of the simplex of bundle lotteries, its endpoint bundles need
not differ by one item. The manuscript exchanges their differing items one
at a time, never leaving their union. This module retains that exact exchange sequence, concatenates its paths on
equal intervals, and reuses their admissibility certificates.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- The same complete finite chain is shared by Section 3 threshold
selection and the Section 5 vector-valued equal-subdivision paths. -/
abbrev BundleExchangeChain {m : ℕ} (q : ℕ) (E F T : Finset (Fin m)) :=
  FairDivision.Finite.BundleExchangeChain (q - 1) q E F T

namespace BundleExchangeChain

/-- Compatibility wrapper retaining the earlier BF constructor API. -/
def refl {m q : ℕ} (E F : Finset (Fin m))
    (hF : F.card = q - 1) (hFE : F ⊆ E) : BundleExchangeChain q E F F :=
  FairDivision.Finite.BundleExchangeChain.refl E F hF hFE

/-- Prepend the same first exchange; the shared construction has the same
bundle sequence, length and stock certificates. -/
def prepend {m q : ℕ} {E F U T : Finset (Fin m)}
    (chain : BundleExchangeChain q E U T)
    (hF : F.card = q - 1) (hFE : F ⊆ E)
    (hFU : (F ∪ U).card = q) : BundleExchangeChain q E F T :=
  FairDivision.Finite.BundleExchangeChain.prepend chain hF hFE hFU

end BundleExchangeChain

/-- Choose the entire manuscript exchange sequence independently of scores;
its exact length is the number of items to replace. -/
theorem exists_bundle_exchange_chain
    {m q : ℕ} (E F T : Finset (Fin m))
    (hq : 1 ≤ q)
    (hF : F.card = q - 1) (hT : T.card = q - 1)
    (hFE : F ⊆ E) (hTE : T ⊆ E) :
    ∃ chain : BundleExchangeChain q E F T, chain.length = (F \ T).card := by
  exact FairDivision.Finite.exists_bundle_exchange_chain E F T
    (show q = q - 1 + 1 by omega) hF hT hFE hTE


/-- The same exchange sequence, now run on equal first-subdivision intervals.
Its local two/four-piece paths and all witnesses are the existing manuscript
ones. Both subdivisions are shared by the entire valuation vector. -/
theorem exists_admissible_bundle_path
    {n m q : ℕ} (dummy : Fin m)
    (v : Fin n → Finset (Fin m) → ℝ)
    (E F T : Finset (Fin m))
    (hq : 1 ≤ q)
    (hF : F.card = q - 1) (hT : T.card = q - 1)
    (hFE : F ⊆ E) (hTE : T ⊆ E) :
    ∃ γ : Path (fun j => v j F) (fun j => v j T),
      ∀ t, IsAdmissible q dummy v E (γ t) := by
  classical
  obtain ⟨chain, hlength⟩ := exists_bundle_exchange_chain E F T hq hF hT hFE hTE
  by_cases hzero : chain.length = 0
  · have heq : F = T := by
      have hi : (0 : Fin (chain.length + 1)) = Fin.last chain.length :=
        Fin.ext (by simp [hzero])
      exact chain.first.symm.trans ((congrArg chain.bundle hi).trans chain.last)
    subst T
    exact ⟨Path.refl _, fun _ => isAdmissible_vertex v E F hq hF hFE⟩
  · let point : Fin (chain.length + 1) → Fin n → ℝ :=
      fun r j => v j (chain.bundle r)
    let segment : ∀ k : Fin chain.length, Path (point k.castSucc) (point k.succ) :=
      fun k => manuscriptExchangePath dummy v (chain.bundle k.castSucc) (chain.bundle k.succ)
    let path := FairDivision.Topology.uniformPath (Nat.pos_of_ne_zero hzero) point segment
    have hadm : ∀ t, IsAdmissible q dummy v E (path t) :=
      FairDivision.Topology.uniformPath_property (Nat.pos_of_ne_zero hzero) point segment
        (IsAdmissible q dummy v E) (fun k =>
          manuscriptExchangePath_admissible dummy v E
            (chain.bundle k.castSucc) (chain.bundle k.succ) hq
            (chain.card _) (chain.card _) (chain.exchange k)
            (chain.in_stock _) (chain.in_stock _))
    let result : Path (fun j => v j F) (fun j => v j T) := {
      toContinuousMap := path.toContinuousMap
      source' := by simpa [point, chain.first] using path.source
      target' := by simpa [point, chain.last] using path.target }
    exact ⟨result, hadm⟩

end FairDivision.BF
