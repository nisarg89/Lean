import EF1FPO.Model
import OAI.Optimization.LinearProgramming.OracleSpec.PriceEncoding

/-! Parseable binary input and output and a fixed, closed finite-stack machine contract. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.Optimization.LinearProgramming.OracleSpec

/-- All natural fields and rational components use the upstream framed binary encoding.
Both sets of indices are explicitly listed, including when the table has no columns. -/
def encodeInstance (I : Instance) : Word :=
  encodeNat I.n ++ encodeNat I.m ++
    (List.ofFn (fun i : I.Agent => i.val)).flatMap encodeNat ++
    (List.ofFn (fun g : I.Good => g.val)).flatMap encodeNat ++
    (List.ofFn (fun i : I.Agent => List.ofFn (I.v i))).flatten.flatMap encodeRat

def encodeAllocation {I : Instance} (A : I.Allocation) : Word :=
  encodeNat I.n ++ encodeNat I.m ++ (List.ofFn (fun g : I.Good => (A g).val)).flatMap encodeNat

/-- A closed execution accepts no external information. Every `ask` would create a
permanent transcript entry and violate the empty-transcript postcondition. -/
def ClosedComputesWithin (M : BitProgram) (input : Word) (time : ℕ)
    (post : Word → Prop) : Prop :=
  M.ComputesWithin (fun _ _ => []) input time (fun history output => history = [] ∧ post output)

/-- Program and clock are quantified before inputs. The cost is ordinary binary bit time. -/
def BitPolynomial {X : Type} (input : X → Word) (post : X → Word → Prop) : Prop :=
  ∃ (M : BitProgram) (C d : ℕ), ∀ x : X,
    ClosedComputesWithin M (input x) (C * ((input x).length + 1) ^ d) (post x)

/-- Size, height, and log radius from the computation section of the manuscript. -/
def valuationBits (I : Instance) : ℕ := max 4 (max (I.n + I.m) (encodeInstance I).length)

def weightBits (I : Instance) : ℕ := 16 * (I.n + I.m + 1) * (valuationBits I + 1)

def logRadius (I : Instance) : ℕ := 4 * (valuationBits I + 1)

theorem encodeInstance_injective : Function.Injective encodeInstance := by
  have rows {n m : ℕ} (v : Fin n → Fin m → ℚ) :
      (List.ofFn (fun i : Fin n => List.ofFn (v i))).flatten =
        List.ofFn (fun p : Fin (n * m) => v (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) := by
    conv_rhs => rw [List.ofFn_mul]
    congr 1
    apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext g
    have decode (p : Fin (n * m)) (h : p.val = g.val + m * i.val) :
        finProdFinEquiv.symm p = (i, g) := by
      apply finProdFinEquiv.injective
      rw [Equiv.apply_symm_apply]
      exact Fin.ext h
    rw [decode _ (by change i.val * m + g.val = g.val + m * i.val; ac_rfl)]
  rintro ⟨n, m, hn, v, hNonneg⟩ ⟨n', m', hn', v', hNonneg'⟩ h
  simp only [encodeInstance, List.append_assoc] at h
  obtain ⟨rfl, h⟩ := (encodeNat_prefix _ _ _ _).mp h
  obtain ⟨rfl, h⟩ := (encodeNat_prefix _ _ _ _).mp h
  have hPacked := List.append_cancel_left (List.append_cancel_left h)
  rw [rows, rows] at hPacked
  let flat (a : Fin n → Fin m → ℚ) (p : Fin (n * m)) :=
    a (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  have hLists := ((encodeRats_prefix (List.ofFn (flat v)) (List.ofFn (flat v'))
    (by simp only [List.length_ofFn]) [] []).mp (by simpa only [List.append_nil, flat] using hPacked)).1
  have hCells := List.ofFn_injective hLists
  have hV : v = v' := by
    funext i g
    simpa only [flat, Equiv.symm_apply_apply] using congrFun hCells (finProdFinEquiv (i, g))
  subst v'
  rfl

theorem encodeAllocation_injective (I : Instance) :
    Function.Injective (encodeAllocation (I := I)) := by
  have prefixed : ∀ xs ys : List ℕ, xs.flatMap encodeNat = ys.flatMap encodeNat → xs = ys := by
    intro xs
    induction xs with
    | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons b ys =>
        have hLen := congrArg List.length h
        simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil, List.length_append,
          encodeNat_length] at hLen
        omega
    | cons a xs ih =>
      intro ys h
      cases ys with
      | nil =>
        have hLen := congrArg List.length h
        simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil, List.length_append,
          encodeNat_length] at hLen
        omega
      | cons b ys =>
        obtain ⟨rfl, hTail⟩ := (encodeNat_prefix _ _ _ _).mp h
        rw [ih ys hTail]
  intro A B h
  unfold encodeAllocation at h
  have hOwners := List.ofFn_injective (prefixed _ _ (List.append_cancel_left h))
  funext g
  exact Fin.ext (congrFun hOwners g)

theorem dimensions_le_binarySize (I : Instance) : I.n + I.m ≤ (encodeInstance I).length := by
  have indices_le_length : ∀ indices : List ℕ, indices.length ≤ (indices.flatMap encodeNat).length := by
    intro indices
    induction indices with
    | nil => simp
    | cons i rest ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append, encodeNat_length]
      omega
  have agents := indices_le_length (List.ofFn (fun i : I.Agent => i.val))
  have goods := indices_le_length (List.ofFn (fun g : I.Good => g.val))
  simp only [List.length_ofFn] at agents goods
  simp only [encodeInstance, List.length_append]
  omega

end EF1FPO
