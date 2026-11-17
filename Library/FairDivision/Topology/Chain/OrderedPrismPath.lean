import FairDivision.Topology.Chain.OrderedPrismNaturality
import Mathlib.Algebra.BigOperators.Fin

/-!
# The actual finite sum of adjacent ordered prisms

No triangulation of a product is assumed: the recursive ordered prism already
writes its staircase simplices. Summing along a finite time grid telescopes
the endpoint chain maps, preserves equivariance, and raises list degree once.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Chain

open Dvoretzky.Dold
open scoped BigOperators

variable {R E F : Type*} [CommRing R] {K : ℕ}

def prismPath (sel : Fin (K+1)→E→F) :
    Dvoretzky.Dold.Chain R E→ₗ[R]Dvoretzky.Dold.Chain R F :=
  ∑j : Fin K,prism (sel j.castSucc) (sel j.succ)

/-- The finite telescoping identity in precisely the time-grid indexing used
by the actual source selection. -/
theorem sum_fin_adjacent_sub {A : Type*} [AddCommGroup A] (f : Fin (K+1)→A) :
    (∑j : Fin K, (f j.succ-f j.castSucc))=f (Fin.last K)-f 0 := by
  rw [Finset.sum_sub_distrib]
  apply sub_eq_iff_eq_add.mpr
  calc
    ∑j : Fin K,f j.succ=(f 0+∑j : Fin K,f j.succ)-f 0 := by abel
    _=((∑j : Fin K,f j.castSucc)+f (Fin.last K))-f 0 := by
      rw [←Fin.sum_univ_succ,Fin.sum_univ_castSucc]
    _=(f (Fin.last K)-f 0)+∑j : Fin K,f j.castSucc := by abel

/-- Literal endpoint-minus-start chain homotopy for the finite prism sum. -/
theorem bd_prismPath (sel : Fin (K+1)→E→F) (c : Dvoretzky.Dold.Chain R E) :
    bd (prismPath sel c)+prismPath sel (bd c)=
      actL (sel (Fin.last K)) c-actL (sel 0) c := by
  change bd ((∑j : Fin K,prism (sel j.castSucc) (sel j.succ)) c)+
    (∑j : Fin K,prism (sel j.castSucc) (sel j.succ)) (bd c)=_
  simp only [LinearMap.sum_apply,map_sum]
  rw [←Finset.sum_add_distrib]
  simp_rw [bd_prism]
  exact sum_fin_adjacent_sub (fun j=>actL (sel j) c)

theorem prismPath_naturality_on_supported (a : E→E) (b : F→F)
    (sel : Fin (K+1)→E→F) {S : Set E}
    (heq : ∀j x,x∈S→sel j (a x)=b (sel j x))
    {c : Dvoretzky.Dold.Chain R E}
    (hc : c∈Finsupp.supported R R {l : List E|∀x∈l,x∈S}) :
    prismPath sel (actL a c)=actL b (prismPath sel c) := by
  simp only [prismPath,LinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact prism_naturality_on_supported a b _ _ (heq j.castSucc) (heq j.succ) hc

theorem prismPath_supported_length (sel : Fin (K+1)→E→F) (q : ℕ)
    {c : Dvoretzky.Dold.Chain R E}
    (hc : c∈Finsupp.supported R R {l : List E|l.length=q}) :
    prismPath sel c∈Finsupp.supported R R {w : List F|w.length=q+1} := by
  simp only [prismPath,LinearMap.sum_apply]
  exact Submodule.sum_mem _ (fun j _=>prism_supported_length _ _ q hc)

end FairDivision.Topology.Chain
