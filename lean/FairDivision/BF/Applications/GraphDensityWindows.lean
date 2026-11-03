import FairDivision.BF.Applications.GraphDensityBasics
import FairDivision.BF.IdenticalExistence

/-!
# Exact augmented deletions give the paper's density windows

A real deletion uses the induced-degree identity. A dummy deletion keeps
the whole real part; the simple-graph edge bound gives the same window.
Thus the common exact-deletion threshold places every density between t
and t+(s-1)/s, where s is that part's actual real order.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Applications

open FairDivision FairDivision.Topology Recording
open scoped Classical

variable {V:Type*} [Fintype V]

def densityRadius (s:ℕ):ℝ:=((s:ℝ)-1)/s

/-- The whole-real-part value, occurring when an actual dummy is deleted,
lies in the same window as real deletions. -/
theorem modifiedDensity_self_bounds (G:SimpleGraph V) (S:Finset V) (hs:0<S.card):
    graphDensity G S-densityRadius S.card≤ modifiedDensity G S ∧
      modifiedDensity G S≤graphDensity G S:=by
  have hsR:0<(S.card:ℝ):=by exact_mod_cast hs
  have hsOne:(1:ℝ)≤S.card:=by exact_mod_cast (Nat.succ_le_of_lt hs)
  have hE:0≤(inducedEdges G S:ℝ):=Nat.cast_nonneg _
  have hBound:(2:ℝ)*(inducedEdges G S:ℝ)≤(S.card:ℝ)*(S.card-1:ℕ):=by
    exact_mod_cast two_mul_inducedEdges_le G S
  rw [Nat.cast_sub (by omega :1≤S.card),Nat.cast_one] at hBound
  constructor
  · change (inducedEdges G S:ℝ)/S.card-((S.card:ℝ)-1)/S.card≤
      (inducedEdges G S:ℝ)/((S.card:ℝ)+1)
    rw [←sub_div,div_le_div_iff₀ hsR (by linarith)]
    have hProduct:0≤((S.card:ℝ)-1)*((S.card:ℝ)+2):=
      mul_nonneg (sub_nonneg.mpr hsOne) (by linarith)
    nlinarith
  · exact div_le_div_of_nonneg_left hE hsR (by linarith)

/-- Projecting an exact augmented deletion yields either a real deletion
or the unchanged real set, with the deleted real item certified to belong. -/
theorem augmentedDeletion_real_cases {m d:ℕ}
    (B:Finset (Fin (m+d))) (z:Fin (m+d)) (hz:z∈B):
    realPart (B.erase z)=realPart B ∨
      ∃x∈realPart B,realPart (B.erase z)=(realPart B).erase x:=by
  classical
  by_cases hReal:z.val< m
  · right
    let x:Fin m:=⟨z.val,hReal⟩
    have he:realEmbedding m d x=z:=Fin.ext rfl
    refine ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.symm▸hz⟩,?_⟩
    ext y
    have hne:realEmbedding m d y≠z↔y≠x:=by rw [←he];exact (realEmbedding m d).injective.ne_iff
    simp only [Recording.realPart,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_erase,hne]
  · left
    have hne:∀x:Fin m,realEmbedding m d x≠z:=by
      intro x he
      have hv:=congrArg Fin.val he
      change x.val=z.val at hv
      exact hReal (hv▸x.isLt)
    ext x
    simp only [Recording.realPart,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_erase]
    constructor
    ·exact And.right
    ·intro hx
     exact ⟨hne x,hx⟩

/-- Exact augmented deletion, including deleting the one dummy, respects
exactly the manuscript's radius for the actual real part. -/
theorem augmentedDeletion_density_bounds {m d:ℕ} (G:SimpleGraph (Fin m))
    (B:Finset (Fin (m+d))) (hReal:0<(realPart B).card)
    (z:Fin (m+d)) (hz:z∈B):
    graphDensity G (realPart B)-densityRadius (realPart B).card≤
      modifiedDensity G (realPart (B.erase z)) ∧
    modifiedDensity G (realPart (B.erase z))≤graphDensity G (realPart B):=by
  rcases augmentedDeletion_real_cases B z hz with hSame|⟨x,hx,hDelete⟩
  · rw [hSame]
    exact modifiedDensity_self_bounds G (realPart B) hReal
  · rw [hDelete]
    have hErase :
        @Finset.erase (Fin m) (Classical.decEq (Fin m)) (realPart B) x=
          (realPart B).erase x:=by
      ext y
      simp only [Finset.mem_erase]
    simpa only [densityRadius,hErase] using
      modifiedDensity_erase_bounds G (realPart B) x hx

/-- The same threshold bounds every real-part density from below and
bounds it from above by that part's own radius. -/
theorem exactBrackets_density_window {m d:ℕ} (G:SimpleGraph (Fin m))
    (B:Finset (Fin (m+d))) (hReal:0<(realPart B).card) (t:ℝ)
    (hBracket:BracketsOneDeletion (fun C=>modifiedDensity G (realPart C)) B t):
    t≤graphDensity G (realPart B) ∧
      graphDensity G (realPart B)≤t+densityRadius (realPart B).card:=by
  obtain ⟨⟨x,hx,hLow⟩,⟨y,hy,hHigh⟩⟩:=hBracket
  have hX:=augmentedDeletion_density_bounds G B hReal x hx
  have hY:=augmentedDeletion_density_bounds G B hReal y hy
  exact ⟨hHigh.trans hY.2,by linarith [hX.1]⟩

/-- Radius monotonicity is just the paper's (s-1)/s = 1-1/s. -/
theorem densityRadius_mono {r s:ℕ} (hr:0<r) (hrs:r ≤ s):
    densityRadius r≤densityRadius s:=by
  have hrR:0<(r:ℝ):=by exact_mod_cast hr
  have hsR:0<(s:ℝ):=by exact_mod_cast (hr.trans_le hrs)
  have hrsR:(r:ℝ) ≤ s:=by exact_mod_cast hrs
  unfold densityRadius
  rw [div_le_div_iff₀ hrR hsR]
  nlinarith

/-- Full augmented q-item parts have q or q-1 actual real items. -/
theorem realPart_full_or_short {m d q:ℕ} (B:Finset (Fin (m+d)))
    (hFull:B.card=q) (hDummy:(B∩dummyLabels m d).card≤1):
    (realPart B).card=q ∨(realPart B).card=q-1:=by
  rw [card_realPart_eq_sdiff]
  rcases FairDivision.Finite.card_removeDummies_full_or_short
    B (dummyLabels m d) q hFull hDummy with hFullReal|hShortReal
  ·exact Or.inl hFullReal
  ·exact Or.inr (by omega)

/-- Direct extraction of the paper's two possible real sizes and its
size-specific density windows from the SAME augmented allocation. -/
theorem exists_balanced_density_windows
    (k m q d:ℕ) (hk:0<k) (hq:2≤q) (hm:2≤ m)
    (hd:d<k) (hCount:m+d=k*q) (G:SimpleGraph (Fin m)):
    ∃(A:Allocation k m)(t:ℝ),IsBalanced A ∧
      ∀i:Fin k,((bundle A i).card=q ∨(bundle A i).card=q-1) ∧
        t≤graphDensity G (bundle A i) ∧
        graphDensity G (bundle A i)≤t+densityRadius (bundle A i).card:=by
  obtain ⟨B,t,hB⟩:=identical_exists_augmented_commonThreshold k m q d hk hq hm hd hCount
    (modifiedDensity G)
  let A:=actualRealAllocation B
  have hSizes:∀i:Fin k,(bundle A i).card=q ∨(bundle A i).card=q-1:=by
    intro i
    rw [bundle_actualRealAllocation]
    exact realPart_full_or_short (bundle B i) (hB i).1 (hB i).2.2
  have hBalanced:IsBalanced A:=actualRealAllocation_balanced hCount hk (by omega) hd B
    (fun i=>⟨(hB i).1,(hB i).2.2⟩)
  refine ⟨A,t,hBalanced,?_⟩
  intro i
  have hPos:0<(realPart (bundle B i)).card:=by
    have h:=hSizes i
    rw [bundle_actualRealAllocation] at h
    omega
  refine ⟨hSizes i,?_⟩
  have hBundle : bundle A i=realPart (bundle B i):=
    bundle_actualRealAllocation B i
  rw [hBundle]
  exact exactBrackets_density_window G (bundle B i) hPos t (hB i).2.1

end FairDivision.BF.Applications
