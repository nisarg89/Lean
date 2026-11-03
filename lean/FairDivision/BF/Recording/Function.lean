import FairDivision.BF.Recording.Leaf
import FairDivision.Topology.Recording.SupportedItemRelabel

/-!
# Exact recording-function interface and the actual leaf recorder

The domain is the literal finite graph times the common closed value
interval. A zero certifies an equitable compatible lottery in the exact
positive-support available pool. The relabeling theorem below realizes the
same certificate with arbitrary imposed labels on that pool, including when
fewer actual dummies are present than the unused formal dummy inventory.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace FairDivision.BF.Recording

open FairDivision.Topology

/-- Exactly the equitable compatible lottery required at a zero. -/
def Certifies {a q m:ℕ} (v:Finset (Fin m)→ℝ) (b:Space a q m) (t:ℝ):Prop:=
  ∃μ:stdSimplex ℝ (PartialVertex a (dummyLabels m a) (q-1) 1),
    μ∈compatibleLotterySpace a (m+a) (q-1) 1 (dummyLabels m a) ∧
    (∀i:Fin a,pool (lotterySupport μ) i⊆available b) ∧
    ∀i:Fin a,(∑X:PartialVertex a (dummyLabels m a) (q-1) 1,
      μ.1 X*v (realPart (partialBundle X.1 i)))=t

/-- The lower endpoint of the manuscript's fixed value interval. -/
def lowerTarget {L H:ℝ} (hLH:L≤H):Set.Icc L H:=⟨L,le_rfl,hLH⟩

/-- The upper endpoint of that SAME fixed interval. -/
def upperTarget {L H:ℝ} (hLH:L≤H):Set.Icc L H:=⟨H,hLH,le_rfl⟩

/-- The manuscript's recording function, before any prime multiplication
step. Its only certificate clause is the actual equitable compatible
lottery, with the precise available-pool inclusion. -/
structure RecordingFunction (a q m:ℕ) (v:Finset (Fin m)→ℝ)
    (L H:ℝ) (hLH:L≤H) where
  phi:C(Space a q m×Set.Icc L H,ℝ)
  negative:∀b:Space a q m,phi (b,lowerTarget hLH)<0
  positive:∀b:Space a q m,0<phi (b,upperTarget hLH)
  realizes:∀b:Space a q m,∀t:Set.Icc L H,phi (b,t)=0→Certifies v b t.val

/-- Realize a recording zero with any injective actual labeling of its
available items. Unused formal dummy labels need not be injected. The
valuation equality is the defining condition that only labels changed. -/
theorem Certifies.relabel {a q m N:ℕ} {v:Finset (Fin m)→ℝ}
    {b:Space a q m} {t:ℝ} (h:Certifies v b t)
    (D:Finset (Fin N)) (e:Fin (m+a)→Fin N)
    (hInject:Set.InjOn e (available b:Set (Fin (m+a))))
    (hDummy:∀g∈available b,e g∈D↔g∈dummyLabels m a)
    (w:Finset (Fin N)→ℝ)
    (hValue:∀B:Finset (Fin (m+a)),B⊆available b→w (B.image e)=v (realPart B)):
    ∃μ:stdSimplex ℝ (PartialVertex a D (q-1) 1),
      μ∈compatibleLotterySpace a N (q-1) 1 D ∧
      (∀i:Fin a,pool (lotterySupport μ) i⊆(available b).image e) ∧
      ∀i:Fin a,(∑X:PartialVertex a D (q-1) 1,μ.1 X*w (partialBundle X.1 i))=t:=by
  obtain ⟨μ,hCompatible,hPool,hEquitable⟩:=h
  obtain ⟨ν,hν,hνPool,hνValue⟩:=FairDivision.Topology.Recording.exists_supported_item_relabel
    μ hCompatible (available b) hPool e hInject hDummy
    (fun B=>v (realPart B)) w (by
      intro X hX i
      exact hValue (partialBundle X.1 i)
        ((partialBundle_subset_pool hX i).trans (hPool i)))
  refine ⟨ν,hν,hνPool,?_⟩
  intro i
  exact (hνValue i).trans (hEquitable i)

/-- Literal Phi₁=t−expected-v on the graph times the fixed interval. -/
def leafRecordingFunction {q m:ℕ} (v:Finset (Fin m)→ℝ)
    (L H:ℝ) (hLH:L≤H)
    (hL:∀A:Finset (Fin m),L<v A) (hH:∀A:Finset (Fin m),v A<H):
    RecordingFunction 1 q m v L H hLH where
  phi:={
    toFun:=fun z=>leafPhi v (z.1,z.2.val)
    continuous_toFun:=(continuous_leafPhi v).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)) }
  negative:=fun b=>leafPhi_lower v L hL b
  positive:=fun b=>leafPhi_upper v H hH b
  realizes:=fun b t hZero=>leafPhi_zero_realizes v b t.val hZero

/-- The leaf base of the manuscript recursion is an actual construction,
with all continuity, signs, available-pool and lottery obligations proved. -/
theorem exists_leaf_recordingFunction {q m:ℕ} (v:Finset (Fin m)→ℝ)
    (L H:ℝ) (hLH:L≤H)
    (hL:∀A:Finset (Fin m),L<v A) (hH:∀A:Finset (Fin m),v A<H):
    Nonempty (RecordingFunction 1 q m v L H hLH):=
  ⟨leafRecordingFunction v L H hLH hL hH⟩

end FairDivision.BF.Recording
