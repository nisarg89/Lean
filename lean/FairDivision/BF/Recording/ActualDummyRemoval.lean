import FairDivision.BF.Recording.RealItemCoordinates
import FairDivision.Finite.DummyRemovalArithmetic
import FairDivision.Finite.Replacement

/-!
# Delete the actual canonical dummy labels without re-enumerating real items

The final augmented allocation already uses the literal real prefix Fin m
inside Fin (m+d). Restrict its owner function along that exact embedding.
The existing finite dummy-removal arithmetic proves balance. An exact
augmented deletion projects to an optional real deletion through `realPart`;
its value is unchanged. This is the manuscript deletion argument in the
actual coordinates, with no arbitrary real-item enumeration or new proof
strategy.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Recording

open FairDivision

/-- Restriction of the actual augmented owner map to the original real labels. -/
def actualRealAllocation {n m d : ℕ} (A : Allocation n (m+d)) : Allocation n m :=
  fun g=>A (realEmbedding m d g)

@[simp] theorem bundle_actualRealAllocation {n m d : ℕ}
    (A : Allocation n (m+d)) (i : Fin n) :
    bundle (actualRealAllocation A) i=realPart (bundle A i) := by
  classical
  apply Finset.ext
  intro g
  constructor
  · intro hg
    have hOwner : A (realEmbedding m d g)=i :=
      (Finset.mem_filter.mp hg).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hOwner⟩⟩
  · intro hg
    have hBundle : realEmbedding m d g ∈ bundle A i :=
      (Finset.mem_filter.mp hg).2
    have hOwner : A (realEmbedding m d g)=i :=
      (Finset.mem_filter.mp hBundle).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hOwner⟩

/-- Canonical real projection commutes with every deletion set, including
a deletion consisting solely of a dummy label. -/
theorem realPart_sdiff {m d : ℕ} (B E : Finset (Fin (m+d))) :
    realPart (B\E)=realPart B\realPart E := by
  classical
  ext g
  simp only [realPart,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]

theorem realPart_mono {m d : ℕ} {B C : Finset (Fin (m+d))} (hBC : B⊆C) :
    realPart B⊆realPart C := by
  classical
  intro g hg
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hBC (Finset.mem_filter.mp hg).2⟩

/-- Projecting an exact augmented singleton can delete zero or one real item. -/
theorem realPart_card_le_one {m d : ℕ} {E : Finset (Fin (m+d))} (hE : E.card≤1) :
    (realPart E).card≤1 := by
  classical
  apply Finset.card_le_one.mpr
  intro g hg h hh
  apply (realEmbedding m d).injective
  exact (Finset.card_le_one.mp hE) _ (Finset.mem_filter.mp hg).2 _
    (Finset.mem_filter.mp hh).2

theorem realEmbedding_not_dummy (m d : ℕ) (g : Fin m) :
    realEmbedding m d g∉dummyLabels m d := by
  intro hg
  have hge:=(mem_dummyLabels_iff (realEmbedding m d g)).mp hg
  change m≤g.val at hge
  exact (not_le_of_gt g.isLt) hge

/-- Deleting an actual real singleton deletes that same original item. -/
@[simp] theorem realPart_singleton_real {m d : ℕ} (g : Fin m) :
    realPart ({realEmbedding m d g} : Finset (Fin (m+d)))={g} := by
  simpa only [Finset.map_singleton] using
    (realPart_realMap (a:=d) ({g} : Finset (Fin m)))

/-- Deleting an actual dummy singleton deletes no real item, regardless of
which of the labeled dummy coordinates was selected by the bracket witness.
-/
theorem realPart_singleton_dummy {m d : ℕ} (z : Fin (m+d))
    (hz : z∈dummyLabels m d) : realPart ({z} : Finset (Fin (m+d)))=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have hEq : realEmbedding m d g=z :=
    Finset.mem_singleton.mp (Finset.mem_filter.mp hg).2
  apply realEmbedding_not_dummy m d g
  rw [hEq]
  exact hz

/-- The zero-dummy endpoint is the literal original owner function. -/
@[simp] theorem actualRealAllocation_no_dummy {n m : ℕ}
    (A : Allocation n (m+0)) : actualRealAllocation A=A := by
  funext g
  apply congrArg A
  apply Fin.ext
  rfl

@[simp] theorem realPart_sdiff_dummy {m d : ℕ} (B : Finset (Fin (m+d))) :
    realPart (B\dummyLabels m d)=realPart B := by
  classical
  ext g
  simp only [realPart,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]
  constructor
  · exact And.left
  · intro hg
    exact ⟨hg,realEmbedding_not_dummy m d g⟩

/-- The cardinality comparison uses the original labels themselves. -/
theorem realMap_realPart_eq_sdiff {m d : ℕ} (B : Finset (Fin (m+d))) :
    (realPart B).map (realEmbedding m d)=B\dummyLabels m d := by
  have hDisjoint : Disjoint (B\dummyLabels m d) (dummyLabels m d) := by
    apply Finset.disjoint_left.mpr
    intro g hg hD
    exact (Finset.mem_sdiff.mp hg).2 hD
  simpa only [realPart_sdiff_dummy] using
    realMap_realPart_of_disjoint (B\dummyLabels m d) hDisjoint

theorem card_realPart_eq_sdiff {m d : ℕ} (B : Finset (Fin (m+d))) :
    (realPart B).card=(B\dummyLabels m d).card := by
  calc
    (realPart B).card=((realPart B).map (realEmbedding m d)).card := by
      simp only [Finset.card_map]
    _=(B\dummyLabels m d).card := congrArg Finset.card (realMap_realPart_eq_sdiff B)

/-- Exact augmented brackets become the SAME common threshold after the
canonical restriction. A dummy deletion becomes an empty real deletion. -/
theorem actualRealAllocation_commonThreshold {n m d : ℕ}
    (A : Allocation n (m+d)) (v : Finset (Fin m)→ℝ) (t : ℝ)
    (h : ∀i : Fin n,BracketsOneDeletion (fun B=>v (realPart B)) (bundle A i) t) :
    HasCommonThreshold v (actualRealAllocation A) t := by
  classical
  intro i
  obtain ⟨⟨x,hx,hLow⟩,⟨y,hy,hHigh⟩⟩:=h i
  have hWitness (z : Fin (m+d)) (hz : z∈bundle A i) :
      CanDeleteOne (realPart {z}) (bundle (actualRealAllocation A) i) := by
    refine ⟨?_,realPart_card_le_one (by simp)⟩
    rw [bundle_actualRealAllocation]
    exact realPart_mono (Finset.singleton_subset_iff.mpr hz)
  have hComm (z : Fin (m+d)) :
      bundle (actualRealAllocation A) i\realPart {z}=realPart ((bundle A i).erase z) := by
    calc
      bundle (actualRealAllocation A) i\realPart {z}=
          realPart (bundle A i)\realPart {z} := by rw [bundle_actualRealAllocation]
      _=realPart (bundle A i\{z}) := (realPart_sdiff (bundle A i) {z}).symm
      _=realPart ((bundle A i).erase z) := by rw [Finset.sdiff_singleton_eq_erase]
  constructor
  · refine ⟨realPart {x},hWitness x hx,?_⟩
    rw [hComm]
    exact hLow
  · refine ⟨realPart {y},hWitness y hy,?_⟩
    rw [hComm]
    exact hHigh

/-- The already proved Euclidean-size arithmetic applies directly to the
actual canonical dummy set; no allocation or valuation is re-enumerated. -/
theorem actualRealAllocation_balanced {n m d q : ℕ}
    (hCount : m+d=n*q) (hn : 0<n) (hq : 0<q) (hd : d<n)
    (A : Allocation n (m+d))
    (h : ∀i : Fin n,(bundle A i).card=q ∧ (bundle A i∩dummyLabels m d).card≤1) :
    IsBalanced (actualRealAllocation A) := by
  intro i
  rw [bundle_actualRealAllocation,card_realPart_eq_sdiff]
  have hDummy : (dummyLabels m d).card<n := by simpa only [card_dummyLabels] using hd
  have hRealCount : n*q-(dummyLabels m d).card=m := by
    rw [card_dummyLabels]
    omega
  have hSize:=Finite.card_removeDummies_isBalancedSize n q (bundle A i) (dummyLabels m d)
    hn hq hDummy (h i).1 (h i).2
  simpa only [hRealCount] using hSize

/-- The requested final dummy-removal endpoint on the original item type. -/
theorem actualDummyRemoval {n m d q : ℕ}
    (hCount : m+d=n*q) (hn : 0<n) (hq : 0<q) (hd : d<n)
    (A : Allocation n (m+d)) (v : Finset (Fin m)→ℝ) (t : ℝ)
    (h : ∀i : Fin n,(bundle A i).card=q ∧
      BracketsOneDeletion (fun B=>v (realPart B)) (bundle A i) t ∧
      (bundle A i∩dummyLabels m d).card≤1) :
    ∃R : Allocation n m,IsBalanced R ∧ HasCommonThreshold v R t := by
  refine ⟨actualRealAllocation A,?_,?_⟩
  · exact actualRealAllocation_balanced hCount hn hq hd A (fun i=>⟨(h i).1,(h i).2.2⟩)
  · exact actualRealAllocation_commonThreshold A v t (fun i=>(h i).2.1)

/-- The stronger literal-output form exposes the owner's direct restriction,
which downstream readers may use without an existential choice. -/
theorem actualDummyRemoval_spec {n m d q : ℕ}
    (hCount : m+d=n*q) (hn : 0<n) (hq : 0<q) (hd : d<n)
    (A : Allocation n (m+d)) (v : Finset (Fin m)→ℝ) (t : ℝ)
    (h : ∀i : Fin n,(bundle A i).card=q ∧
      BracketsOneDeletion (fun B=>v (realPart B)) (bundle A i) t ∧
      (bundle A i∩dummyLabels m d).card≤1) :
    IsBalanced (actualRealAllocation A) ∧ HasCommonThreshold v (actualRealAllocation A) t :=
  ⟨actualRealAllocation_balanced hCount hn hq hd A (fun i=>⟨(h i).1,(h i).2.2⟩),
    actualRealAllocation_commonThreshold A v t (fun i=>(h i).2.1)⟩

end FairDivision.BF.Recording
