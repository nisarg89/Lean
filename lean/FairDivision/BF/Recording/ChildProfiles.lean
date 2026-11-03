import FairDivision.BF.Recording.Function
import FairDivision.Topology.Volovikov.UniversalJoinEquivariantHomotopy

/-!
# One fixed finite profile space for every parent graph point

A child profile is exactly one recording-graph vertex per child position.
The auxiliary face criterion is the manuscript's disjoint real pools and
sum of maximal dummy counts, with the available real stock and dummy budget
recorded explicitly. All local stocks therefore embed in ONE finite
probability simplex by preserving their real bundles and dummy counts.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace FairDivision.BF.Recording

open FairDivision.Topology FairDivision.Topology.NerveConnectivity

abbrev ChildProfile (p a q m:ℕ):=Fin p→Vertex a q m

def childRealPool {p a q m:ℕ} (S:Finset (ChildProfile p a q m)) (i:Fin p):
    Finset (Fin m):=S.biUnion (fun b=>real (b i))

def childDummyMax {p a q m:ℕ} (S:Finset (ChildProfile p a q m)) (i:Fin p):ℕ:=
  S.sup (fun b=>dummyCount (b i))

theorem childRealPool_mono {p a q m:ℕ}{S T:Finset (ChildProfile p a q m)}
    (hST:S⊆T) (i:Fin p):childRealPool S i⊆childRealPool T i:=by
  intro g hg
  obtain ⟨b,hb,hgb⟩:=Finset.mem_biUnion.mp hg
  exact Finset.mem_biUnion.mpr ⟨b,hST hb,hgb⟩

theorem childDummyMax_mono {p a q m:ℕ}{S T:Finset (ChildProfile p a q m)}
    (hST:S⊆T) (i:Fin p):childDummyMax S i≤childDummyMax T i:=by
  apply Finset.sup_le
  intro b hb
  exact Finset.le_sup (f:=fun c:ChildProfile p a q m=>dummyCount (c i)) (hST hb)

/-- The common-coordinate local auxiliary complex C_{p,aq−1,a}(E,d).
Its vertices retain counts, not dummy identities. -/
def availableAuxiliaryComplex (p a q m:ℕ) (E:Finset (Fin m)) (d:ℕ):
    PreAbstractSimplicialComplex (ChildProfile p a q m) where
  faces:={S|S.Nonempty ∧
    (∀i j:Fin p,i≠j→Disjoint (childRealPool S i) (childRealPool S j)) ∧
    (∑i:Fin p,childDummyMax S i)≤d ∧
    ∀i:Fin p,childRealPool S i⊆E}
  isRelLowerSet_faces:=by
    intro S hS
    refine ⟨hS.1,?_⟩
    intro T hTS hT
    refine ⟨hT,?_,?_,?_⟩
    ·intro i j hij
     exact (hS.2.1 i j hij).mono (childRealPool_mono hTS i) (childRealPool_mono hTS j)
    ·exact (Finset.sum_le_sum (fun i _=>childDummyMax_mono hTS i)).trans hS.2.2.1
    ·intro i
     exact (childRealPool_mono hTS i).trans (hS.2.2.2 i)

theorem availableAuxiliaryComplex_mono {p a q m d e:ℕ}
    {E F:Finset (Fin m)} (hEF:E⊆F) (hde:d≤e):
    availableAuxiliaryComplex p a q m E d≤availableAuxiliaryComplex p a q m F e:=by
  intro S hS
  exact ⟨hS.1,hS.2.1,hS.2.2.1.trans hde,fun i=>(hS.2.2.2 i).trans hEF⟩

/-- Relabel the p child positions; real items and dummy counts stay fixed. -/
def relabelChildProfile {p a q m:ℕ} (σ:Equiv.Perm (Fin p))
    (b:ChildProfile p a q m):ChildProfile p a q m:=fun i=>b (σ.symm i)

/-- Identity and composition are literal reindexings of the child
positions; no real item or dummy count changes. -/
@[simp] theorem relabelChildProfile_one {p a q m:ℕ}:
    relabelChildProfile (a:=a) (q:=q) (m:=m) (1:Equiv.Perm (Fin p))=id:=by
  funext b i
  rfl

theorem relabelChildProfile_mul {p a q m:ℕ}
    (σ τ:Equiv.Perm (Fin p)) (b:ChildProfile p a q m):
    relabelChildProfile (σ*τ) b=relabelChildProfile σ (relabelChildProfile τ b):=by
  funext i
  rfl

def relabelChildProfileEquiv {p a q m:ℕ} (σ:Equiv.Perm (Fin p)):
    ChildProfile p a q m≃ChildProfile p a q m where
  toFun:=relabelChildProfile σ
  invFun:=relabelChildProfile σ.symm
  left_inv:=by intro b;funext i;simp [relabelChildProfile]
  right_inv:=by intro b;funext i;simp [relabelChildProfile]

theorem childRealPool_relabel {p a q m:ℕ} (σ:Equiv.Perm (Fin p))
    (S:Finset (ChildProfile p a q m)) (i:Fin p):
    childRealPool (S.image (relabelChildProfile σ)) i=childRealPool S (σ.symm i):=by
  ext g
  simp only [childRealPool,Finset.mem_biUnion,Finset.mem_image]
  constructor
  ·rintro ⟨c,⟨b,hb,rfl⟩,hg⟩
   exact ⟨b,hb,hg⟩
  ·rintro ⟨b,hb,hg⟩
   exact ⟨relabelChildProfile σ b,⟨b,hb,rfl⟩,hg⟩

theorem childDummyMax_relabel {p a q m:ℕ} (σ:Equiv.Perm (Fin p))
    (S:Finset (ChildProfile p a q m)) (i:Fin p):
    childDummyMax (S.image (relabelChildProfile σ)) i=childDummyMax S (σ.symm i):=by
  simp [childDummyMax,Finset.sup_image,relabelChildProfile,Function.comp_def]

theorem availableAuxiliary_relabel {p a q m d:ℕ} (E:Finset (Fin m))
    (σ:Equiv.Perm (Fin p)) (S:Finset (ChildProfile p a q m))
    (hS:S∈availableAuxiliaryComplex p a q m E d):
    S.image (relabelChildProfile σ)∈availableAuxiliaryComplex p a q m E d:=by
  refine ⟨hS.1.image _,?_,?_,?_⟩
  ·intro i j hij
   rw [childRealPool_relabel,childRealPool_relabel]
   exact hS.2.1 _ _ (fun h=>hij (σ.symm.injective h))
  ·simp_rw [childDummyMax_relabel]
   exact (Equiv.sum_comp σ.symm (fun i=>childDummyMax S i)).le.trans hS.2.2.1
  ·intro i
   rw [childRealPool_relabel]
   exact hS.2.2.2 _

/-- The common ambient profile-simplex position action. -/
def relabelChildLottery {p a q m:ℕ} (σ:Equiv.Perm (Fin p))
    (x:stdSimplex ℝ (ChildProfile p a q m)):
    stdSimplex ℝ (ChildProfile p a q m):=
  stdSimplex.map (relabelChildProfile σ) x

/-- The actual ambient lottery reindexing is an action, by Mathlib's
pushforward identity and composition laws. -/
@[simp] theorem relabelChildLottery_one {p a q m:ℕ}
    (x:stdSimplex ℝ (ChildProfile p a q m)):
    relabelChildLottery (1:Equiv.Perm (Fin p)) x=x:=by
  change stdSimplex.map (relabelChildProfile (1:Equiv.Perm (Fin p))) x=x
  rw [relabelChildProfile_one]
  exact stdSimplex.map_id_apply x

theorem relabelChildLottery_mul {p a q m:ℕ}
    (σ τ:Equiv.Perm (Fin p)) (x:stdSimplex ℝ (ChildProfile p a q m)):
    relabelChildLottery (σ*τ) x=
      relabelChildLottery σ (relabelChildLottery τ x):=by
  change stdSimplex.map (relabelChildProfile (σ*τ)) x=
    stdSimplex.map (relabelChildProfile σ) (stdSimplex.map (relabelChildProfile τ) x)
  rw [stdSimplex.map_comp_apply]
  apply congrArg (fun f:ChildProfile p a q m→ChildProfile p a q m=>stdSimplex.map f x)
  funext b
  exact relabelChildProfile_mul σ τ b

/-- Local stock inclusion into the one fixed profile simplex is literal. -/
def availableAuxiliaryInclude {p a q m d:ℕ} (E:Finset (Fin m)):
    C(simplicialRealization (availableAuxiliaryComplex p a q m E d),
      stdSimplex ℝ (ChildProfile p a q m)):=
  ⟨Subtype.val,continuous_subtype_val⟩

end FairDivision.BF.Recording
