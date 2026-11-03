import FairDivision.BF.Applications.EqualParameters
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Independence, clique, and chromatic-number instances

The graph invariants are the existing Mathlib invariants of actual induced
graphs. The standard deletion facts are proved using Mathlib's maximum
clique witness, induced-clique correspondence, and finite optimal coloring.
Only the equal-parameter extraction is supplied by the manuscript theorem.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Applications

open FairDivision SimpleGraph

/-- Mathlib's clique number of the graph induced on a finite vertex set. -/
def cliqueNumberOn {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N)) : ℕ :=
  (G.induce (S : Set (Fin N))).cliqueNum

/-- An actual maximum clique, written in the original vertex type. -/
theorem exists_maximum_clique_on {N : ℕ} (G : SimpleGraph (Fin N))
    (S : Finset (Fin N)) :
    ∃ C : Finset (Fin N), C ⊆ S ∧ G.IsClique C ∧ C.card = cliqueNumberOn G S := by
  classical
  obtain ⟨C, hC⟩ := (G.induce (S : Set (Fin N))).exists_isNClique_cliqueNum
  have hMapped := (SimpleGraph.isNClique_induce_iff (S : Set (Fin N)) C
    (cliqueNumberOn G S)).mp hC
  refine ⟨C.map (Function.Embedding.subtype _), ?_, hMapped.isClique, hMapped.card_eq⟩
  intro x hx
  obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
  exact y.property

/-- A clique contained in S is bounded by the SAME induced-graph clique
number, using the existing finite induced-clique correspondence. -/
theorem clique_on_card_le {N : ℕ} (G : SimpleGraph (Fin N))
    {C S : Finset (Fin N)} (hCS : C ⊆ S) (hC : G.IsClique C) :
    C.card ≤ cliqueNumberOn G S := by
  classical
  let C' : Finset ↥(S : Set (Fin N)) :=
    C.subtype (fun x => x ∈ (S : Set (Fin N)))
  have hMap : C'.map (Function.Embedding.subtype
      (fun x : Fin N => x ∈ (S : Set (Fin N)))) = C :=
    Finset.subtype_map_of_mem (fun _ hx => hCS hx)
  have hNClique : (G.induce (S : Set (Fin N))).IsNClique C.card C' := by
    apply (SimpleGraph.isNClique_induce_iff (S : Set (Fin N)) C' C.card).mpr
    rw [hMap]
    exact ⟨hC, rfl⟩
  have h := hNClique.isClique.card_le_cliqueNum
  rw [hNClique.card_eq] at h
  exact h

/-- Restriction cannot increase clique number. -/
theorem cliqueNumberOn_mono {N : ℕ} (G : SimpleGraph (Fin N)) :
    Monotone (cliqueNumberOn G) := by
  intro S T hST
  obtain ⟨C, hCS, hC, hCard⟩ := exists_maximum_clique_on G S
  rw [← hCard]
  exact clique_on_card_le G (hCS.trans hST) hC

/-- One deleted vertex can remove at most one vertex of a maximum clique. -/
theorem cliqueNumberOn_erase_le_one {N : ℕ} (G : SimpleGraph (Fin N))
    (S : Finset (Fin N)) (x : Fin N) :
    cliqueNumberOn G S ≤ cliqueNumberOn G (S.erase x) + 1 := by
  classical
  obtain ⟨C, hCS, hC, hCard⟩ := exists_maximum_clique_on G S
  have hSubset : C.erase x ⊆ S.erase x := by
    intro z hz
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1,
      hCS (Finset.mem_erase.mp hz).2⟩
  have hEraseClique : G.IsClique (C.erase x) := by
    intro u hu v hv huv
    exact hC (Finset.mem_erase.mp hu).2 (Finset.mem_erase.mp hv).2 huv
  have hBound := clique_on_card_le G hSubset hEraseClique
  by_cases hx : x ∈ C
  · have hErase := Finset.card_erase_of_mem hx
    have hPositive := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  · rw [Finset.erase_eq_of_notMem hx] at hBound
    omega

/-- The standard clique-number deletion property in the exact integer
format consumed by the manuscript theorem. -/
theorem cliqueNumberOn_unitDeletion {N : ℕ} (G : SimpleGraph (Fin N)) :
    UnitDeletionParameter (fun S => (cliqueNumberOn G S : ℤ)) := by
  intro S x _
  change 0 ≤ (cliqueNumberOn G S : ℤ)-cliqueNumberOn G (S.erase x) ∧
    (cliqueNumberOn G S : ℤ)-cliqueNumberOn G (S.erase x) ≤ 1
  have hLower := cliqueNumberOn_mono G (Finset.erase_subset x S)
  have hUpper := cliqueNumberOn_erase_le_one G S x
  have hLowerInt : (cliqueNumberOn G (S.erase x) : ℤ) ≤ cliqueNumberOn G S := by
    exact_mod_cast hLower
  have hUpperInt : (cliqueNumberOn G S : ℤ) ≤ cliqueNumberOn G (S.erase x) + 1 := by
    exact_mod_cast hUpper
  constructor <;> omega

/-- Complement commutes with taking an induced graph, including its
subtype inequality test. -/
theorem induce_complement {N : ℕ} (G : SimpleGraph (Fin N))
    (S : Finset (Fin N)) :
    Gᶜ.induce (S : Set (Fin N)) = (G.induce (S : Set (Fin N)))ᶜ := by
  ext u v
  simp only [SimpleGraph.induce_adj, SimpleGraph.compl_adj]
  constructor
  ·rintro ⟨hne,hNotAdj⟩
   exact ⟨fun h => hne (congrArg Subtype.val h),hNotAdj⟩
  ·rintro ⟨hne,hNotAdj⟩
   exact ⟨fun h => hne (Subtype.ext h),hNotAdj⟩

/-- Mathlib's independence number equals the clique number of the actual
induced complement. -/
theorem independenceNumberOn_eq {N : ℕ} (G : SimpleGraph (Fin N))
    (S : Finset (Fin N)) :
    (G.induce (S : Set (Fin N))).indepNum = cliqueNumberOn Gᶜ S := by
  rw [cliqueNumberOn, induce_complement, SimpleGraph.cliqueNum_compl]

/-- The standard independence-number deletion property, inherited from
Mathlib's complement-clique identity. -/
theorem independenceNumberOn_unitDeletion {N : ℕ} (G : SimpleGraph (Fin N)) :
    UnitDeletionParameter (fun S : Finset (Fin N) =>
      ((G.induce (S : Set (Fin N))).indepNum : ℤ)) := by
  simpa only [independenceNumberOn_eq] using cliqueNumberOn_unitDeletion Gᶜ

/-- The finite natural value of Mathlib's extended-natural chromatic
number. The coercion identity below guarantees no truncation is involved. -/
def chromaticNumberOn {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N)) : ℕ :=
  (G.induce (S : Set (Fin N))).chromaticNumber.toNat

/-- The induced graph is finite, hence its actual Mathlib chromatic number
is the natural integer used in the deletion argument. -/
theorem chromaticNumberOn_cast {N : ℕ} (G : SimpleGraph (Fin N))
    (S : Finset (Fin N)) :
    (chromaticNumberOn G S : ℕ∞) = (G.induce (S : Set (Fin N))).chromaticNumber := by
  classical
  apply ENat.natCast_toNat
  exact (lt_of_le_of_lt (G.induce (S : Set (Fin N))).chromaticNumber_le_card
    (ENat.natCast_lt_top _)).ne

/-- Restrict an optimal coloring along the actual inclusion. -/
theorem chromaticNumberOn_mono {N : ℕ} (G : SimpleGraph (Fin N)) :
    Monotone (chromaticNumberOn G) := by
  classical
  intro S T hST
  have hSTSet : (S : Set (Fin N)) ⊆ (T : Set (Fin N)) := hST
  have h := SimpleGraph.chromaticNumber_mono_of_hom (G.induceHomOfLE hSTSet).toHom
  rw [← chromaticNumberOn_cast G S, ← chromaticNumberOn_cast G T] at h
  exact_mod_cast h

/-- A coloring after deletion extends by giving the deleted vertex one
new color. This proves the usual unit deletion bound for chromatic number. -/
theorem chromaticNumberOn_erase_le_one {N : ℕ} (G : SimpleGraph (Fin N))
    (S : Finset (Fin N)) (x : Fin N) :
    chromaticNumberOn G S ≤ chromaticNumberOn G (S.erase x) + 1 := by
  classical
  let c : (G.induce ((S.erase x) : Set (Fin N))).Coloring
      (Fin (chromaticNumberOn G (S.erase x))) :=
    Classical.choice (G.induce ((S.erase x) : Set (Fin N))).colorable_chromaticNumber_of_fintype
  let color : ↥(S : Set (Fin N)) → Fin (chromaticNumberOn G (S.erase x) + 1) :=
    fun u => if h : u.val = x then Fin.last _
      else Fin.castSucc (c ⟨u.val, Finset.mem_erase.mpr ⟨h, u.property⟩⟩)
  have hValid : ∀ {u v : (S : Set (Fin N))},
      (G.induce (S : Set (Fin N))).Adj u v → color u ≠ color v := by
    intro u v huv hEqual
    by_cases hu : u.val = x
    · by_cases hv : v.val = x
      · exact huv.ne (Subtype.ext (hu.trans hv.symm))
      · simp only [color, dif_pos hu, dif_neg hv] at hEqual
        have hValue : chromaticNumberOn G (S.erase x) =
            (c ⟨v.val, Finset.mem_erase.mpr ⟨hv, v.property⟩⟩).val :=
          congrArg (fun z : Fin (chromaticNumberOn G (S.erase x)+1)=>z.val) hEqual
        have hBound := (c ⟨v.val, Finset.mem_erase.mpr ⟨hv, v.property⟩⟩).isLt
        omega
    · by_cases hv : v.val = x
      · simp only [color, dif_neg hu, dif_pos hv] at hEqual
        have hValue : (c ⟨u.val, Finset.mem_erase.mpr ⟨hu, u.property⟩⟩).val =
            chromaticNumberOn G (S.erase x) :=
          congrArg (fun z : Fin (chromaticNumberOn G (S.erase x)+1)=>z.val) hEqual
        have hBound := (c ⟨u.val, Finset.mem_erase.mpr ⟨hu, u.property⟩⟩).isLt
        omega
      · simp only [color, dif_neg hu, dif_neg hv] at hEqual
        exact c.valid
          (v:=⟨u.val,Finset.mem_erase.mpr ⟨hu,u.property⟩⟩)
          (w:=⟨v.val,Finset.mem_erase.mpr ⟨hv,v.property⟩⟩)
          huv (Fin.castSucc_injective _ hEqual)
  have hColorable : (G.induce (S : Set (Fin N))).Colorable
      (chromaticNumberOn G (S.erase x) + 1) :=
    ⟨SimpleGraph.Coloring.mk color hValid⟩
  have hUpper := hColorable.chromaticNumber_le
  rw [← chromaticNumberOn_cast G S] at hUpper
  exact_mod_cast hUpper

/-- Chromatic number has exactly the integer deletion property required by
the manuscript, without an auxiliary coloring certificate in its conclusion. -/
theorem chromaticNumberOn_unitDeletion {N : ℕ} (G : SimpleGraph (Fin N)) :
    UnitDeletionParameter (fun S => (chromaticNumberOn G S : ℤ)) := by
  intro S x _
  change 0 ≤ (chromaticNumberOn G S : ℤ)-chromaticNumberOn G (S.erase x) ∧
    (chromaticNumberOn G S : ℤ)-chromaticNumberOn G (S.erase x) ≤ 1
  have hLower := chromaticNumberOn_mono G (Finset.erase_subset x S)
  have hUpper := chromaticNumberOn_erase_le_one G S x
  have hLowerInt : (chromaticNumberOn G (S.erase x) : ℤ) ≤ chromaticNumberOn G S := by
    exact_mod_cast hLower
  have hUpperInt : (chromaticNumberOn G S : ℤ) ≤ chromaticNumberOn G (S.erase x) + 1 := by
    exact_mod_cast hUpper
  constructor <;> omega

/-- Actual induced subgraphs of the asserted order and equal clique
number, omitting at most 2k-1 of the original vertices. -/
theorem exists_disjoint_equal_clique_numbers (N k : ℕ) (hk : 0 < k)
    (hEnough : 2 * k ≤ N) (G : SimpleGraph (Fin N)) :
    ∃ B : Fin k → Finset (Fin N),
      (∀ i, (B i).card = N / k - 1) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i j, (G.induce (B i : Set (Fin N))).cliqueNum =
        (G.induce (B j : Set (Fin N))).cliqueNum) ∧
      (Finset.univ \ Finset.univ.biUnion B).card ≤ 2 * k - 1 := by
  obtain ⟨B, T, hCard, hDisjoint, hValue, _, hOmit⟩ :=
    exists_disjoint_equal_parameters N k hk hEnough (fun S => (cliqueNumberOn G S : ℤ))
      (cliqueNumberOn_unitDeletion G)
  refine ⟨B, hCard, hDisjoint, ?_, hOmit⟩
  intro i j
  have hEq : (cliqueNumberOn G (B i) : ℤ)=cliqueNumberOn G (B j) :=
    (hValue i).trans (hValue j).symm
  change cliqueNumberOn G (B i) = cliqueNumberOn G (B j)
  exact_mod_cast hEq

/-- The identical statement for Mathlib's actual independence number. -/
theorem exists_disjoint_equal_independence_numbers (N k : ℕ) (hk : 0 < k)
    (hEnough : 2 * k ≤ N) (G : SimpleGraph (Fin N)) :
    ∃ B : Fin k → Finset (Fin N),
      (∀ i, (B i).card = N / k - 1) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i j, (G.induce (B i : Set (Fin N))).indepNum =
        (G.induce (B j : Set (Fin N))).indepNum) ∧
      (Finset.univ \ Finset.univ.biUnion B).card ≤ 2 * k - 1 := by
  obtain ⟨B, T, hCard, hDisjoint, hValue, _, hOmit⟩ :=
    exists_disjoint_equal_parameters N k hk hEnough
      (fun S : Finset (Fin N) => ((G.induce (S : Set (Fin N))).indepNum : ℤ))
      (independenceNumberOn_unitDeletion G)
  refine ⟨B, hCard, hDisjoint, ?_, hOmit⟩
  intro i j
  have hEq : ((G.induce (B i : Set (Fin N))).indepNum : ℤ)=
      (G.induce (B j : Set (Fin N))).indepNum :=
    (hValue i).trans (hValue j).symm
  exact_mod_cast hEq

/-- The identical statement for Mathlib's actual extended-natural
chromatic number; no custom graph parameter replaces it in the conclusion. -/
theorem exists_disjoint_equal_chromatic_numbers (N k : ℕ) (hk : 0 < k)
    (hEnough : 2 * k ≤ N) (G : SimpleGraph (Fin N)) :
    ∃ B : Fin k → Finset (Fin N),
      (∀ i, (B i).card = N / k - 1) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i j, (G.induce (B i : Set (Fin N))).chromaticNumber =
        (G.induce (B j : Set (Fin N))).chromaticNumber) ∧
      (Finset.univ \ Finset.univ.biUnion B).card ≤ 2 * k - 1 := by
  obtain ⟨B, T, hCard, hDisjoint, hValue, _, hOmit⟩ :=
    exists_disjoint_equal_parameters N k hk hEnough (fun S => (chromaticNumberOn G S : ℤ))
      (chromaticNumberOn_unitDeletion G)
  refine ⟨B, hCard, hDisjoint, ?_, hOmit⟩
  intro i j
  have hEqInt : (chromaticNumberOn G (B i) : ℤ)=chromaticNumberOn G (B j) :=
    (hValue i).trans (hValue j).symm
  have hEq : chromaticNumberOn G (B i) = chromaticNumberOn G (B j) := by
    exact_mod_cast hEqInt
  rw [← chromaticNumberOn_cast G (B i), ← chromaticNumberOn_cast G (B j), hEq]

/-- The actual finite set of values on all labeled s-vertex graphs. The
labeling does not inflate the number of distinct parameter values. -/
def graphParameterValues (s : ℕ)
    (P : SimpleGraph (Fin s) → Finset (Fin s) → ℤ) : Finset ℤ :=
  Finset.univ.image (fun G => P G Finset.univ)

/-- The manuscript's g_P(s)≤s+1 bound across ALL s-vertex graphs. The
common base is P(empty); it need not be zero. Graph invariance identifies
the empty-graph value, represented here by the explicit common-base premise. -/
theorem graphParameter_values_le (s : ℕ)
    (P : SimpleGraph (Fin s) → Finset (Fin s) → ℤ)
    (hP : ∀ G, UnitDeletionParameter (P G))
    (base : ℤ) (hBase : ∀ G, P G ∅ = base) :
    (graphParameterValues s P).card ≤ s + 1 := by
  apply integer_family_distinct_values_le (fun G => P G Finset.univ) base s
  intro G
  simpa only [hBase G, Finset.card_univ, Fintype.card_fin] using
    unitDeletion_value_bounds (hP G) Finset.univ

/-- Consequently the paper's generic Caro--Yuster size condition holds
at s=floor(N/3), for the actual set of graph-parameter values. -/
theorem graphParameter_caro_yuster_comparison (N : ℕ)
    (P : SimpleGraph (Fin (N / 3)) → Finset (Fin (N / 3)) → ℤ)
    (hP : ∀ G, UnitDeletionParameter (P G))
    (base : ℤ) (hBase : ∀ G, P G ∅ = base) :
    (graphParameterValues (N / 3) P).card < N - 2 * (N / 3) + 2 :=
  caro_yuster_generic_comparison N _ (graphParameter_values_le (N / 3) P hP base hBase)

end FairDivision.BF.Applications
