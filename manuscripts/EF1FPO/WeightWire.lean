import EF1FPO.InstanceWire
import EF1FPO.Geometry
import EF1FPO.PreparationMatrixWire
import OAI.Optimization.LinearProgramming.PriceGame.ControlRatListSum
import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCost
import OAI.Computability.QuantumFactoring.BitStackRationalDivision

/-! Exact relative weights and component scales on a serialized bidder graph. -/

set_option autoImplicit false

namespace EF1FPO.WeightWire

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame
open EF1FPO.InstanceWire
open EF1FPO.PreparationMatrixWire (readCell)

structure GraphPacket where
  inst : Instance
  mask : inst.Agent → inst.Good → Bool

def GraphPacket.encode (d : GraphPacket) : Word :=
  encodeInstance d.inst ++ (List.ofFn (fun i => List.ofFn (d.mask i))).flatten

structure PackedGraph where
  agents : ℕ
  goods : ℕ
  valuations : List ℚ
  mask : List Bool

def packedCode (d : PackedGraph) : Word :=
  prodCode unaryCode (prodCode unaryCode (prodCode (listCode ratCode) (listCode boolCode)))
    (d.agents, d.goods, d.valuations, d.mask)

def GraphPacket.decode (d : GraphPacket) : PackedGraph :=
  ⟨d.inst.n, d.inst.m, (List.ofFn (fun i => List.ofFn (d.inst.v i))).flatten,
    (List.ofFn (fun i => List.ofFn (d.mask i))).flatten⟩

noncomputable def decodeGraph : Procedure GraphPacket.encode packedCode GraphPacket.decode := by
  let field (b : Bool) : Word := [b]
  let source (p : Bool × Word) : Word := p.1 :: p.2
  let readOne : Procedure (fun p : Bool × Word => field p.1 ++ p.2) (prodCode boolCode id) id :=
    ((Procedure.head.pair Procedure.tail).precompose source).congrFun (by rintro ⟨b, tail⟩; rfl)
  let readBits := decodeCountedFields field boolCode false readOne 1
    (by intro b; simp [field]) (by intro b; simp [field, boolCode])
    (by intro b; simp [field, boolCode])
  let fields := prodCode (listCode ratCode) id
  let other := prodCode unaryCode fields
  let matrix : Procedure GraphPacket.encode decodedInstanceCode
      (fun p => decodeInstance (p.inst, p.decode.mask)) :=
    (decodeInstancePrefix.precompose (fun p : GraphPacket => (p.inst, p.decode.mask))).congrEncoding
      (by intro p; rfl) (by intro p; rfl)
  let agents := (first unaryCode other).comp matrix
  let suffix := (second unaryCode other).comp matrix
  let goods := (first unaryCode fields).comp suffix
  let values := (second unaryCode fields).comp suffix
  let entries := (first (listCode ratCode) id).comp values
  let rawMask := (second (listCode ratCode) id).comp values
  let count := unaryMul.comp (agents.pair goods)
  have field_length (p : GraphPacket) : p.decode.mask.length = p.inst.n * p.inst.m := by
    simp [GraphPacket.decode, List.length_flatten, List.map_ofFn, Function.comp_def]
  have fields_exact (xs : Word) : xs.flatMap field = xs := by
    induction xs with
    | nil => rfl
    | cons b xs ih => simp [field, ih]
  let maskInput : Procedure GraphPacket.encode (countedFields field) (fun p => (p.decode.mask, [])) :=
    (count.pair rawMask).result (by
      intro p
      change prodCode unaryCode id (p.inst.n * p.inst.m, p.decode.mask) = _
      simp [countedFields, rawFields, field_length, fields_exact])
  let mask := (first (listCode boolCode) id).comp (readBits.comp maskInput)
  exact (agents.pair (goods.pair (entries.pair mask))).result (by intro p; rfl)

def tableValue (d : PackedGraph) (i g : ℕ) : ℚ := readCell 0 d.valuations (i * d.goods + g)

def marked (d : PackedGraph) (i g : ℕ) : Bool := readCell false d.mask (i * d.goods + g)

private noncomputable def graphTuple : Procedure packedCode
    (prodCode unaryCode (prodCode unaryCode (prodCode (listCode ratCode) (listCode boolCode))))
    (fun p => (p.agents, p.goods, p.valuations, p.mask)) :=
  (identity _).precompose (fun p : PackedGraph => (p.agents, p.goods, p.valuations, p.mask))

private noncomputable def graphAgentCount : Procedure packedCode unaryCode PackedGraph.agents :=
  ((first unaryCode (prodCode unaryCode (prodCode (listCode ratCode) (listCode boolCode)))).comp
    graphTuple).congrFun (by intro p; rfl)

private noncomputable def graphGoodCount : Procedure packedCode unaryCode PackedGraph.goods :=
  ((first unaryCode (prodCode (listCode ratCode) (listCode boolCode))).comp
    ((second unaryCode (prodCode unaryCode (prodCode (listCode ratCode) (listCode boolCode)))).comp
      graphTuple)).congrFun (by intro p; rfl)

private noncomputable def columnLookup {α : Type} (cell : α → Word) (fallback : α)
    (data : PackedGraph → List α) (cells : Procedure packedCode (listCode cell) data) :
    Procedure (prodCode Nat.bits (prodCode Nat.bits packedCode)) cell
      (fun p => readCell fallback (data p.2.2) (p.1 * p.2.2.goods + p.2.1)) := by
  let indices := prodCode Nat.bits packedCode
  let i := first Nat.bits indices
  let rest := second Nat.bits indices
  let g := (first Nat.bits packedCode).comp rest
  let table := (second Nat.bits packedCode).comp rest
  let width := (unaryToBits.comp graphGoodCount).comp table
  let offset := binaryMul.comp (i.pair width)
  let absolute := binaryAdd.comp (offset.pair g)
  exact ((listGet cell fallback).comp (absolute.pair (cells.comp table))).congrFun (by intro p; rfl)

private noncomputable def valueLookup :
    Procedure (prodCode Nat.bits (prodCode Nat.bits packedCode)) ratCode
      (fun p => tableValue p.2.2 p.1 p.2.1) := by
  let values := listCode ratCode
  let masks := listCode boolCode
  let payload := prodCode values masks
  let fields := (second unaryCode payload).comp ((second unaryCode (prodCode unaryCode payload)).comp graphTuple)
  exact (columnLookup ratCode 0 PackedGraph.valuations
    (((first values masks).comp fields).congrFun (by intro p; rfl))).congrFun (by intro p; rfl)

private noncomputable def markLookup :
    Procedure (prodCode Nat.bits (prodCode Nat.bits packedCode)) boolCode
      (fun p => marked p.2.2 p.1 p.2.1) := by
  let values := listCode ratCode
  let masks := listCode boolCode
  let payload := prodCode values masks
  let fields := (second unaryCode payload).comp ((second unaryCode (prodCode unaryCode payload)).comp graphTuple)
  exact (columnLookup boolCode false PackedGraph.mask
    (((second values masks).comp fields).congrFun (by intro p; rfl))).congrFun (by intro p; rfl)

def relativeOrigin (d : PackedGraph) (root : ℕ) : List ℚ :=
  (List.range d.agents).map (fun i => if i = root then 1 else 0)

def relativeCandidate (d : PackedGraph) (rho : List ℚ) (target source good : ℕ) : ℚ :=
  if marked d target good && marked d source good then
    readCell 0 rho source * tableValue d source good / tableValue d target good else 0

def relativeStep (d : PackedGraph) (rho : List ℚ) : List ℚ :=
  (List.range d.agents).map (fun i =>
    ((List.range d.agents).flatMap (fun j => (List.range d.goods).map (relativeCandidate d rho i j))).foldl
      max (readCell 0 rho i))

private noncomputable def chosenFold (f : ℚ → ℚ → ℚ)
    (step : Procedure (prodCode ratCode ratCode) ratCode (fun p => f p.2 p.1))
    (choice : ∀ a b, f a b = a ∨ f a b = b) :
    Procedure (prodCode (listCode ratCode) ratCode) ratCode (fun p => p.1.foldl f p.2) := by
  have selected (xs : List ℚ) (seed : ℚ) : xs.foldl f seed = seed ∨ xs.foldl f seed ∈ xs := by
    induction xs generalizing seed with
    | nil => exact Or.inl rfl
    | cons x xs ih =>
      rw [List.foldl_cons]
      rcases ih (f seed x) with he | hm
      · rcases choice seed x with left | right
        · exact Or.inl (he.trans left)
        · exact Or.inr (List.mem_cons.mpr (Or.inl (he.trans right)))
      · exact Or.inr (List.mem_cons_of_mem _ hm)
  exact (foldList 0 step Polynomial.X (by
    intro xs seed i
    change (ratCode ((xs.take i).foldl f seed)).length ≤ _
    rw [Polynomial.eval_X]
    rcases selected (xs.take i) seed with h | h
    · rw [h]; omega
    · exact (code_le_of_mem ratCode (List.mem_of_mem_take h)).trans (Nat.le_add_right _ _)
    )).congrFun (by intro p; rfl)

private noncomputable def foldMax :
    Procedure (prodCode (listCode ratCode) ratCode) ratCode (fun p => p.1.foldl max p.2) :=
  chosenFold max (Control.Native.ratMaxP.comp (swap ratCode ratCode)) (fun a b =>
    (le_total a b).elim (fun h => Or.inr (max_eq_right h)) (fun h => Or.inl (max_eq_left h)))

private noncomputable def foldMin :
    Procedure (prodCode (listCode ratCode) ratCode) ratCode (fun p => p.1.foldl min p.2) :=
  chosenFold min (Control.Native.ratMinP.comp (swap ratCode ratCode)) (fun a b =>
    (le_total a b).elim (fun h => Or.inl (min_eq_left h)) (fun h => Or.inr (min_eq_right h)))

noncomputable def relativeStepProcedure : Procedure (prodCode packedCode (listCode ratCode))
    (listCode ratCode) (fun p => relativeStep p.1 p.2) := by
  let rats := listCode ratCode
  let state := prodCode packedCode rats
  let targetData := prodCode Nat.bits state
  let context := prodCode Nat.bits (prodCode Nat.bits state)
  let cellInput := prodCode unaryCode context
  let good := unaryToBits.comp (first unaryCode context)
  let input := second unaryCode context
  let target := (first Nat.bits (prodCode Nat.bits state)).comp input
  let remaining := (second Nat.bits (prodCode Nat.bits state)).comp input
  let source := (first Nat.bits state).comp remaining
  let fields := (second Nat.bits state).comp remaining
  let graph := (first packedCode rats).comp fields
  let ratios := (second packedCode rats).comp fields
  let goodData := good.pair graph
  let toTarget := target.pair goodData
  let toSource := source.pair goodData
  let tied := boolAnd.comp ((markLookup.comp toTarget).pair (markLookup.comp toSource))
  let width := (listGet ratCode 0).comp (source.pair ratios)
  let product := ratMul.comp (width.pair (valueLookup.comp toSource))
  let score := ratDiv.comp (product.pair (valueLookup.comp toTarget))
  let candidate : Procedure cellInput ratCode (fun p =>
      relativeCandidate p.2.2.2.1 p.2.2.2.2 p.2.1 p.2.2.1 p.1) :=
    (conditional tied score (constant cellInput ratCode 0)).congrFun (by intro p; rfl)
  let byGood := tabulate (ea := context) (eb := ratCode)
    (f := fun p => relativeCandidate p.2.2.1 p.2.2.2 p.1 p.2.1) 0 candidate
  let j := unaryToBits.comp (first unaryCode targetData)
  let rowInput := second unaryCode targetData
  let i := (first Nat.bits state).comp rowInput
  let base := (second Nat.bits state).comp rowInput
  let m := graphGoodCount.comp ((first packedCode rats).comp base)
  let row : Procedure (prodCode unaryCode targetData) rats
      (fun p => (List.range p.2.2.1.goods).map (relativeCandidate p.2.2.1 p.2.2.2 p.2.1 p.1)) :=
    (byGood.comp (m.pair (i.pair (j.pair base)))).congrFun (by intro p; rfl)
  let bySource := tabulate (ea := targetData) (eb := rats)
    (f := fun p j => (List.range p.2.1.goods).map (relativeCandidate p.2.1 p.2.2 p.1 j)) [] row
  let t := unaryToBits.comp (first unaryCode state)
  let stepInput := second unaryCode state
  let n := graphAgentCount.comp ((first packedCode rats).comp stepInput)
  let rows := bySource.comp (n.pair (t.pair stepInput))
  let flat := (Learning.GenerationCost.flattenP ratCode 0).comp rows
  let start := (listGet ratCode 0).comp (t.pair ((second packedCode rats).comp stepInput))
  have flatten (f : ℕ → List ℚ) (xs : List ℕ) : (xs.map f).flatten = xs.flatMap f := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]
  let best : Procedure (prodCode unaryCode state) ratCode (fun p =>
      ((List.range p.2.1.agents).flatMap (fun j => (List.range p.2.1.goods).map
        (relativeCandidate p.2.1 p.2.2 p.1 j))).foldl max (readCell 0 p.2.2 p.1)) :=
    (foldMax.comp (flat.pair start)).congrFun (by intro p; simp [Function.comp_apply, flatten, readCell])
  let all := tabulate (ea := state) (eb := ratCode)
    (f := fun p i => ((List.range p.1.agents).flatMap (fun j => (List.range p.1.goods).map
      (relativeCandidate p.1 p.2 i j))).foldl max (readCell 0 p.2 i)) 0 best
  exact (all.comp ((graphAgentCount.comp (first packedCode rats)).pair (identity state))).congrFun
    (by intro p; rfl)

def relativeFinal (d : PackedGraph) (root : ℕ) : List ℚ :=
  ((relativeStep d)^[d.agents + d.goods]) (relativeOrigin d root)

def soleBidder (d : PackedGraph) (i g : ℕ) : Bool :=
  marked d i g && ((List.range d.agents).filter (fun j => decide (j ≠ i) && marked d j g)).isEmpty

def forcedUtility (d : PackedGraph) (i : ℕ) : ℚ :=
  ((List.range d.goods).map (fun g => if soleBidder d i g then tableValue d i g else 0)).sum

def rootScale (d : PackedGraph) (rho : List ℚ) : ℚ :=
  ((List.range d.agents).map (fun i =>
    let r := readCell 0 rho i
    let u := forcedUtility d i
    if r = 0 then 4 else min (4 / r) (if u = 0 then 4 else 1 / (r * u)))).foldl min 4

noncomputable def rootScaleProcedure : Procedure (prodCode packedCode (listCode ratCode))
    ratCode (fun p => rootScale p.1 p.2) := by
  let cellCode := prodCode Nat.bits (prodCode Nat.bits packedCode)
  let cell := first cellCode Nat.bits
  let j := second cellCode Nat.bits
  let owner := (first Nat.bits (prodCode Nat.bits packedCode)).comp cell
  let goodGraph := (second Nat.bits (prodCode Nat.bits packedCode)).comp cell
  let different := boolNot.comp (Control.Native.natEqP.comp (j.pair owner))
  let bidder := markLookup.comp (j.pair goodGraph)
  let rival := boolAnd.comp (different.pair bidder)
  let graph := (second Nat.bits packedCode).comp (second Nat.bits (prodCode Nat.bits packedCode))
  let indices := Control.Native.addressRangeP.comp (graphAgentCount.comp graph)
  let rivals := (Learning.BitMachine.filterWithP (0 : ℕ) rival).comp (indices.pair (identity cellCode))
  let only : Procedure cellCode boolCode (fun p => soleBidder p.2.2 p.1 p.2.1) :=
    (boolAnd.comp (markLookup.pair ((listEmpty Nat.bits).comp rivals))).congrFun (by
      intro p
      simp [Function.comp_apply, soleBidder])
  let consumer := prodCode Nat.bits packedCode
  let columnData := prodCode unaryCode consumer
  let col := unaryToBits.comp (first unaryCode consumer)
  let context := second unaryCode consumer
  let i := (first Nat.bits packedCode).comp context
  let table := (second Nat.bits packedCode).comp context
  let cellInput := i.pair (col.pair table)
  let uniqueCell : Procedure columnData ratCode
      (fun p => if soleBidder p.2.2 p.2.1 p.1 then tableValue p.2.2 p.2.1 p.1 else 0) :=
    conditional (only.comp cellInput) (valueLookup.comp cellInput) (constant columnData ratCode 0)
  let row := tabulate (ea := consumer) (eb := ratCode)
    (f := fun p g => if soleBidder p.2 p.1 g then tableValue p.2 p.1 g else 0) 0 uniqueCell
  let width := graphGoodCount.comp (second Nat.bits packedCode)
  let utility : Procedure consumer ratCode (fun p => forcedUtility p.2 p.1) :=
    (Control.Native.ratListSumP.comp (row.comp (width.pair (identity consumer)))).congrFun (by intro p; rfl)
  let zero : Procedure ratCode boolCode (fun q => decide (q = 0)) :=
    (binaryZero.comp (intAbs.comp ratNum)).congrFun (by intro q; simp)
  let rats := listCode ratCode
  let foldedData := prodCode packedCode rats
  let boundInput := prodCode unaryCode foldedData
  let addr := unaryToBits.comp (first unaryCode foldedData)
  let fields := second unaryCode foldedData
  let dataset := (first packedCode rats).comp fields
  let q := (listGet ratCode 0).comp (addr.pair ((second packedCode rats).comp fields))
  let u := utility.comp (addr.pair dataset)
  let four := constant boundInput ratCode 4
  let unity := constant boundInput ratCode 1
  let capBound := ratDiv.comp (four.pair q)
  let spendBound := ratDiv.comp (unity.pair (ratMul.comp (q.pair u)))
  let spend := conditional (zero.comp u) four spendBound
  let boundOp : Procedure boundInput ratCode (fun p =>
      let r := readCell 0 p.2.2 p.1
      let u := forcedUtility p.2.1 p.1
      if r = 0 then 4 else min (4 / r) (if u = 0 then 4 else 1 / (r * u))) :=
    (conditional (zero.comp q) four (Control.Native.ratMinP.comp (capBound.pair spend))).congrFun (by
      intro p
      simp [Function.comp_apply, readCell])
  let all := tabulate (ea := foldedData) (eb := ratCode)
    (f := fun p i =>
      let r := readCell 0 p.2 i
      let u := forcedUtility p.1 i
      if r = 0 then 4 else min (4 / r) (if u = 0 then 4 else 1 / (r * u))) 0 boundOp
  let values := all.comp ((graphAgentCount.comp (first packedCode rats)).pair (identity foldedData))
  exact (foldMin.comp (values.pair (constant foldedData ratCode 4))).congrFun (by intro p; rfl)

def ValidMask (d : GraphPacket) (q : d.inst.Agent → ℚ) : Prop :=
  (∀ i, 0 < q i) ∧ d.inst.PositiveColumns ∧
  ∀ i g, d.mask i g = true ↔ d.inst.IsHighestBidder (fun j => (q j : ℝ)) i g

def RelativeInvariant (d : GraphPacket) (q : d.inst.Agent → ℚ)
    (root : d.inst.Agent) (rho : List ℚ) : Prop :=
  rho.length = d.inst.n ∧
  ∀ i : d.inst.Agent, readCell 0 rho i.val = 0 ∨
    (readCell 0 rho i.val = q i / q root ∧ d.inst.AgentConnected (fun j => (q j : ℝ)) root i)

private theorem read_range {α : Type} (fallback : α) (f : ℕ → α) {n i : ℕ} (hi : i < n) :
    readCell fallback ((List.range n).map f) i = f i := by
  rw [readCell, List.headD_eq_head?_getD, List.head?_drop,
    List.getElem?_eq_getElem (by simpa using hi), Option.getD_some]
  simp

private theorem read_rectangular {α : Type} {n m : ℕ} (fallback : α)
    (u : Fin n → Fin m → α) (i : Fin n) (g : Fin m) :
    readCell fallback (List.ofFn (fun j => List.ofFn (u j))).flatten (i.val * m + g.val) = u i g := by
  let e : Fin n × Fin m ≃ Fin (n * m) := finProdFinEquiv
  let f (z : Fin (n * m)) := u (e.symm z).1 (e.symm z).2
  have address (i : Fin n) (g : Fin m) : (e (i, g)).val = i.val * m + g.val := by
    change g.val + m * i.val = _
    ac_rfl
  have packing : (List.ofFn (fun j => List.ofFn (u j))).flatten = List.ofFn f := by
    rw [List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext x
    apply congrArg List.ofFn
    funext y
    have hCoord : ∀ z : Fin (n * m), z.val = x.val * m + y.val → e.symm z = (x, y) := by
      intro z hz
      apply e.injective
      rw [Equiv.apply_symm_apply]
      exact Fin.ext (hz.trans (address x y).symm)
    exact (congrArg (fun p : Fin n × Fin m => u p.1 p.2) (hCoord _ (by simp))).symm
  rw [packing, ← address i g, readCell, List.headD_eq_head?_getD, List.head?_drop,
    List.getElem?_eq_getElem (by simp), Option.getD_some, List.getElem_ofFn]
  exact congrArg (fun p : Fin n × Fin m => u p.1 p.2) (e.symm_apply_apply (i, g))

private theorem table_at (d : GraphPacket) (i : d.inst.Agent) (g : d.inst.Good) :
    tableValue d.decode i.val g.val = d.inst.v i g :=
  read_rectangular 0 d.inst.v i g

private theorem mark_at (d : GraphPacket) (i : d.inst.Agent) (g : d.inst.Good) :
    marked d.decode i.val g.val = d.mask i g :=
  read_rectangular false d.mask i g

private theorem positive_marked (d : GraphPacket) (q : d.inst.Agent → ℚ) (h : ValidMask d q)
    (i : d.inst.Agent) (g : d.inst.Good) (hi : d.mask i g = true) : 0 < d.inst.v i g := by
  obtain ⟨j, hj⟩ := h.2.1 g
  have hWeight (k : d.inst.Agent) : (0 : ℝ) < (q k : ℝ) := by exact_mod_cast h.1 k
  have hBid : 0 < d.inst.bid (fun k => (q k : ℝ)) j g := mul_pos (hWeight j) hj
  have hiBid := hBid.trans_le ((h.2.2 i g).1 hi j)
  have hiValue : 0 < d.inst.value i g := pos_of_mul_pos_right hiBid (hWeight i).le
  change 0 < (d.inst.v i g : ℝ) at hiValue
  exact_mod_cast hiValue

theorem relative_origin_invariant (d : GraphPacket) (q : d.inst.Agent → ℚ)
    (h : ValidMask d q) (root : d.inst.Agent) :
    RelativeInvariant d q root (relativeOrigin d.decode root.val) := by
  refine ⟨by simp [relativeOrigin, GraphPacket.decode], ?_⟩
  intro i
  unfold relativeOrigin
  have hiLen : i.val < d.decode.agents := i.isLt
  rw [read_range _ _ hiLen]
  by_cases hi : i = root
  · subst i
    exact Or.inr ⟨by simp [(h.1 root).ne'], SimpleGraph.Reachable.rfl⟩
  · exact Or.inl (by simp [Fin.val_inj, hi])

theorem relative_step_invariant (d : GraphPacket) (q : d.inst.Agent → ℚ)
    (h : ValidMask d q) (root : d.inst.Agent) (rho : List ℚ)
    (hrho : RelativeInvariant d q root rho) : RelativeInvariant d q root (relativeStep d.decode rho) := by
  let w : d.inst.Weights := fun i => (q i : ℝ)
  let Good (i : d.inst.Agent) (x : ℚ) : Prop :=
    x = 0 ∨ (x = q i / q root ∧ d.inst.AgentConnected w root i)
  have candidates (i j : d.inst.Agent) (g : d.inst.Good) :
      Good i (relativeCandidate d.decode rho i.val j.val g.val) := by
    unfold relativeCandidate
    rw [mark_at, mark_at, table_at, table_at]
    by_cases hBoth : d.mask i g && d.mask j g
    · obtain ⟨hi, hj⟩ := Bool.and_eq_true_iff.mp hBoth
      rw [if_pos hBoth]
      rcases hrho.2 j with hZero | ⟨hRatio, hPath⟩
      · exact Or.inl (by simp [hZero])
      · have hiB := (h.2.2 i g).mp hi
        have hjB := (h.2.2 j g).mp hj
        have htReal := (hiB j).antisymm (hjB i)
        change (q j : ℝ) * (d.inst.v j g : ℝ) = (q i : ℝ) * (d.inst.v i g : ℝ) at htReal
        have ht : q j * d.inst.v j g = q i * d.inst.v i g := by exact_mod_cast htReal
        have hvi := positive_marked d q h i g hi
        have hPathStep : d.inst.AgentConnected w j i := by
          have h1 : (d.inst.highestBidderGraph w).Adj (Sum.inl j) (Sum.inr g) := by
            simpa [Instance.highestBidderGraph] using hjB
          have h2 : (d.inst.highestBidderGraph w).Adj (Sum.inl i) (Sum.inr g) := by
            simpa [Instance.highestBidderGraph] using hiB
          exact ⟨SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2.symm SimpleGraph.Walk.nil)⟩
        refine Or.inr ⟨?_, hPath.trans hPathStep⟩
        rw [hRatio]
        apply (div_eq_iff hvi.ne').mpr
        simp only [div_mul_eq_mul_div, ht]
    · rw [if_neg hBoth]
      exact Or.inl rfl
  have fold_good (i : d.inst.Agent) (xs : List ℚ) (a : ℚ) (ha : Good i a)
      (hx : ∀ x ∈ xs, Good i x) : Good i (xs.foldl max a) := by
    induction xs generalizing a with
    | nil => exact ha
    | cons x xs ih =>
      rw [List.foldl_cons]
      apply ih (max a x) _ (fun t ht => hx t (List.mem_cons_of_mem _ ht))
      rcases le_total a x with hax | hxa
      · rw [max_eq_right hax]
        exact hx x List.mem_cons_self
      · rwa [max_eq_left hxa]
  refine ⟨by simp [relativeStep, GraphPacket.decode], ?_⟩
  intro i
  have hi : i.val < d.decode.agents := i.isLt
  unfold relativeStep
  rw [read_range _ _ hi]
  apply fold_good i _ _ (hrho.2 i)
  intro x hx
  obtain ⟨j, hj, hG⟩ := List.mem_flatMap.mp hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hG
  exact candidates i ⟨j, List.mem_range.mp hj⟩ ⟨g, List.mem_range.mp hg⟩

theorem relative_complete (d : GraphPacket) (q : d.inst.Agent → ℚ)
    (h : ValidMask d q) (root i : d.inst.Agent) :
    (d.inst.AgentConnected (fun j => (q j : ℝ)) root i →
      readCell 0 (relativeFinal d.decode root.val) i.val = q i / q root) ∧
    (¬ d.inst.AgentConnected (fun j => (q j : ℝ)) root i →
      readCell 0 (relativeFinal d.decode root.val) i.val = 0) := by
  let I := d.inst
  let w : I.Weights := fun j => (q j : ℝ)
  let G := I.highestBidderGraph w
  let sequence (t : ℕ) := ((relativeStep d.decode)^[t]) (relativeOrigin d.decode root.val)
  have next (t : ℕ) : sequence (t + 1) = relativeStep d.decode (sequence t) := by
    simp only [sequence, Function.iterate_succ_apply']
  have invariant (t : ℕ) : RelativeInvariant d q root (sequence t) := by
    induction t with
    | zero => exact relative_origin_invariant d q h root
    | succ t ih =>
      rw [next]
      exact relative_step_invariant d q h root _ ih
  have fold_larger (xs : List ℚ) (a x : ℚ) (hx : x ≤ a ∨ x ∈ xs) : x ≤ xs.foldl max a := by
    induction xs generalizing a with
    | nil => simpa using hx
    | cons y ys ih =>
      rw [List.foldl_cons]
      apply ih
      rcases hx with ha | hm
      · exact Or.inl (ha.trans (le_max_left _ _))
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact Or.inl (le_max_right _ _)
        · exact Or.inr hm
  have keep (t : ℕ) (i : I.Agent) :
      readCell 0 (sequence t) i.val ≤ readCell 0 (sequence (t + 1)) i.val := by
    have hi : i.val < d.decode.agents := i.isLt
    rw [next, relativeStep, read_range _ _ hi]
    exact fold_larger _ _ _ (Or.inl le_rfl)
  have send (t : ℕ) (a b : I.Agent) (g : I.Good) (ha : d.mask a g = true)
      (hb : d.mask b g = true) (hPos : 0 < readCell 0 (sequence t) a.val) :
      0 < readCell 0 (sequence (t + 1)) b.val := by
    let x := relativeCandidate d.decode (sequence t) b.val a.val g.val
    have hx : 0 < x := by
      unfold x relativeCandidate
      rw [mark_at, mark_at, ha, hb, table_at, table_at]
      simpa using div_pos (mul_pos hPos (positive_marked d q h a g ha)) (positive_marked d q h b g hb)
    have hb' : b.val < d.decode.agents := b.isLt
    rw [next, relativeStep, read_range _ _ hb']
    apply hx.trans_le
    apply fold_larger _ _ _ ∘ Or.inr
    apply List.mem_flatMap.mpr
    exact ⟨a.val, List.mem_range.mpr a.isLt,
      List.mem_map.mpr ⟨g.val, List.mem_range.mpr g.isLt, rfl⟩⟩
  let occupied (t : ℕ) (v : I.Agent ⊕ I.Good) : Prop :=
    match v with
    | Sum.inl i => 0 < readCell 0 (sequence t) i.val
    | Sum.inr g => ∀ i : I.Agent, d.mask i g = true → 0 < readCell 0 (sequence t) i.val
  have walk_occupied {a b : I.Agent ⊕ I.Good} (p : G.Walk a b) :
      a = Sum.inl root → occupied p.length b := by
    refine SimpleGraph.Walk.concatRec (motive := fun a b p => a = Sum.inl root → occupied p.length b)
      ?_ ?_ p
    · intro a ha
      subst a
      change 0 < readCell 0 (relativeOrigin d.decode root.val) root.val
      have hRoot : root.val < d.decode.agents := root.isLt
      rw [relativeOrigin, read_range _ _ hRoot]
      norm_num
    · intro a b c p he ih ha
      have old := ih ha
      rw [SimpleGraph.Walk.length_concat]
      cases b with
      | inl j =>
        cases c with
        | inl k => simp [G, Instance.highestBidderGraph] at he
        | inr g =>
          have hj : I.IsHighestBidder w j g := by simpa [G, Instance.highestBidderGraph] using he
          intro k hk
          exact send p.length j k g ((h.2.2 j g).2 hj) hk old
      | inr g =>
        cases c with
        | inl k =>
          have hk : I.IsHighestBidder w k g := by simpa [G, Instance.highestBidderGraph] using he
          exact (old k ((h.2.2 k g).2 hk)).trans_le (keep p.length k)
        | inr g' => simp [G, Instance.highestBidderGraph] at he
  let horizon := I.n + I.m
  have last := (invariant horizon).2 i
  change (d.inst.AgentConnected w root i → readCell 0 (sequence horizon) i.val = q i / q root) ∧
    (¬ d.inst.AgentConnected w root i → readCell 0 (sequence horizon) i.val = 0)
  constructor
  · intro hReach
    obtain ⟨p, hp⟩ := hReach.exists_isPath
    have hLen : p.length ≤ horizon := by
      have hCard := hp.support_nodup.length_le_card
      rw [SimpleGraph.Walk.length_support, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hCard
      dsimp [horizon, I]
      omega
    have initialPos : 0 < readCell 0 (sequence p.length) i.val := walk_occupied p rfl
    have mono : Monotone (fun t => readCell 0 (sequence t) i.val) :=
      monotone_nat_of_le_succ (fun t => keep t i)
    have hPos := initialPos.trans_le (mono hLen)
    rcases last with hZero | good
    · exact False.elim (hPos.ne' hZero)
    · exact good.1
  · intro hReach
    rcases last with hZero | good
    · exact hZero
    · exact False.elim (hReach good.2)

theorem relative_state_width (d : GraphPacket) (q : d.inst.Agent → ℚ)
    (h : ValidMask d q) (root : d.inst.Agent) (rho : List ℚ)
    (hrho : RelativeInvariant d q root rho)
    (height : ∀ i, (q i).num.natAbs ≤ 2 ^ (d.inst.P (valuationBits d.inst)) ∧
      (q i).den ≤ 2 ^ (d.inst.P (valuationBits d.inst))) :
    (listCode ratCode rho).length ≤ 2048 * (d.encode.length + 1)^3 := by
  let N := d.encode.length
  let P := d.inst.P (valuationBits d.inst)
  have hRaw : (encodeInstance d.inst).length ≤ N := by
    simp only [N, GraphPacket.encode, List.length_append]
    omega
  have hDims : d.inst.n + d.inst.m ≤ N := (dimensions_le_binarySize d.inst).trans hRaw
  have hL : valuationBits d.inst ≤ N + 4 :=
    max_le (by omega) (max_le (hDims.trans (Nat.le_add_right _ _)) (hRaw.trans (Nat.le_add_right _ _)))
  have hP : P ≤ 80 * (N + 1)^2 := by
    calc
      P = 16 * (d.inst.n + d.inst.m + 1) * (valuationBits d.inst + 1) := rfl
      _ ≤ 16 * (N + 1) * (5 * (N + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 80 * (N + 1)^2 := by ring
  have ratio_height (i : d.inst.Agent) :
      (q i / q root).num.natAbs ≤ 2 ^ (2 * P) ∧ (q i / q root).den ≤ 2 ^ (2 * P) := by
    have hLeft := RationalBounds.of_rat (2 ^ P) (q i) (h.1 i) (height i).1 (height i).2
    have hRoot := RationalBounds.of_rat (2 ^ P) (q root) (h.1 root) (height root).1 (height root).2
    have product := RationalBounds.mul_ratio hLeft (RationalBounds.inv_ratio hRoot)
    rw [← pow_add, show P + P = 2 * P by omega, ← div_eq_mul_inv, ← Rat.cast_div] at product
    obtain ⟨y, he, _, hnum, hden⟩ := RationalBounds.to_rat _ _ product
    have hRat : q i / q root = y := by exact_mod_cast he
    rw [hRat]
    exact ⟨hnum, hden⟩
  have val_height (x : ℚ) (hx : x ∈ rho) : x.num.natAbs ≤ 2 ^ (2 * P) ∧ x.den ≤ 2 ^ (2 * P) := by
    obtain ⟨j, hj, hval⟩ := List.mem_iff_getElem.mp hx
    let i : d.inst.Agent := ⟨j, by simpa only [hrho.1] using hj⟩
    have hRead : readCell 0 rho i.val = x := by
      change readCell 0 rho j = x
      rw [readCell, List.headD_eq_head?_getD, List.head?_drop, List.getElem?_eq_getElem hj,
        Option.getD_some, hval]
    rcases hrho.2 i with hZero | ⟨hRatio, _⟩
    · rw [hRead] at hZero
      rw [hZero]
      exact ⟨by simp, one_le_pow₀ (by decide)⟩
    · rw [hRead] at hRatio
      rw [hRatio]
      exact ratio_height i
  have hField (x : ℚ) (hx : x ∈ rho) : (ratCode x).length ≤ 6 * P + 10 := by
    have hn := bits_length_mono (val_height x hx).1
    have hd := bits_length_mono (val_height x hx).2
    rw [bits_length_pow2] at hn hd
    simp only [ratCode, intCode, intData, prodCode, pairBits_length, boolCode, List.length_cons, List.length_nil]
    omega
  have hList : (listCode ratCode rho).length ≤ rho.length * (2 * (6 * P + 10) + 2) + 1 := by
    simpa only [List.map_id, id_eq] using listCode_length_map_bound ratCode id rho _ hField
  have hSquare : 1 ≤ (N + 1)^2 := Nat.one_le_of_lt (by positivity)
  have hCell : 2 * (6 * P + 10) + 2 ≤ 1000 * (N + 1)^2 := by nlinarith
  have hWidth : rho.length ≤ N + 1 := by rw [hrho.1]; omega
  have hCube : 1 ≤ (N + 1)^3 := Nat.one_le_of_lt (by positivity)
  calc
    _ ≤ _ := hList
    _ ≤ (N + 1) * (1000 * (N + 1)^2) + 1 := Nat.add_le_add_right (Nat.mul_le_mul hWidth hCell) _
    _ = 1000 * (N + 1)^3 + 1 := by ring
    _ ≤ _ := by
      change 1000 * (N + 1)^3 + 1 ≤ 2048 * (N + 1)^3
      omega

set_option maxHeartbeats 1000000 in
theorem root_scale_correct (d : GraphPacket) (q : d.inst.Agent → ℚ) (h : ValidMask d q)
    (hY : d.inst.IsGreatestFeasible d.inst.cap (fun i => (q i : ℝ))) (root : d.inst.Agent) :
    rootScale d.decode (relativeFinal d.decode root.val) = q root := by
  classical
  let I := d.inst
  let w : I.Weights := fun i => (q i : ℝ)
  let rho := relativeFinal d.decode root.val
  let ratio (i : I.Agent) : ℚ := readCell 0 rho i.val
  let rhoR : I.Weights := fun i => (ratio i : ℝ)
  have sole (i : I.Agent) (g : I.Good) :
      soleBidder d.decode i.val g.val = true ↔ g ∈ I.forcedGoods w i := by
    let rivals := (List.range d.decode.agents).filter
      (fun j => decide (j ≠ i.val) && marked d.decode j g.val)
    change (marked d.decode i.val g.val && rivals.isEmpty) = true ↔ _
    rw [Bool.and_eq_true_iff, mark_at]
    have hEmpty : rivals.isEmpty = true ↔ ∀ j : I.Agent, j ≠ i → d.mask j g ≠ true := by
      constructor
      · intro hE j hj hM
        have he : rivals = [] := by simpa using hE
        have hm : j.val ∈ rivals := by
          apply List.mem_filter.mpr
          exact ⟨List.mem_range.mpr j.isLt,
            Bool.and_eq_true_iff.mpr ⟨decide_eq_true (fun e => hj (Fin.ext e)),
              by rwa [mark_at]⟩⟩
        simpa [he] using hm
      · intro hNone
        cases he : rivals with
        | nil => rfl
        | cons a as =>
          have hm : a ∈ rivals := by rw [he]; exact List.mem_cons_self
          obtain ⟨hm, ht⟩ := List.mem_filter.mp hm
          let j : I.Agent := ⟨a, List.mem_range.mp hm⟩
          obtain ⟨hd, hjm⟩ := Bool.and_eq_true_iff.mp ht
          have hji : j ≠ i := fun e => (of_decide_eq_true hd) (congrArg Fin.val e)
          have hJ : d.mask j g = true := by
            change marked d.decode j.val g.val = true at hjm
            rwa [mark_at] at hjm
          exact False.elim (hNone j hji hJ)
    rw [hEmpty]
    simp only [Instance.forcedGoods, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hi, hr⟩ j hji
      have hig := (h.2.2 i g).mp hi
      refine lt_of_le_of_ne (hig j) (fun e => hr j hji ((h.2.2 j g).mpr ?_))
      intro k
      exact (hig k).trans_eq e.symm
    · intro hi
      have hOwn : I.IsHighestBidder w i g := by
        intro j
        by_cases hj : j = i
        · subst j
          exact le_rfl
        · exact (hi j hj).le
      exact ⟨(h.2.2 i g).mpr hOwn, fun j hj hm =>
        (not_lt_of_ge ((h.2.2 j g).mp hm i)) (hi j hj)⟩
  have utilityQ (i : I.Agent) :
      forcedUtility d.decode i.val = ∑ g ∈ I.forcedGoods w i, I.v i g := by
    let f (g : I.Good) := if g ∈ I.forcedGoods w i then I.v i g else 0
    have congr :
        (List.range d.decode.goods).map (fun g =>
          if soleBidder d.decode i.val g then tableValue d.decode i.val g else 0) = List.ofFn f := by
      apply List.ext_getElem
      · simp [GraphPacket.decode, I]
      · intro n hn hn'
        simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
        let g : I.Good := ⟨n, by simpa [GraphPacket.decode, I] using hn⟩
        change (if soleBidder d.decode i.val g.val = true then tableValue d.decode i.val g.val else 0) = f g
        simp only [table_at, sole, f]
        rfl
    unfold forcedUtility
    rw [congr, List.sum_ofFn]
    classical
    have hFilter : (Finset.univ.filter fun g : I.Good => g ∈ I.forcedGoods w i) =
        I.forcedGoods w i := by ext; simp
    rw [← Finset.sum_filter, hFilter]
  have utilityR (i : I.Agent) :
      (forcedUtility d.decode i.val : ℝ) = I.utility i (I.forcedGoods w i) := by
    rw [utilityQ, Rat.cast_sum]
    rfl
  have uPos (i : I.Agent) (hi : (I.forcedGoods w i).Nonempty) :
      0 < forcedUtility d.decode i.val := by
    rw [utilityQ]
    apply Finset.sum_pos _ hi
    intro g hg
    have hS := (sole i g).mpr hg
    have hM := (Bool.and_eq_true_iff.mp hS).1
    rw [mark_at] at hM
    exact positive_marked d q h i g hM
  have uNonempty (i : I.Agent) (hn : forcedUtility d.decode i.val ≠ 0) :
      (I.forcedGoods w i).Nonempty := by
    by_contra hempty
    have hF := Finset.not_nonempty_iff_eq_empty.mp hempty
    apply hn
    simp [utilityQ, hF]
  have connected (i : I.Agent) (hi : I.AgentConnected w root i) :
      ratio i = q i / q root := (relative_complete d q h root i).1 hi
  have disconnected (i : I.Agent) (hi : ¬ I.AgentConnected w root i) :
      ratio i = 0 := (relative_complete d q h root i).2 hi
  have ratioPos (i : I.Agent) (hi : I.AgentConnected w root i) : 0 < ratio i :=
    (connected i hi).symm ▸ div_pos (h.1 i) (h.1 root)
  have hRel : I.IsRelativeWeight w rhoR root := by
    refine ⟨?_, ?_⟩
    · change (ratio root : ℝ) = 1
      rw [connected root SimpleGraph.Reachable.rfl, div_self (h.1 root).ne']
      norm_num
    · intro i j g hc hi hj
      have e1 : (I.highestBidderGraph w).Adj (Sum.inl i) (Sum.inr g) := by
        simpa [Instance.highestBidderGraph] using hi
      have e2 : (I.highestBidderGraph w).Adj (Sum.inl j) (Sum.inr g) := by
        simpa [Instance.highestBidderGraph] using hj
      have step : I.AgentConnected w i j :=
        ⟨SimpleGraph.Walk.cons e1 (SimpleGraph.Walk.cons e2.symm SimpleGraph.Walk.nil)⟩
      have hV := positive_marked d q h j g ((h.2.2 j g).mpr hj)
      have e := (hi j).antisymm (hj i)
      change (q j : ℝ) * (I.v j g : ℝ) = (q i : ℝ) * (I.v i g : ℝ) at e
      have eQ : q j * I.v j g = q i * I.v i g := by exact_mod_cast e
      have ratioEq : ratio j = ratio i * I.v i g / I.v j g := by
        rw [connected j (hc.trans step), connected i hc]
        apply (eq_div_iff hV.ne').mpr
        simp only [div_mul_eq_mul_div]
        exact congrArg (fun t : ℚ => t / q root) eQ
      change (ratio j : ℝ) = (ratio i : ℝ) * (I.v i g : ℝ) / (I.v j g : ℝ)
      exact_mod_cast ratioEq
  have least := I.component_scale_formula w rhoR h.2.1 hY root hRel
  have getCap (i : I.Agent) (hi : I.AgentConnected w root i) : q root ≤ 4 / ratio i := by
    have hs := least.2 (show I.cap i / rhoR i ∈ I.componentScaleBounds w rhoR root from
      ⟨i, hi, Or.inl rfl⟩)
    change (q root : ℝ) ≤ (4 : ℝ) / (ratio i : ℝ) at hs
    exact_mod_cast hs
  have getSpending (i : I.Agent) (hi : I.AgentConnected w root i)
      (he : (I.forcedGoods w i).Nonempty) :
      q root ≤ 1 / (ratio i * forcedUtility d.decode i.val) := by
    have hs := least.2
      (show (rhoR i * I.utility i (I.forcedGoods w i))⁻¹ ∈ I.componentScaleBounds w rhoR root from
        ⟨i, hi, Or.inr ⟨he, rfl⟩⟩)
    change (q root : ℝ) ≤ ((ratio i : ℝ) * I.utility i (I.forcedGoods w i))⁻¹ at hs
    rw [← utilityR, ← one_div] at hs
    exact_mod_cast hs
  have capRoot : q root ≤ 4 := by
    have hBound : (q root : ℝ) ≤ 4 := hY.1.2.1 root
    exact_mod_cast hBound
  let entry (i : ℕ) : ℚ :=
    let r := readCell 0 rho i
    let u := forcedUtility d.decode i
    if r = 0 then 4 else min (4 / r) (if u = 0 then 4 else 1 / (r * u))
  let entries := (List.range d.decode.agents).map entry
  have foldRule (xs : List ℚ) (a b : ℚ) :
      b ≤ xs.foldl min a ↔ b ≤ a ∧ ∀ x ∈ xs, b ≤ x := by
    induction xs generalizing a with
    | nil => simp
    | cons x xs ih => simp [ih, le_min_iff, and_assoc]
  have entry_eq (i : I.Agent) :
      entry i.val = if ratio i = 0 then 4 else
        min (4 / ratio i) (if forcedUtility d.decode i.val = 0 then 4
          else 1 / (ratio i * forcedUtility d.decode i.val)) := rfl
  change entries.foldl min 4 = q root
  apply le_antisymm
  · obtain ⟨i, hReach, htight⟩ := least.1
    have hMem : entry i.val ∈ entries :=
      List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩
    have hf := ((foldRule entries 4 (entries.foldl min 4)).mp le_rfl).2 _ hMem
    apply hf.trans
    rw [entry_eq, if_neg (ratioPos i hReach).ne']
    rcases htight with he | ⟨hne, he⟩
    · change (q root : ℝ) = 4 / (ratio i : ℝ) at he
      have eqQ : q root = 4 / ratio i := by exact_mod_cast he
      rw [eqQ]
      exact min_le_left _ _
    · change (q root : ℝ) = ((ratio i : ℝ) * I.utility i (I.forcedGoods w i))⁻¹ at he
      rw [← utilityR, ← one_div] at he
      have eqQ : q root = 1 / (ratio i * forcedUtility d.decode i.val) := by exact_mod_cast he
      rw [if_neg (uPos i hne).ne']
      exact (min_le_right _ _).trans_eq eqQ.symm
  · apply (foldRule entries 4 (q root)).mpr
    refine ⟨capRoot, ?_⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    let j : I.Agent := ⟨i, List.mem_range.mp hi⟩
    change q root ≤ entry j.val
    rw [entry_eq]
    by_cases hc : I.AgentConnected w root j
    · rw [if_neg (ratioPos j hc).ne']
      apply le_min (getCap j hc)
      by_cases hz : forcedUtility d.decode j.val = 0
      · rwa [if_pos hz]
      · rw [if_neg hz]
        exact getSpending j hc (uNonempty j hz)
    · rwa [if_pos (disconnected j hc)]

end EF1FPO.WeightWire
