import EF1FPO.InstanceWire
import EF1FPO.Prices
import EF1FPO.PreparationMatrixWire
import OAI.Optimization.LinearProgramming.PriceGame.MarketInitializeMachine

/-! Exact prices and bidder sets from rationally weighted valuations. -/

set_option autoImplicit false

namespace EF1FPO.RoundData

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame
open EF1FPO.InstanceWire
open EF1FPO.PreparationMatrixWire (readCell unpackRow unpackRows unpackRows_agrees)

structure Packet where
  inst : Instance
  weights : inst.Agent → ℚ

def Packet.encode (d : Packet) : Word :=
  encodeInstance d.inst ++ (List.ofFn d.weights).flatMap encodeRat

abbrev Weighed := ℕ × ℕ × List ℚ × List ℚ

def weighedCode : Weighed → Word :=
  prodCode unaryCode (prodCode unaryCode (prodCode (listCode ratCode) (listCode ratCode)))

def Packet.weighed (d : Packet) : Weighed :=
  (d.inst.n, d.inst.m, (List.ofFn (fun i => List.ofFn (d.inst.v i))).flatten, List.ofFn d.weights)

noncomputable def decode : Procedure Packet.encode weighedCode Packet.weighed := by
  let ratList := listCode ratCode
  let values := prodCode ratList id
  let body := prodCode unaryCode values
  let header (d : Packet) : Instance × Word := (d.inst, (List.ofFn d.weights).flatMap encodeRat)
  let base : Procedure Packet.encode decodedInstanceCode (fun d => decodeInstance (header d)) :=
    (decodeInstancePrefix.precompose header).congrEncoding (by intro d; rfl) (by intro d; rfl)
  let n := (first unaryCode body).comp base
  let m := (first unaryCode values).comp ((second unaryCode body).comp base)
  let remainder := (second unaryCode values).comp ((second unaryCode body).comp base)
  let val := (first ratList id).comp remainder
  let suffix := (second ratList id).comp remainder
  let counted : Procedure Packet.encode (countedFields encodeRat)
      (fun d => (List.ofFn d.weights, [])) :=
    (n.pair suffix).result (by
      intro d
      change prodCode unaryCode id (d.inst.n, (List.ofFn d.weights).flatMap encodeRat) = _
      simp [countedFields, rawFields])
  let readRats := decodeCountedFields encodeRat ratCode (0 : ℚ) PricePacketProcedures.decodeRatField 6
    (by intro q; simp [encodeRat])
    (by
      intro q
      simp only [encodeRat, encodeNat, frame_length, List.length_cons, List.length_append,
        ratCode, intCode, intData, prodCode, pairBits_length, boolCode, List.length_nil]
      omega)
    (by
      intro q
      simp only [encodeRat, encodeNat, frame_length, List.length_cons, List.length_append,
        ratCode, intCode, intData, prodCode, pairBits_length, boolCode, List.length_nil]
      omega)
  let weights := (first ratList id).comp (readRats.comp counted)
  exact (n.pair (m.pair (val.pair weights))).congrFun (by intro d; rfl)

def bidEntry (d : Weighed) (g i : ℕ) : ℚ :=
  readCell 0 d.2.2.2 i * readCell 0 d.2.2.1 (i * d.2.1 + g)

def bidColumn (d : Weighed) (g : ℕ) : List ℚ :=
  (List.range d.1).map (bidEntry d g)

def colPrice (bids : List ℚ) : ℚ := bids.foldl (fun best q => max q best) 0

structure Packed where
  agents : ℕ
  goods : ℕ
  bidders : List (List Bool)
  prices : List ℚ

def packedCode (d : Packed) : Word :=
  prodCode unaryCode (prodCode unaryCode (prodCode (listCode (listCode boolCode)) (listCode ratCode)))
    (d.agents, d.goods, d.bidders, d.prices)

def fromWeighed (d : Weighed) : Packed :=
  let cols := (List.range d.2.1).map (bidColumn d)
  ⟨d.1, d.2.1, cols.map (fun col => col.map (fun q => decide (q = colPrice col))),
    cols.map colPrice⟩

def Packet.pack (d : Packet) : Packed := fromWeighed d.weighed

def marked (d : Packed) (i g : ℕ) : Bool :=
  readCell false (readCell [] d.bidders g) i

def price (d : Packed) (g : ℕ) : ℚ := readCell 0 d.prices g

noncomputable def fromWeighedProcedure : Procedure weighedCode packedCode fromWeighed := by
  let rats := listCode ratCode
  let payload := prodCode rats rats
  let tails := prodCode unaryCode payload
  let n := first unaryCode tails
  let m := (first unaryCode payload).comp (second unaryCode tails)
  let values := (second unaryCode payload).comp (second unaryCode tails)
  let vals := (first rats rats).comp values
  let weights := (second rats rats).comp values
  let context := prodCode Nat.bits weighedCode
  let query := prodCode unaryCode context
  let i := unaryToBits.comp (first unaryCode context)
  let pair := second unaryCode context
  let g := (first Nat.bits weighedCode).comp pair
  let d := (second Nat.bits weighedCode).comp pair
  let width := (unaryToBits.comp m).comp d
  let index := binaryAdd.comp ((binaryMul.comp (i.pair width)).pair g)
  let v := (listGet ratCode 0).comp (index.pair (vals.comp d))
  let a := (listGet ratCode 0).comp (i.pair (weights.comp d))
  let bid : Procedure query ratCode (fun p => bidEntry p.2.2 p.2.1 p.1) :=
    (ratMul.comp (a.pair v)).congrFun (by intro p; rfl)
  let col := Procedure.tabulate (ea := context) (f := fun p => bidEntry p.2 p.1) 0 bid
  let oneQuery := prodCode unaryCode weighedCode
  let one : Procedure oneQuery rats (fun p => bidColumn p.2 p.1) :=
    (col.comp (((n.comp (second unaryCode weighedCode))).pair
      ((unaryToBits.comp (first unaryCode weighedCode)).pair (second unaryCode weighedCode)))).congrFun
        (by intro p; rfl)
  let all := Procedure.tabulate (ea := weighedCode) (f := bidColumn) [] one
  let cols := all.comp (m.pair (identity weighedCode))
  let highest := Market.InitializeMachine.maxP
  let prices := (Procedure.listMap ([] : List ℚ) (0 : ℚ) highest).comp cols
  let test := prodCode ratCode ratCode
  let eqBid : Procedure test boolCode (fun p => decide (p.2 = p.1)) :=
    (boolAnd.comp (Arithmetic.ratLe.pair (Arithmetic.ratLe.comp (swap ratCode ratCode)))).congrFun
      (by
        rintro ⟨p, q⟩
        change (decide (p ≤ q) && decide (q ≤ p)) = decide (q = p)
        by_cases hp : p ≤ q <;> by_cases hq : q ≤ p
        · simp [hp, hq, le_antisymm hq hp]
        · have he : q ≠ p := fun e => hq (e ▸ le_rfl)
          simp [hp, hq, he]
        · have he : q ≠ p := fun e => hp (e ▸ le_rfl)
          simp [hp, hq, he]
        · have he : q ≠ p := fun e => hq (e ▸ le_rfl)
          simp [hp, hq, he])
  let rowMark := Market.GridMachine.mapWithContext (0 : ℚ) false eqBid
  let markCol : Procedure rats (listCode boolCode) (fun row => row.map (fun q => decide (q = colPrice row))) :=
    (rowMark.comp ((identity rats).pair highest)).congrFun (by intro row; rfl)
  let masks := (Procedure.listMap ([] : List ℚ) ([] : List Bool) markCol).comp cols
  exact (n.pair (m.pair (masks.pair prices))).result (by intro p; rfl)

private theorem access {α : Type} (fallback : α) {n i : ℕ} (f : ℕ → α) (hi : i < n) :
    readCell fallback ((List.range n).map f) i = f i := by
  rw [readCell, List.headD_eq_head?_getD, List.head?_drop,
    List.getElem?_eq_getElem (by simpa using hi), Option.getD_some]
  simp

private theorem access_fin {α : Type} (fallback : α) {n : ℕ} (f : Fin n → α) (i : Fin n) :
    readCell fallback (List.ofFn f) i.val = f i := by
  rw [readCell, List.headD_eq_head?_getD, List.head?_drop,
    List.getElem?_eq_getElem (by simpa using i.isLt), Option.getD_some]
  simp

theorem packet_agrees (d : Packet) (hw : d.inst.Positive (fun i => (d.weights i : ℝ))) :
    (∀ g : d.inst.Good, (price d.pack g.val : ℝ) =
      d.inst.price (fun i => (d.weights i : ℝ)) g) ∧
    ∀ (i : d.inst.Agent) (g : d.inst.Good), marked d.pack i.val g.val = true ↔
      d.inst.IsHighestBidder (fun i => (d.weights i : ℝ)) i g := by
  let I := d.inst
  let w : I.Weights := fun i => (d.weights i : ℝ)
  let table := (List.ofFn (fun i : I.Agent => List.ofFn (I.v i))).flatten
  have value (i : I.Agent) (g : I.Good) : readCell 0 table (i.val * I.m + g.val) = I.v i g := by
    have identity : unpackRows (I.n, I.m, table) = List.ofFn (fun i : I.Agent => List.ofFn (I.v i)) :=
      unpackRows_agrees I
    have row := congrArg (fun rs : List (List ℚ) => readCell [] rs i.val) identity
    simp only [unpackRows, access _ _ i.isLt, access_fin] at row
    have col := congrArg (fun xs : List ℚ => readCell 0 xs g.val) row
    simpa only [unpackRow, access _ _ g.isLt, access_fin] using col
  have bid (i : I.Agent) (g : I.Good) : (bidEntry d.weighed g.val i.val : ℝ) = I.bid w i g := by
    change ((readCell 0 (List.ofFn d.weights) i.val *
      readCell 0 table (i.val * I.m + g.val) : ℚ) : ℝ) = I.bid w i g
    rw [access_fin, value, Rat.cast_mul]
    rfl
  have fold_le (xs : List ℚ) (seed : ℚ) (p : ℝ) :
      ((xs.foldl (fun a b => max b a) seed : ℚ) : ℝ) ≤ p ↔
        (seed : ℝ) ≤ p ∧ ∀ a : ℚ, a ∈ xs → (a : ℝ) ≤ p := by
    induction xs generalizing seed with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldl_cons, ih, Rat.cast_max, max_le_iff, List.mem_cons]
      constructor
      · rintro ⟨⟨hx, hs⟩, hTail⟩
        exact ⟨hs, by rintro v (rfl | hv); exact hx; exact hTail v hv⟩
      · rintro ⟨hs, hAll⟩
        exact ⟨⟨hAll _ (Or.inl rfl), hs⟩, fun a ha => hAll a (Or.inr ha)⟩
  have col_eq (g : I.Good) : (colPrice (bidColumn d.weighed g.val) : ℝ) = I.price w g := by
    apply le_antisymm
    · exact (fold_le _ _ _).mpr ⟨by simpa using I.price_nonneg w hw g, by
        intro a ha
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
        let i : I.Agent := ⟨j, List.mem_range.mp hj⟩
        change (bidEntry d.weighed g.val i.val : ℝ) ≤ _
        rw [bid]
        exact I.bid_le_price w i g⟩
    · obtain ⟨i, hi⟩ := I.exists_highest_bidder w g
      rw [← (I.highest_bidder_iff_bid_eq_price w i g).mp hi, ← bid]
      exact ((fold_le _ _ _).mp le_rfl).2 _
        (List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩)
  constructor
  · intro g
    change ((readCell 0 (((List.range I.m).map (bidColumn d.weighed)).map colPrice) g.val : ℚ) : ℝ) = _
    rw [List.map_map, access _ _ g.isLt]
    exact col_eq g
  · intro i g
    change readCell false (readCell []
      (((List.range I.m).map (bidColumn d.weighed)).map
        (fun col => col.map (fun q => decide (q = colPrice col)))) g.val) i.val = true ↔ _
    rw [List.map_map, access _ _ g.isLt]
    change readCell false (((List.range I.n).map (bidEntry d.weighed g.val)).map
      (fun q => decide (q = colPrice (bidColumn d.weighed g.val)))) i.val = true ↔ _
    rw [List.map_map, access _ _ i.isLt]
    simp only [Function.comp_apply, decide_eq_true_eq]
    rw [I.highest_bidder_iff_bid_eq_price w i g, ← bid, ← col_eq]
    exact ⟨fun e => congrArg (fun q : ℚ => (q : ℝ)) e, by intro e; exact_mod_cast e⟩

end EF1FPO.RoundData
