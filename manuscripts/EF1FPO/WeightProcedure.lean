import EF1FPO.WeightWire

/-! Dimension-uniform iteration and enumeration for exact reconstructed weights. -/

set_option autoImplicit false

namespace EF1FPO.WeightProcedure

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame
open EF1FPO.WeightWire EF1FPO.InstanceWire
open EF1FPO.PricePacketProcedures (rawNatField)

structure ExactGraph where
  graph : GraphPacket
  weights : graph.inst.Agent → ℚ
  valid : ValidMask graph weights
  greatest : graph.inst.IsGreatestFeasible graph.inst.cap (fun i => (weights i : ℝ))
  height : ∀ i, (weights i).num.natAbs ≤ 2 ^ (graph.inst.P (valuationBits graph.inst)) ∧
    (weights i).den ≤ 2 ^ (graph.inst.P (valuationBits graph.inst))

def ExactGraph.encode (d : ExactGraph) : Word := d.graph.encode

structure RootInput where
  data : ExactGraph
  root : data.graph.inst.Agent

def RootInput.encode (p : RootInput) : Word :=
  prodCode unaryCode GraphPacket.encode (p.root.val, p.data.graph)

def rootOutput (p : RootInput) : ℚ :=
  rootScale p.data.graph.decode (relativeFinal p.data.graph.decode p.root.val)

noncomputable def recoverRootProcedure : Procedure RootInput.encode ratCode rootOutput := by
  let rats := listCode ratCode
  let rawState := prodCode RootInput.encode rats
  let Valid := {s : RootInput × List ℚ //
    RelativeInvariant s.1.data.graph s.1.data.weights s.1.root s.2}
  let stateCode (s : Valid) := rawState s.val
  let advance (s : Valid) : Valid :=
    ⟨(s.val.1, relativeStep s.val.1.data.graph.decode s.val.2),
      relative_step_invariant _ _ s.val.1.data.valid _ _ s.property⟩
  let packet := (second unaryCode GraphPacket.encode).precompose
    (fun p : RootInput => (p.root.val, p.data.graph))
  let parse : Procedure RootInput.encode packedCode (fun p => p.data.graph.decode) :=
    (decodeGraph.comp packet).congrFun (by intro p; rfl)
  let saved := first RootInput.encode rats
  let values := second RootInput.encode rats
  let stepped := relativeStepProcedure.comp ((parse.comp saved).pair values)
  let step : Procedure stateCode stateCode advance :=
    ((saved.pair stepped).precompose (fun p : Valid => p.val)).result (by intro p; rfl)
  let tupleCode := prodCode unaryCode (prodCode unaryCode (prodCode (listCode ratCode) (listCode boolCode)))
  let tuple := parse.result (ec := tupleCode)
    (h := fun p => (p.data.graph.inst.n, p.data.graph.inst.m, p.data.graph.decode.valuations, p.data.graph.decode.mask))
    (by intro p; rfl)
  let tailCode := prodCode unaryCode (prodCode (listCode ratCode) (listCode boolCode))
  let n := (first unaryCode tailCode).comp tuple
  let m := (first unaryCode (prodCode (listCode ratCode) (listCode boolCode))).comp
    ((second unaryCode tailCode).comp tuple)
  let root := (first unaryCode GraphPacket.encode).precompose
    (fun p : RootInput => (p.root.val, p.data.graph))
  let query := prodCode unaryCode Nat.bits
  let matchRoot := Control.Native.natEqP.comp
    ((unaryToBits.comp (first unaryCode Nat.bits)).pair (second unaryCode Nat.bits))
  let atRoot : Procedure query ratCode (fun p => if p.1 = p.2 then 1 else 0) :=
    (conditional matchRoot (constant query ratCode 1) (constant query ratCode 0)).congrFun (by intro p; simp)
  let all := tabulate (ea := Nat.bits) (eb := ratCode) (f := fun r i => if i = r then 1 else 0) 0 atRoot
  let initialRatios := all.comp (n.pair (unaryToBits.comp root))
  let startVal (p : RootInput) : Valid :=
    ⟨(p, relativeOrigin p.data.graph.decode p.root.val), relative_origin_invariant _ _ p.data.valid _⟩
  let start : Procedure RootInput.encode stateCode startVal :=
    ((identity RootInput.encode).pair initialRatios).result (by intro p; rfl)
  have unchanged (s : Valid) (t : ℕ) : ((advance^[t]) s).val.1 = s.val.1 := by
    induction t with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply']; exact ih
  have scanned (s : Valid) (t : ℕ) : ((advance^[t]) s).val.2 =
      (relativeStep s.val.1.data.graph.decode)^[t] s.val.2 := by
    induction t with
    | zero => rfl
    | succ j ih =>
      simp only [Function.iterate_succ_apply']
      change relativeStep ((advance^[j]) s).val.1.data.graph.decode ((advance^[j]) s).val.2 = _
      rw [unchanged, ih]
  let width : Polynomial ℕ := Polynomial.C 4096 * (Polynomial.X + 1)^3
  let loop := step.iterate width (by
    intro count s t _
    let L := count + (stateCode s).length
    let out := (advance^[t]) s
    have hRawLen : s.val.1.data.graph.encode.length ≤ (RootInput.encode s.val.1).length := by
      simp only [RootInput.encode, prodCode, pairBits_length, unaryCode, List.length_replicate]
      omega
    have hDataLen : (RootInput.encode s.val.1).length ≤ L := by
      simp only [L, stateCode, rawState, prodCode, pairBits_length]
      omega
    have hGraph : out.val.1.data.graph.encode.length ≤ L := by
      rw [show out.val.1 = s.val.1 from unchanged s t]
      exact hRawLen.trans hDataLen
    have hRatLen : (rats out.val.2).length ≤ 2048 * (L + 1)^3 := by
      exact (relative_state_width _ _ out.val.1.data.valid _ _ out.property out.val.1.data.height).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hGraph 1) _))
    have hCube : L + 1 ≤ (L + 1)^3 := by
      simpa only [pow_one] using (Nat.pow_le_pow_right (show 0 < L + 1 by omega) (show 1 ≤ 3 by decide))
    change (stateCode out).length ≤ width.eval L
    simp only [stateCode, rawState, prodCode, pairBits_length, width, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    rw [show out.val.1 = s.val.1 from unchanged s t]
    omega)
  let count := unaryAdd.comp (n.pair m)
  let final := loop.comp (count.pair start)
  let finalGraph := (parse.comp saved).precompose (fun p : Valid => p.val)
  let finalRatios := values.precompose (fun p : Valid => p.val)
  let calculated := rootScaleProcedure.comp (finalGraph.pair finalRatios)
  exact (calculated.comp final).congrFun (by
    intro p
    let horizon := p.data.graph.inst.n + p.data.graph.inst.m
    let out := (advance^[horizon]) (startVal p)
    change rootScale out.val.1.data.graph.decode out.val.2 = rootOutput p
    rw [show out.val.1 = p from unchanged (startVal p) horizon]
    rw [show out.val.2 = ((relativeStep p.data.graph.decode)^[horizon])
        (relativeOrigin p.data.graph.decode p.root.val) from scanned (startVal p) horizon]
    rfl)

def vectorOutput (d : GraphPacket) : List ℚ :=
  (List.range d.inst.n).map (fun i => rootScale d.decode (relativeFinal d.decode i))

noncomputable def recoverVectorProcedure : Procedure ExactGraph.encode (listCode ratCode)
    (fun d => vectorOutput d.graph) := by
  let graph : Procedure ExactGraph.encode packedCode (fun d => d.graph.decode) :=
    decodeGraph.precompose (fun d : ExactGraph => d.graph)
  let rows := prodCode unaryCode (prodCode (listCode ratCode) (listCode boolCode))
  let counts := graph.result (ec := prodCode unaryCode rows)
    (h := fun d => (d.graph.inst.n, d.graph.inst.m, d.graph.decode.valuations, d.graph.decode.mask))
    (by intro p; rfl)
  let n := (first unaryCode rows).comp counts
  let packet := prodCode unaryCode ExactGraph.encode
  let query := first unaryCode ExactGraph.encode
  let data := second unaryCode ExactGraph.encode
  let job (p : ℕ × ExactGraph) : RootInput :=
    ⟨p.2, ⟨p.1 % p.2.graph.inst.n, Nat.mod_lt _ p.2.graph.inst.hn⟩⟩
  let bounded (p : ℕ × ExactGraph) : BoundedNatField :=
    ⟨((job p).root.val, p.2.encode), by
      have hRaw : (encodeInstance p.2.graph.inst).length ≤ p.2.encode.length := by
        simp only [ExactGraph.encode, GraphPacket.encode, List.length_append]
        omega
      have hDims := (dimensions_le_binarySize p.2.graph.inst).trans hRaw
      have hIndex : (job p).root.val < p.2.graph.inst.n := (job p).root.isLt
      change (job p).root.val ≤ (encodeNat (job p).root.val ++ p.2.encode).length
      simp only [List.length_append]
      omega⟩
  let reduced := binaryMod.comp ((unaryToBits.comp query).pair ((unaryToBits.comp n).comp data))
  let rawData := data.result (ec := id) (h := fun p : ℕ × ExactGraph => p.2.encode) (by intro p; rfl)
  let glued := Procedure.append.comp ((Wire.writeNat.comp reduced).pair rawData)
  let field : Procedure packet (fun f : BoundedNatField => rawNatField f.val) bounded :=
    glued.result (by intro p; rfl)
  let idx := decodeBoundedNatField.comp field
  let rootInput : Procedure packet RootInput.encode job := idx.result (by intro p; rfl)
  let one := recoverRootProcedure.comp rootInput
  let all := Procedure.tabulate (ea := ExactGraph.encode) (f := fun d i => rootOutput (job (i, d))) 0 one
  exact (all.comp (n.pair (identity ExactGraph.encode))).congrFun (by
    intro d
    change (List.range d.graph.inst.n).map (fun i => rootOutput (job (i, d))) = vectorOutput d.graph
    unfold vectorOutput
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    simp only [job, rootOutput, Nat.mod_eq_of_lt hi'])

theorem vectorOutput_correct (d : ExactGraph) : vectorOutput d.graph = List.ofFn d.weights := by
  apply List.ext_getElem
  · simp [vectorOutput]
  · intro i hi hj
    let root : d.graph.inst.Agent := ⟨i, by simpa [vectorOutput] using hi⟩
    simp only [vectorOutput, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    exact root_scale_correct d.graph d.weights d.valid d.greatest root

end EF1FPO.WeightProcedure
