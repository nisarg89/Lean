import EF1FPO.Contraction
import EF1FPO.Geometry
import EF1FPO.Preparation
import EF1FPO.Prices
import EF1FPO.RecoveryWire
import EF1FPO.ProcedureTime
import EF1FPO.PreparationOutputWire
import EF1FPO.WeightProcedure
import EF1FPO.RoundKernel

/-! Uniform binary-time phase contracts following the proof of the main theorem. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.Optimization.LinearProgramming.OracleSpec

def encodePreparation {I : Instance} (P : Preparation I) : Word :=
  encodeInstance P.prepared ++
    encodeNat P.keptCount ++ (List.ofFn (fun g => (P.keptGood g).val)).flatMap encodeNat

def encodeWeights {I : Instance} (q : I.Agent → ℚ) : Word :=
  (List.ofFn q).flatMap encodeRat

abbrev BidderMask (I : Instance) := I.Agent → I.Good → Bool

def encodeBidderMask {I : Instance} (e : BidderMask I) : Word :=
  (List.ofFn (fun i : I.Agent => List.ofFn (e i))).flatten

def IsBidderMask (I : Instance) (e : BidderMask I) (Y : I.Weights) : Prop :=
  ∀ i g, e i g = true ↔ I.IsHighestBidder Y i g

def IsGreatestBidderMask (I : Instance) (e : BidderMask I) : Prop :=
  ∃ Y : I.Weights, I.IsGreatestFeasible I.cap Y ∧ IsBidderMask I e Y

structure PreparedInput where
  original : Instance
  preparation : Preparation original
  valid : preparation.IsPreparation

def PreparedInput.inst (input : PreparedInput) : Instance := input.preparation.prepared

theorem valuationBits_logInputBound (I : Instance) : I.LogInputBound (valuationBits I) := by
  refine ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _), fun i g => ?_⟩
  have encoded_entry_length (q : ℚ) (entries : List ℚ) (hq : q ∈ entries) :
      (encodeRat q).length ≤ (entries.flatMap encodeRat).length := by
    induction entries with
    | nil => simp at hq
    | cons head tail ih =>
      simp only [List.flatMap_cons, List.length_append]
      rcases List.mem_cons.mp hq with rfl | hTail
      · omega
      · have h := ih hTail
        omega
  let entries := (List.ofFn (fun i : I.Agent => List.ofFn (I.v i))).flatten
  let q := I.v i g
  have hEntry : q ∈ entries := List.mem_flatten.mpr
    ⟨List.ofFn (I.v i), List.mem_ofFn.mpr ⟨i, rfl⟩, List.mem_ofFn.mpr ⟨g, rfl⟩⟩
  have hLength := encoded_entry_length q entries hEntry
  have hSize : (entries.flatMap encodeRat).length ≤ valuationBits I := by
    have hLen : (entries.flatMap encodeRat).length ≤ (encodeInstance I).length := by
      simp only [entries, encodeInstance, List.length_append]
      omega
    exact hLen.trans ((le_max_right _ _).trans (le_max_right _ _))
  have h : (encodeRat q).length ≤ valuationBits I := hLength.trans hSize
  simp only [encodeRat, List.length_cons, List.length_append, encodeNat_length] at h
  have hNum : q.num.natAbs.size ≤ valuationBits I := by omega
  have hDen : q.den.size ≤ valuationBits I := by omega
  exact ⟨(Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hNum),
    (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hDen)⟩

theorem prepared_normalized_map_contract (d : PreparedInput) :
    MonotoneContraction (d.inst.normalizedBiasedMap (valuationBits d.inst)) (16 * weightBits d.inst) := by
  let I := d.inst
  let L := valuationBits I
  let b := 16 * weightBits I
  have hRow : ∀ i, I.PositiveRow i := by
    intro i
    obtain ⟨g, hg⟩ := d.preparation.prepared_positive_agents d.valid i
    exact ⟨g, by exact_mod_cast hg⟩
  have hBias : I.bias L = precisionError b := rfl
  have hPow : (0 : ℝ) < 2 ^ b := by positivity
  have hFactor : 0 ≤ 1 - I.bias L := by
    rw [hBias]
    exact sub_nonneg.mpr ((inv_le_one₀ hPow).mpr (one_le_pow₀ (by norm_num)))
  refine ⟨?_, ?_, ?_⟩
  · intro x hx i
    have hInput : x ∈ I.cube 1 := fun j => abs_le.mpr (hx j)
    have hImage := I.normalized_biased_map_cube L (valuationBits_logInputBound I) hRow hInput
    exact abs_le.mp (hImage i)
  · intro x y _ _ hxy i
    let r : ℝ := I.R L
    have hr : 0 ≤ r := Nat.cast_nonneg _
    have hScale : (fun j => r * x j) ≤ fun j => r * y j := fun j =>
      mul_le_mul_of_nonneg_left (hxy j) hr
    have hImage := I.logMap_monotone hScale i
    exact div_le_div_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left hImage hFactor) (le_refl (I.bias L * I.logCap i))) hr
  · intro x y _ _
    have hDist := (I.normalized_biased_map_contraction L hRow).dist_le_mul x y
    rw [Real.coe_toNNReal _ hFactor, hBias] at hDist
    exact hDist

def prepareOutput (I : Instance) (output : Word) : Prop :=
  ∃ P : Preparation I, P.IsPreparation ∧ output = encodePreparation P

namespace PrepareStage

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.PriceGame
open InstanceWire PreparationMatrixWire
open PreparationArithmeticWire (summarize summarizeProcedure)
open PreparationOutputWire (prepareTable encodeTable prepareTableProcedure encodeTableProcedure encode_prepared_agrees)

def output (I : Instance) : Word :=
  let values := (List.ofFn (fun i : I.Agent => List.ofFn (I.v i))).flatten
  let rows := unpackRows (I.n, I.m, values)
  let kept := keptColumns (I.m, rows)
  let entries := (scaledRetainedRows (rows, kept)).flatten
  encodeTable (prepareTable (I.n, kept, summarize entries))

noncomputable def procedure : Procedure encodeInstance id output := by
  let decoded : Procedure encodeInstance decodedInstanceCode (fun I => decodeInstance (I, [])) :=
    (decodeInstancePrefix.precompose (fun I : Instance => (I, []))).congrEncoding
      (by intro I; simp) (by intro I; rfl)
  let flatCode := prodCode (listCode ratCode) id
  let header := prodCode unaryCode flatCode
  let n := (first unaryCode header).comp decoded
  let other := (second unaryCode header).comp decoded
  let m := (first unaryCode flatCode).comp other
  let table := (first (listCode ratCode) id).comp ((second unaryCode flatCode).comp other)
  let rows := unpackRowsProcedure.comp (n.pair (m.pair table))
  let kept := keptColumnsProcedure.comp (m.pair rows)
  let scaled := scaledRetainedRowsProcedure.comp (rows.pair kept)
  let entries := (Learning.GenerationCost.flattenP Nat.bits 0).comp scaled
  let stats := summarizeProcedure.comp entries
  let word := (encodeTableProcedure.comp prepareTableProcedure).comp (n.pair (kept.pair stats))
  exact word.congrFun (by intro I; rfl)

theorem output_correct (I : Instance) : prepareOutput I (output I) := by
  obtain ⟨P, hP⟩ := Preparation.exists_preparation I
  refine ⟨P, hP, ?_⟩
  dsimp only [output]
  rw [unpackRows_agrees I, keptColumns_agrees P hP, scaledRetainedRows_agrees P]
  simpa only [encodePreparation] using encode_prepared_agrees P hP

end PrepareStage

theorem prepare_binary : BitPolynomial encodeInstance prepareOutput := by
  obtain ⟨M, C, degree, hRun⟩ := bitPolynomial_of_procedure PrepareStage.procedure
  refine ⟨M, C, degree, fun I => ?_⟩
  obtain ⟨P, hP, hWord⟩ := PrepareStage.output_correct I
  obtain ⟨time, config, run, clock, stopped, history, output⟩ := hRun I
  exact ⟨time, config, run, clock, stopped, history, P, hP, output.trans hWord⟩

structure LogInput where
  q : ℚ
  positive : 0 < q
  precision : ℕ

def encodeLogInput (d : LogInput) : Word := encodeRat d.q ++ encodeUnary d.precision

def logOutput (d : LogInput) (output : Word) : Prop :=
  ∃ approximate : ℚ,
    |(approximate : ℝ) - Real.log (d.q : ℝ)| ≤ precisionError d.precision ∧
    output = encodeRat approximate

structure EvaluationInput where
  prepared : PreparedInput
  inputPrecision : ℕ
  precision : ℕ
  numerator : GridNumerator prepared.inst.n
  inCube : unitCube (dyadicPoint inputPrecision numerator)

def EvaluationInput.encode (d : EvaluationInput) : Word :=
  frame (encodeInstance d.prepared.inst) ++ dyadicQuery d.inputPrecision d.precision d.numerator

def EvaluationInput.output (d : EvaluationInput) (bits : Word) : Prop :=
  let I := d.prepared.inst
  ∃ q : GridNumerator I.n,
    unitCube (dyadicPoint d.precision q) ∧
    dist (dyadicPoint d.precision q)
      (I.normalizedBiasedMap (valuationBits I) (dyadicPoint d.inputPrecision d.numerator)) ≤
        precisionError d.precision ∧ bits = encodeGrid q

/-- The biased fixed-point driver supplies the scaled real error used for exact tie recovery. -/
def approximateOutput (d : PreparedInput) (bits : Word) : Prop :=
  let I := d.inst
  let f := I.normalizedBiasedMap (valuationBits I)
  ∃ (s : ℕ) (q : GridNumerator I.n) (v : Vector I.n),
    unitCube (dyadicPoint s q) ∧ unitCube v ∧ f v = v ∧
    (∀ i, |(logRadius I : ℝ) * (dyadicPoint s q i - v i)| ≤ precisionError (8 * weightBits I)) ∧
    bits = encodeUnary s ++ encodeGrid q

structure GreatestGraphInput where
  prepared : PreparedInput
  graph : BidderMask prepared.inst
  greatest : IsGreatestBidderMask prepared.inst graph

def GreatestGraphInput.encode (d : GreatestGraphInput) : Word :=
  encodeInstance d.prepared.inst ++ encodeBidderMask d.graph

namespace GreatestWeightStage

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec

def packet (d : GreatestGraphInput) : WeightWire.GraphPacket := ⟨d.prepared.inst, d.graph⟩

def output (d : GreatestGraphInput) : Word :=
  (WeightProcedure.vectorOutput (packet d)).flatMap encodeRat

private theorem actual_data (d : GreatestGraphInput) :
    ∃ q : d.prepared.inst.Agent → ℚ, WeightWire.ValidMask (packet d) q ∧
      d.prepared.inst.IsGreatestFeasible d.prepared.inst.cap (fun i => (q i : ℝ)) ∧
      ∀ i, (q i).num.natAbs ≤ 2 ^ (d.prepared.inst.P (valuationBits d.prepared.inst)) ∧
        (q i).den ≤ 2 ^ (d.prepared.inst.P (valuationBits d.prepared.inst)) := by
  let I := d.prepared.inst
  obtain ⟨Y, hY, hMask⟩ := d.greatest
  have hCols : I.PositiveColumns := by
    intro g
    obtain ⟨i, hg⟩ := d.prepared.preparation.prepared_positive_goods d.prepared.valid g
    exact ⟨i, by exact_mod_cast hg⟩
  have hh := I.weight_height_of_greatest (valuationBits I)
    (valuationBits_logInputBound I) hCols Y hY
  choose q hq using hh
  have eqY : (fun i : I.Agent => (q i : ℝ)) = Y := funext (fun i => (hq i).1.symm)
  have valid : WeightWire.ValidMask (packet d) q := by
    refine ⟨fun i => (hq i).2.1, hCols, ?_⟩
    intro i g
    change (d.graph i g = true ↔ I.IsHighestBidder (fun j => (q j : ℝ)) i g)
    rw [eqY]
    exact hMask i g
  have greatest : (packet d).inst.IsGreatestFeasible (packet d).inst.cap (fun i => (q i : ℝ)) := by
    change I.IsGreatestFeasible I.cap (fun i => (q i : ℝ))
    rwa [eqY]
  exact ⟨q, valid, greatest, fun i => (hq i).2.2⟩

private noncomputable def exactGraph (d : GreatestGraphInput) : WeightProcedure.ExactGraph :=
  let h := Classical.choose_spec (actual_data d)
  ⟨packet d, Classical.choose (actual_data d), h.1, h.2.1, h.2.2⟩

noncomputable def procedure : Procedure GreatestGraphInput.encode id output := by
  let native := WeightProcedure.recoverVectorProcedure.precompose exactGraph
  let physical := Wire.flatten.comp (Procedure.listMap (0 : ℚ) ([] : Word) Wire.writeRat)
  have serialization (xs : List ℚ) : (xs.map encodeRat).flatten = xs.flatMap encodeRat := by
    induction xs with
    | nil => rfl
    | cons q qs ih => simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]
  let body := (physical.comp native).congrEncoding (ec := GreatestGraphInput.encode) (by intro d; rfl)
    (by intro d; rfl)
  exact body.congrFun (by
    intro d
    change ((WeightProcedure.vectorOutput (packet d)).map encodeRat).flatten =
      (WeightProcedure.vectorOutput (packet d)).flatMap encodeRat
    exact serialization _)

theorem output_correct (d : GreatestGraphInput) :
    ∃ q : d.prepared.inst.Agent → ℚ,
      d.prepared.inst.IsGreatestFeasible d.prepared.inst.cap (fun i => (q i : ℝ)) ∧
      output d = encodeWeights q := by
  let data := exactGraph d
  refine ⟨data.weights, data.greatest, ?_⟩
  exact congrArg (fun xs : List ℚ => xs.flatMap encodeRat) (WeightProcedure.vectorOutput_correct data)

end GreatestWeightStage

theorem recover_greatest_weights_binary : BitPolynomial GreatestGraphInput.encode (fun d bits =>
    ∃ q : d.prepared.inst.Agent → ℚ,
      d.prepared.inst.IsGreatestFeasible d.prepared.inst.cap (fun i => (q i : ℝ)) ∧
      bits = encodeWeights q) := by
  obtain ⟨M, C, degree, hRun⟩ := bitPolynomial_of_procedure GreatestWeightStage.procedure
  refine ⟨M, C, degree, fun d => ?_⟩
  obtain ⟨q, hGreatest, hWord⟩ := GreatestWeightStage.output_correct d
  obtain ⟨time, config, run, clock, stopped, history, output⟩ := hRun d
  exact ⟨time, config, run, clock, stopped, history, q, hGreatest, output.trans hWord⟩

structure RoundingInput where
  prepared : PreparedInput
  weights : prepared.inst.Agent → ℚ
  greatest : prepared.inst.IsGreatestFeasible prepared.inst.cap (fun i => (weights i : ℝ))

def RoundingInput.encode (d : RoundingInput) : Word :=
  encodeInstance d.prepared.inst ++ encodeWeights d.weights

namespace RoundStage

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec

def packet (d : RoundingInput) : RoundData.Packet := ⟨d.prepared.inst, d.weights⟩

def output (d : RoundingInput) : Word :=
  RoundKernel.emit (packet d).pack (RoundKernel.roundOwners (packet d).pack)

private theorem ready (d : RoundingInput) :
    let I := d.prepared.inst
    let w := fun i : I.Agent => (d.weights i : ℝ)
    I.Positive w ∧ I.IsForest w ∧ I.Covers w ∧ I.ForcedFeasible w := by
  let I := d.prepared.inst
  let w := fun i : I.Agent => (d.weights i : ℝ)
  have hw : I.Positive w := d.greatest.1.1
  have hFor : I.IsForest w := d.prepared.preparation.prepared_forest d.prepared.valid w hw
  have capPos : I.Positive I.cap := by intro i; norm_num [Instance.cap]
  obtain ⟨u, hu, hCover, _⟩ := I.greatest_weights I.cap capPos
    (d.prepared.preparation.prepared_cap_covers d.prepared.valid)
  have eqW : u = w := le_antisymm (d.greatest.2 hu.1) (hu.2 d.greatest.1)
  have coverW : I.Covers w := Eq.mp (congrArg (fun z : I.Weights => I.Covers z) eqW) hCover
  exact ⟨hw, hFor, coverW, d.greatest.1.2.2⟩

noncomputable def procedure :
    Procedure RoundingInput.encode id output :=
  (((RoundKernel.roundProcedure.comp RoundData.fromWeighedProcedure).comp RoundData.decode).precompose packet).congrEncoding
    (by intro d; rfl) (by intro d; rfl)

theorem output_correct (d : RoundingInput) :
    ∃ A : d.prepared.inst.Allocation,
      d.prepared.inst.IsSupported (fun i => (d.weights i : ℝ)) A ∧
      d.prepared.inst.Bands (fun i => (d.weights i : ℝ)) A 1 ∧ output d = encodeAllocation A := by
  obtain ⟨hw, hForest, hCover, hForced⟩ := ready d
  exact RoundKernel.round_correct (packet d) hw hForest hCover hForced

end RoundStage

theorem round_on_forest_binary : BitPolynomial RoundingInput.encode (fun d bits =>
    ∃ A : d.prepared.inst.Allocation,
      d.prepared.inst.IsSupported (fun i => (d.weights i : ℝ)) A ∧
      d.prepared.inst.Bands (fun i => (d.weights i : ℝ)) A 1 ∧ bits = encodeAllocation A) := by
  obtain ⟨M, C, degree, hRun⟩ := bitPolynomial_of_procedure RoundStage.procedure
  refine ⟨M, C, degree, fun d => ?_⟩
  obtain ⟨A, hSupported, hBands, hWord⟩ := RoundStage.output_correct d
  obtain ⟨time, config, run, clock, stopped, history, output⟩ := hRun d
  exact ⟨time, config, run, clock, stopped, history, A, hSupported, hBands, output.trans hWord⟩

structure RecoveryInput where
  prepared : PreparedInput
  allocation : prepared.inst.Allocation
  ef1 : prepared.inst.IsEF1 allocation
  supported : ∃ w : prepared.inst.Weights,
    prepared.inst.Positive w ∧ prepared.inst.IsSupported w allocation

def RecoveryInput.encode (d : RecoveryInput) : Word :=
  encodeInstance d.prepared.original ++ encodePreparation d.prepared.preparation ++
    encodeAllocation d.allocation

namespace ReturnStage

def packet (d : RecoveryInput) : RecoveryWire.Packet :=
  ⟨d.prepared.original, d.prepared.inst,
    List.ofFn (fun k => (d.prepared.preparation.keptGood k).val),
    List.ofFn (fun g : d.prepared.inst.Good => (d.allocation g).val)⟩

def output (d : RecoveryInput) : Word := RecoveryWire.encodeOwners (RecoveryWire.Packet.decode (packet d))

noncomputable def procedure :
    OAI.ExactQuantumFactoring.BitStackProgram.Procedure RecoveryInput.encode id output :=
  ((RecoveryWire.encodeOwnersProcedure.comp RecoveryWire.decodePacket).precompose packet).congrEncoding
    (by intro d; simp [RecoveryInput.encode, RecoveryWire.Packet.encode, encodePreparation,
      encodeAllocation, packet, PreparedInput.inst, List.append_assoc]) (by intro d; rfl)

theorem output_correct (d : RecoveryInput) :
    ∃ A : d.prepared.original.Allocation,
      d.prepared.preparation.IsRecoveredAllocation d.allocation A ∧
      d.prepared.original.IsEF1 A ∧
      (∃ q : d.prepared.original.Agent → ℚ,
        d.prepared.original.Positive (fun i => (q i : ℝ)) ∧
        d.prepared.original.IsSupported (fun i => (q i : ℝ)) A) ∧
      output d = encodeAllocation A := by
  classical
  let I := d.prepared.original
  let P := d.prepared.preparation
  have hP : P.IsPreparation := d.prepared.valid
  obtain ⟨w, hw, hSup⟩ := d.supported
  obtain ⟨A, q, hA, hf, hPos, hBid⟩ := P.recover_allocation hP d.allocation d.ef1 w hw hSup
  let kept := (packet d).retained
  let owners := (packet d).owners
  have hNodup : kept.Nodup := by
    apply List.nodup_ofFn_ofInjective
    intro a b heq
    exact hP.1.injective (Fin.ext heq)
  have hMatch (g : I.Good) : RecoveryWire.ownerAt kept owners g.val = (A g).val := by
    by_cases hg : ∃ k, P.keptGood k = g
    · obtain ⟨k, rfl⟩ := hg
      have hk : k.val < kept.length := by simpa only [kept, packet, List.length_ofFn] using k.isLt
      have hKey : kept[k.val] = (P.keptGood k).val := by
        simp only [kept, packet, List.getElem_ofFn] <;> rfl
      have hOwner : k.val < owners.length := by
        simp only [owners, packet, List.length_ofFn]
        change k.val < P.keptCount + I.n
        exact k.isLt.trans_le (Nat.le_add_right _ _)
      have hVal : owners[k.val]?.getD 0 = (d.allocation (P.originalColumn k)).val := by
        rw [List.getElem?_eq_getElem hOwner]
        simp only [owners, packet, List.getElem_ofFn, Option.getD_some] <;> rfl
      calc
        _ = RecoveryWire.ownerAt kept owners kept[k.val] := by rw [hKey]
        _ = owners[k.val]?.getD 0 := RecoveryWire.ownerAt_of_getElem hk hNodup
        _ = (d.allocation (P.originalColumn k)).val := hVal
        _ = (A (P.keptGood k)).val := congrArg Fin.val (hA.1 k).symm
    · have absent : g.val ∉ kept := by
        intro hg'
        obtain ⟨k, he⟩ := List.mem_ofFn.mp hg'
        exact hg ⟨k, Fin.ext he⟩
      have hZero (i : I.Agent) : I.v i g = 0 :=
        le_antisymm (le_of_not_gt (fun hi => hg ((hP.2.1 g).2 ⟨i, hi⟩))) (I.nonneg i g)
      rw [RecoveryWire.ownerAt_of_not_mem absent, hA.2 g hZero]
  have hList : (List.range I.m).map (RecoveryWire.ownerAt kept owners) =
      List.ofFn (fun g : I.Good => (A g).val) := by
    apply List.ext_getElem
    · simp
    · intro j _ hj
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      exact hMatch ⟨j, by simpa only [List.length_ofFn] using hj⟩
  have hWord : output d = encodeAllocation A := by
    have hFields := congrArg (fun xs : List ℕ => xs.flatMap encodeNat) hList
    simp only [List.flatMap_map, Function.comp_apply] at hFields
    unfold output
    change encodeNat I.n ++ encodeNat I.m ++
      ((List.range I.m).flatMap fun g => encodeNat (RecoveryWire.ownerAt kept owners g)) = _
    rw [hFields]
    rfl
  exact ⟨A, hA, hf, ⟨q, hPos, hBid⟩, hWord⟩

end ReturnStage

theorem recover_allocation_binary : BitPolynomial RecoveryInput.encode (fun d bits =>
    ∃ A : d.prepared.original.Allocation,
      d.prepared.preparation.IsRecoveredAllocation d.allocation A ∧
      d.prepared.original.IsEF1 A ∧
      (∃ q : d.prepared.original.Agent → ℚ,
        d.prepared.original.Positive (fun i => (q i : ℝ)) ∧
        d.prepared.original.IsSupported (fun i => (q i : ℝ)) A) ∧
      bits = encodeAllocation A) := by
  obtain ⟨M, C, degree, hRun⟩ := bitPolynomial_of_procedure ReturnStage.procedure
  refine ⟨M, C, degree, fun d => ?_⟩
  obtain ⟨A, hA, hf, hSupport, hWord⟩ := ReturnStage.output_correct d
  obtain ⟨t, config, run, clock, stopped, history, output⟩ := hRun d
  exact ⟨t, config, run, clock, stopped, history, A, hA, hf, hSupport, output.trans hWord⟩

end EF1FPO
