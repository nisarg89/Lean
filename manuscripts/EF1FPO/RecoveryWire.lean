import EF1FPO.InstanceWire
import OAI.Computability.QuantumFactoring.BitStackTabulate
import OAI.Optimization.LinearProgramming.OracleSpec.ArithmeticEncoding
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine

/-! Wire data and owner lookup after a prepared allocation has been rounded. -/

set_option autoImplicit false

namespace EF1FPO.RecoveryWire

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open EF1FPO.InstanceWire
open EF1FPO.PricePacketProcedures (rawNatField decodeNatField)

structure Packet where
  original : Instance
  prepared : Instance
  retained : List ℕ
  owners : List ℕ

def Packet.encode (p : Packet) : Word :=
  encodeInstance p.original ++ encodeInstance p.prepared ++
    encodeNat p.retained.length ++ p.retained.flatMap encodeNat ++
    encodeNat p.prepared.n ++ encodeNat p.owners.length ++ p.owners.flatMap encodeNat

abbrev Owners := ℕ × ℕ × List ℕ × List ℕ

def ownersCode : Owners → Word :=
  prodCode unaryCode (prodCode unaryCode (prodCode (listCode Nat.bits) (listCode Nat.bits)))

def Packet.decode (p : Packet) : Owners :=
  (p.original.n, p.original.m, p.retained, p.owners)

noncomputable def decodePacket : Procedure Packet.encode ownersCode Packet.decode := by
  let ownerRaw (p : Packet) := rawNatField (p.owners.length, p.owners.flatMap encodeNat)
  let allocRaw (p : Packet) := rawNatField (p.prepared.n, ownerRaw p)
  let retainedData (p : Packet) := (p.retained, allocRaw p)
  let retainedRaw (p : Packet) := rawNatField (p.retained.length, rawFields encodeNat (retainedData p))
  let preparedRaw (p : Packet) := encodeInstance p.prepared ++ retainedRaw p
  let keyField (p : Packet) : BoundedNatField :=
    ⟨(p.retained.length, rawFields encodeNat (retainedData p)), by
      have h := natFields_length p.retained
      simp only [rawNatField, retainedData, rawFields, List.length_append]
      omega⟩
  let ownerField (p : Packet) : BoundedNatField :=
    ⟨(p.owners.length, p.owners.flatMap encodeNat), by
      have h := natFields_length p.owners
      simp only [rawNatField, List.length_append]
      omega⟩
  let valsCode := prodCode (listCode ratCode) id
  let dimensions := prodCode unaryCode valsCode
  let readOriginal : Procedure Packet.encode decodedInstanceCode
      (fun p => decodeInstance (p.original, preparedRaw p)) :=
    (decodeInstancePrefix.precompose (fun p : Packet => (p.original, preparedRaw p))).congrEncoding
      (by intro p; simp [Packet.encode, preparedRaw, retainedRaw, retainedData, allocRaw, ownerRaw,
        rawNatField, rawFields, List.append_assoc]) (by intro p; rfl)
  let dimensionsTail := second unaryCode dimensions
  let suffix := (second (listCode ratCode) id).comp ((second unaryCode valsCode).comp dimensionsTail)
  let afterOriginal := suffix.comp readOriginal
  let prepInput : Procedure Packet.encode (fun p : Instance × Word => encodeInstance p.1 ++ p.2)
      (fun p => (p.prepared, retainedRaw p)) :=
    afterOriginal.result (by intro p; rfl)
  let readPrepared := decodeInstancePrefix.comp prepInput
  let afterPrepared := suffix.comp readPrepared
  let keyInput : Procedure Packet.encode (fun p : BoundedNatField => rawNatField p.val) keyField :=
    afterPrepared.result (by intro p; rfl)
  let keyHeader := decodeBoundedNatField.comp keyInput
  let keysInput : Procedure Packet.encode (countedFields encodeNat) retainedData :=
    keyHeader.result (by intro p; rfl)
  let retained := decodeNatFields.comp keysInput
  let retainKeys := (first (listCode Nat.bits) id).comp retained
  let allocInput := ((second (listCode Nat.bits) id).comp retained).result
    (ec := rawNatField) (h := fun p => (p.prepared.n, ownerRaw p)) (by intro p; rfl)
  let ownerHeaderInput : Procedure Packet.encode (fun p : BoundedNatField => rawNatField p.val) ownerField :=
    ((second Nat.bits id).comp (decodeNatField.comp allocInput)).result (by intro p; rfl)
  let ownerHeader := decodeBoundedNatField.comp ownerHeaderInput
  let ownersInput : Procedure Packet.encode (countedFields encodeNat) (fun p => (p.owners, [])) :=
    ownerHeader.result (by intro p; simp [ownerField, countedFields, rawFields])
  let ownerList := (first (listCode Nat.bits) id).comp (decodeNatFields.comp ownersInput)
  let n := (first unaryCode dimensions).comp readOriginal
  let m := (first unaryCode valsCode).comp (dimensionsTail.comp readOriginal)
  exact (n.pair (m.pair (retainKeys.pair ownerList))).congrFun (by intro p; rfl)

def lookupStep (target : ℕ) (state : List ℕ × ℕ) (good : ℕ) : List ℕ × ℕ :=
  (state.1.tail, if good = target then state.1.headD 0 else state.2)

def ownerAt (kept owners : List ℕ) (target : ℕ) : ℕ :=
  (kept.foldl (lookupStep target) (owners, 0)).2

theorem ownerAt_of_getElem {kept owners : List ℕ} {f : ℕ} (hf : f < kept.length)
    (hKept : kept.Nodup) :
    ownerAt kept owners kept[f] = owners[f]?.getD 0 := by
  have no_match (keys : List ℕ) {target : ℕ} (h : target ∉ keys) (state : List ℕ × ℕ) :
      (keys.foldl (lookupStep target) state).2 = state.2 := by
    induction keys generalizing state with
    | nil => rfl
    | cons good keys ih =>
      have hTail : target ∉ keys := fun hmem => h (List.mem_cons_of_mem _ hmem)
      have hHead : good ≠ target := fun he => h (he ▸ List.mem_cons_self)
      rw [List.foldl_cons, ih hTail]
      simp [lookupStep, hHead]
  induction kept generalizing f owners with
  | nil => simp at hf
  | cons good rest ih =>
    have hN := List.nodup_cons.mp hKept
    cases f with
    | zero =>
      change (rest.foldl (lookupStep good) (lookupStep good (owners, 0) good)).2 = _
      rw [no_match rest hN.1]
      cases owners <;> simp [lookupStep]
    | succ f =>
      have hLen : f < rest.length := by simpa using hf
      have hNe : good ≠ rest[f] := fun he => hN.1 (he.symm ▸ List.getElem_mem hLen)
      change (rest.foldl (lookupStep rest[f]) (lookupStep rest[f] (owners, 0) good)).2 = _
      rw [show lookupStep rest[f] (owners, 0) good = (owners.tail, 0) by
        simp [lookupStep, hNe]]
      change ownerAt rest owners.tail rest[f] = _
      rw [ih hLen hN.2]
      cases owners <;> rfl

theorem ownerAt_of_not_mem {kept owners : List ℕ} {g : ℕ} (hg : g ∉ kept) :
    ownerAt kept owners g = 0 := by
  induction kept generalizing owners with
  | nil => rfl
  | cons key rest ih =>
    have hNe : key ≠ g := fun h => hg (h ▸ List.mem_cons_self)
    have hRest : g ∉ rest := fun hm => hg (List.mem_cons_of_mem _ hm)
    simpa [ownerAt, lookupStep, hNe] using ih (owners := owners.tail) hRest

noncomputable def ownerAtProcedure :
    Procedure (prodCode unaryCode (prodCode (listCode Nat.bits) (listCode Nat.bits))) Nat.bits
      (fun p : ℕ × List ℕ × List ℕ => ownerAt p.2.1 p.2.2 p.1) := by
  let rows := listCode Nat.bits
  let context := prodCode rows rows
  let input := prodCode unaryCode context
  let values := prodCode rows Nat.bits
  let state := prodCode Nat.bits values
  let stepInput := prodCode Nat.bits state
  let update (x : ℕ × ℕ × List ℕ × ℕ) : ℕ × List ℕ × ℕ :=
    (x.2.1, lookupStep x.2.1 x.2.2 x.1)
  let g := first Nat.bits state
  let s := second Nat.bits state
  let target := (first Nat.bits values).comp s
  let current := (second Nat.bits values).comp s
  let remaining := (first rows Nat.bits).comp current
  let saved := (second rows Nat.bits).comp current
  let test := OAI.Optimization.LinearProgramming.PriceGame.Control.Native.natEqP.comp (g.pair target)
  let select := conditional test ((listHead Nat.bits 0).comp remaining) saved
  let updateProc : Procedure stepInput state update :=
    (target.pair (((listTail Nat.bits).comp remaining).pair select)).congrFun (by
      intro x
      simp [Function.comp_def, update, lookupStep])
  have step_size (g : ℕ) (s : ℕ × List ℕ × ℕ) : (state (update (g, s))).length ≤ (state s).length := by
    rcases s with ⟨target, owners, last⟩
    have zeroWidth : (Nat.bits 0).length = 0 := rfl
    cases owners <;> by_cases h : g = target <;>
      simp only [state, values, rows, update, lookupStep, h, ite_true, ite_false, List.tail_nil,
        List.tail_cons, List.headD_nil, List.headD_cons, prodCode, pairBits_length,
        listCode_length_cons, zeroWidth] <;> omega
  have width (xs : List ℕ) (start : ℕ × List ℕ × ℕ) :
      (state (xs.foldl (fun a g => update (g, a)) start)).length ≤ (state start).length := by
    induction xs generalizing start with
    | nil => exact le_rfl
    | cons g xs ih =>
      rw [List.foldl_cons]
      exact (ih _).trans (step_size g start)
  let loop := foldList 0 updateProc Polynomial.X (by
    intro xs s i
    rw [Polynomial.eval_X]
    exact (width (xs.take i) s).trans (Nat.le_add_left _ _))
  let index := unaryToBits.comp (first unaryCode context)
  let fields := second unaryCode context
  let kept := (first rows rows).comp fields
  let allocation := (second rows rows).comp fields
  let init := index.pair (allocation.pair (constant input Nat.bits 0))
  let selectOwner := (second rows Nat.bits).comp (second Nat.bits values)
  have unfold_fold (xs owners : List ℕ) (target initial : ℕ) :
      xs.foldl (fun a g => update (g, a)) (target, owners, initial) =
        (target, xs.foldl (lookupStep target) (owners, initial)) := by
    induction xs generalizing owners initial with
    | nil => rfl
    | cons g xs ih =>
      simp only [List.foldl_cons, update]
      exact ih _ _
  exact (selectOwner.comp (loop.comp (kept.pair init))).congrFun (by
    rintro ⟨target, kept, owners⟩
    change (kept.foldl (fun a g => update (g, a)) (target, owners, 0)).2.2 = _
    rw [unfold_fold]
    rfl)

def encodeOwners (d : Owners) : Word :=
  encodeNat d.1 ++ encodeNat d.2.1 ++
    (List.range d.2.1).flatMap (fun g => encodeNat (ownerAt d.2.2.1 d.2.2.2 g))

noncomputable def encodeOwnersProcedure : Procedure ownersCode id encodeOwners := by
  let keys := listCode Nat.bits
  let context := prodCode keys keys
  let bodyCode := prodCode unaryCode context
  let n := first unaryCode bodyCode
  let body := second unaryCode bodyCode
  let m := (first unaryCode context).comp body
  let owners := (second unaryCode context).comp body
  let tab := tabulate (ea := context) (eb := Nat.bits)
    (f := fun p g => ownerAt p.1 p.2 g) 0 ownerAtProcedure
  let cells := tab.comp (m.pair owners)
  let writeList := Wire.flatten.comp (Procedure.listMap (0 : ℕ) ([] : Word) Wire.writeNat)
  let writeN := Wire.writeNat.comp (unaryToBits.comp n)
  let writeM := Wire.writeNat.comp (unaryToBits.comp m)
  let writeOwners := writeList.comp cells
  let output := Procedure.append.comp (writeN.pair (Procedure.append.comp (writeM.pair writeOwners)))
  have flatten_map (f : ℕ → ℕ) (xs : List ℕ) : ((xs.map f).map encodeNat).flatten =
      xs.flatMap (fun g => encodeNat (f g)) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]
  exact output.congrFun (by
    rintro ⟨n, m, keys, owners⟩
    change encodeNat n ++ (encodeNat m ++
      (((List.range m).map (ownerAt keys owners)).map encodeNat).flatten) = _
    rw [flatten_map]
    simp [encodeOwners, List.append_assoc])

end EF1FPO.RecoveryWire
