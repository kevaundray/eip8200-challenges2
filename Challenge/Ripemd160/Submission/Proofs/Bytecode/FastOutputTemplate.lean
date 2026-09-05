import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate
import Challenge.EvmProof.Meter
import YulEvmCompiler.Instr

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# H31 fast-output helper template

This is the primary minimal-mask helper only.  It loads five arbitrary EVM
words, appends four 32-bit shifts, applies the two dense byte-order stages,
stores at memory offset zero, and returns 32 bytes.  Canonical 32-bit input
conditions belong to a later mathematical specification layer; this template
and its raw trace have no such premise.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputTemplate

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate

def push0 : Instr := .push ⟨0, by decide⟩ ⟨0⟩

def push30 (value : UInt256) : Instr :=
  .push ⟨30, by decide⟩ value

def push31 (value : UInt256) : Instr :=
  .push ⟨31, by decide⟩ value

abbrev mask8 : UInt256 := DenseScheduleTemplate.mask8
abbrev mask16 : UInt256 := DenseScheduleTemplate.mask16

def packAppend (acc word : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.shiftLeft acc (UInt256.ofNat 32)) word

/-- The raw effect of the four `SHL 32; OR` append steps. -/
def packWords (word0 word1 word2 word3 word4 : UInt256) : UInt256 :=
  packAppend (packAppend (packAppend (packAppend word0 word1) word2) word3) word4

def fastLoad0 : List Instr :=
  [DenseScheduleTemplate.push1 (UInt256.ofNat 32), DenseScheduleTemplate.op .MLOAD]

def fastPackStep (address : Nat) : List Instr :=
  [DenseScheduleTemplate.push1 (UInt256.ofNat 32), DenseScheduleTemplate.op .SHL,
   DenseScheduleTemplate.push1 (UInt256.ofNat address), DenseScheduleTemplate.op .MLOAD,
   DenseScheduleTemplate.op .OR]

def fastPackTemplate : List Instr :=
  [DenseScheduleTemplate.op .JUMPDEST] ++ fastLoad0 ++
    fastPackStep 64 ++ fastPackStep 96 ++ fastPackStep 128 ++ fastPackStep 160

def fastEndianStage8 : List Instr :=
  [DenseScheduleTemplate.dup1,
   DenseScheduleTemplate.push1 (UInt256.ofNat 8), DenseScheduleTemplate.op .SHR,
   push31 mask8, DenseScheduleTemplate.op .AND,
   DenseScheduleTemplate.swap1, push31 mask8, DenseScheduleTemplate.op .AND,
   DenseScheduleTemplate.push1 (UInt256.ofNat 8), DenseScheduleTemplate.op .SHL,
   DenseScheduleTemplate.op .OR]

def fastEndianStage16 : List Instr :=
  [DenseScheduleTemplate.dup1,
   DenseScheduleTemplate.push1 (UInt256.ofNat 16), DenseScheduleTemplate.op .SHR,
   push30 mask16, DenseScheduleTemplate.op .AND,
   DenseScheduleTemplate.swap1, push30 mask16, DenseScheduleTemplate.op .AND,
   DenseScheduleTemplate.push1 (UInt256.ofNat 16), DenseScheduleTemplate.op .SHL,
   DenseScheduleTemplate.op .OR]

def fastStoreAndSetup : List Instr :=
  [push0, DenseScheduleTemplate.op .MSTORE,
   DenseScheduleTemplate.push1 (UInt256.ofNat 32), push0]

def fastOutputBeforeReturnTemplate : List Instr :=
  fastPackTemplate ++ fastEndianStage8 ++ fastEndianStage16 ++ fastStoreAndSetup

def fastOutputReturnTemplate : List Instr :=
  [DenseScheduleTemplate.op .RETURN]

def fastOutputTemplate : List Instr :=
  fastOutputBeforeReturnTemplate ++ fastOutputReturnTemplate

@[simp] theorem fastLoad0_length : fastLoad0.length = 2 := by
  rfl

@[simp] theorem fastPackStep_length (address : Nat) :
    (fastPackStep address).length = 5 := by
  rfl

@[simp] theorem fastPackTemplate_length : fastPackTemplate.length = 23 := by
  rfl

@[simp] theorem fastEndianStage8_length : fastEndianStage8.length = 11 := by
  rfl

@[simp] theorem fastEndianStage16_length : fastEndianStage16.length = 11 := by
  rfl

@[simp] theorem fastStoreAndSetup_length : fastStoreAndSetup.length = 4 := by
  rfl

@[simp] theorem fastOutputBeforeReturnTemplate_length :
    fastOutputBeforeReturnTemplate.length = 49 := by
  rfl

@[simp] theorem fastOutputReturnTemplate_length : fastOutputReturnTemplate.length = 1 := by
  rfl

@[simp] theorem fastOutputTemplate_length : fastOutputTemplate.length = 50 := by
  rfl

theorem fastOutputTemplate_byteLength :
    (assembleBytes fastOutputTemplate).length = 186 := by
  rw [fastOutputTemplate, assembleBytes_append,
    List.length_append, assembleBytes_length, assembleBytes_length]
  simp [fastOutputBeforeReturnTemplate, fastPackTemplate, fastLoad0,
    fastPackStep, fastEndianStage8, fastEndianStage16, fastStoreAndSetup,
    fastOutputReturnTemplate, push0, push30, push31,
    DenseScheduleTemplate.op, DenseScheduleTemplate.push1,
    DenseScheduleTemplate.dup1, DenseScheduleTemplate.swap1,
    Instr.size]

def staticGas (instructions : List Instr) : Nat :=
  (instructions.map
    (Challenge.EvmProof.Meter.instrStaticCost .Osaka)).sum

theorem fastOutputTemplate_staticGas : staticGas fastOutputTemplate = 143 := by
  norm_num [staticGas, fastOutputTemplate, fastOutputBeforeReturnTemplate,
    fastPackTemplate, fastLoad0, fastPackStep, fastEndianStage8,
    fastEndianStage16, fastStoreAndSetup, fastOutputReturnTemplate,
    push0, push30, push31, DenseScheduleTemplate.op,
    DenseScheduleTemplate.push1, DenseScheduleTemplate.dup1,
    DenseScheduleTemplate.swap1,
    Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputTemplate
