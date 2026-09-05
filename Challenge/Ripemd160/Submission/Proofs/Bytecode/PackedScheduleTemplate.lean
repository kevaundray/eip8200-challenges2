import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.EvmProof.Meter
import YulEvmCompiler.Instr

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# H17 ascending packed-schedule templates

This module contains only generic instruction templates and executable state
models.  It does not import a concrete bytecode artifact.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleTemplate

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof

def op (operation : Operation) : Instr := .op operation

def push1 (value : UInt256) : Instr :=
  .push ⟨1, by decide⟩ value

def push2 (value : UInt256) : Instr :=
  .push ⟨2, by decide⟩ value

def push4 (value : UInt256) : Instr :=
  .push ⟨4, by decide⟩ value

def push32 (value : UInt256) : Instr :=
  .push ⟨32, by decide⟩ value

def dup1 : Instr := .op (.Dup ⟨0, by decide⟩)

def swap1 : Instr := .op (.Swap ⟨0, by decide⟩)

def mask32 : UInt256 := UInt256.ofNat 0xffffffff

def mask8 : UInt256 :=
  UInt256.ofNat 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff

def mask16 : UInt256 :=
  UInt256.ofNat 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff

def storeBase (half : Nat) : Nat := 672 + 32 * (8 * half)

def storeAddress (half index : Nat) : Nat :=
  672 + 32 * (8 * half + index)

/-! ## The exact instruction plan -/

def initialTemplate : List Instr :=
  [ op .JUMPDEST, dup1, push1 (UInt256.ofNat 60), op .ADD, op .MLOAD,
    op .POP, dup1, op .MLOAD, swap1, push1 (UInt256.ofNat 32), op .ADD,
    op .MLOAD, swap1 ]

def endianStage (shift : Nat) (mask : UInt256) : List Instr :=
  [ dup1, push1 (UInt256.ofNat shift), op .SHR, push32 mask, op .AND,
    swap1, push32 mask, op .AND, push1 (UInt256.ofNat shift), op .SHL,
    op .OR ]

def storeJ0 (half : Nat) : List Instr :=
  [ dup1, push1 (UInt256.ofNat 224), op .SHR,
    push2 (UInt256.ofNat (storeAddress half 0)), op .MSTORE ]

def storeJ (half index : Nat) : List Instr :=
  [ dup1, push1 (UInt256.ofNat (224 - 32 * index)), op .SHR,
    push4 mask32, op .AND,
    push2 (UInt256.ofNat (storeAddress half index)), op .MSTORE ]

def storeJ7 (half : Nat) : List Instr :=
  [ push4 mask32, op .AND,
    push2 (UInt256.ofNat (storeAddress half 7)), op .MSTORE ]

def storeTemplate (half : Nat) : List Instr :=
  storeJ0 half ++ storeJ half 1 ++ storeJ half 2 ++ storeJ half 3 ++
    storeJ half 4 ++ storeJ half 5 ++ storeJ half 6 ++ storeJ7 half

def halfTemplate (half : Nat) : List Instr :=
  endianStage 8 mask8 ++ endianStage 16 mask16 ++ storeTemplate half

def ascendingPackedTemplate : List Instr :=
  initialTemplate ++ halfTemplate 0 ++ halfTemplate 1

def finalJumpTemplate : List Instr := [op .JUMP]

def ascendingPackedFullTemplate : List Instr :=
  ascendingPackedTemplate ++ finalJumpTemplate

@[simp] theorem endianStage_length (shift : Nat) (mask : UInt256) :
    (endianStage shift mask).length = 11 := by
  rfl

@[simp] theorem storeJ0_length (half : Nat) :
    (storeJ0 half).length = 5 := by
  rfl

@[simp] theorem storeJ_length (half index : Nat) :
    (storeJ half index).length = 7 := by
  rfl

@[simp] theorem storeJ7_length (half : Nat) :
    (storeJ7 half).length = 4 := by
  rfl

@[simp] theorem storeTemplate_length (half : Nat) :
    (storeTemplate half).length = 51 := by
  rfl

@[simp] theorem halfTemplate_length (half : Nat) :
    (halfTemplate half).length = 73 := by
  rfl

@[simp] theorem initialTemplate_length : initialTemplate.length = 13 := by
  rfl

@[simp] theorem ascendingPackedTemplate_length :
    ascendingPackedTemplate.length = 159 := by
  rfl

@[simp] theorem ascendingPackedFullTemplate_length :
    ascendingPackedFullTemplate.length = 160 := by
  rfl

theorem assembleBytes_length (instructions : List Instr) :
    (assembleBytes instructions).length =
      (instructions.map Instr.size).sum := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [assembleBytes_cons, List.length_append, List.map_cons,
        List.sum_cons]
      change instruction.bytes.length + (assembleBytes rest).length =
        instruction.bytes.length + (rest.map Instr.size).sum
      rw [ih]

theorem ascendingPackedTemplate_byteLength :
    (assembleBytes ascendingPackedTemplate).length = 527 := by
  rw [assembleBytes_length]
  simp [ascendingPackedTemplate, initialTemplate, halfTemplate, endianStage,
    storeTemplate, storeJ0, storeJ, storeJ7, op, push1, push2, push4, push32,
    dup1, swap1]

theorem ascendingPackedFullTemplate_byteLength :
    (assembleBytes ascendingPackedFullTemplate).length = 528 := by
  rw [ascendingPackedFullTemplate, assembleBytes_append,
    List.length_append, ascendingPackedTemplate_byteLength]
  rfl

/-! ## Generic packed values and state models -/

def packedStage (value : UInt256) (shift : Nat) (mask : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.shiftLeft (UInt256.land value mask) (UInt256.ofNat shift))
    (UInt256.land
      (UInt256.shiftRight value (UInt256.ofNat shift)) mask)

def packedWord (value : UInt256) : UInt256 :=
  packedStage (packedStage value 8 mask8) 16 mask16

def packedChunk (value : UInt256) (index : Nat) : UInt256 :=
  if index = 0 then
    UInt256.shiftRight value (UInt256.ofNat 224)
  else
    UInt256.land
      (UInt256.shiftRight value (UInt256.ofNat (224 - 32 * index))) mask32

def packedChunks (value : UInt256) : List UInt256 :=
  (List.range 8).map (packedChunk value)

def inputWord0 (s : State) (messageOffset : UInt256) : UInt256 :=
  MachineState.readWord s.memory messageOffset.toNat

def inputWord1 (s : State) (messageOffset : UInt256) : UInt256 :=
  MachineState.readWord s.memory
    (messageOffset + UInt256.ofNat 32).toNat

def packedInput0 (s : State) (messageOffset : UInt256) : UInt256 :=
  packedWord (inputWord0 s messageOffset)

def packedInput1 (s : State) (messageOffset : UInt256) : UInt256 :=
  packedWord (inputWord1 s messageOffset)

def wordBytes (value : UInt256) : ByteArray :=
  Data.Bytes.natToBytesPadded value.toNat 32

/-- Write each word as an actual 32-byte EVM `MSTORE`, in ascending order. -/
def writeWordsAscending (memory : ByteArray) (base : Nat)
    (words : List UInt256) : ByteArray :=
  (words.foldl
      (fun (acc : Nat × ByteArray) (value : UInt256) =>
        (acc.1 + 1,
          MachineState.writeBytes acc.2 (wordBytes value)
            (base + 32 * acc.1)))
      (0, memory)).2

def writePackedHalf (memory : ByteArray) (half : Nat) (value : UInt256) : ByteArray :=
  writeWordsAscending memory (storeBase half) (packedChunks value)

def expectedMemory (s : State) (messageOffset : UInt256) : ByteArray :=
  writePackedHalf
    (writePackedHalf s.memory 0 (packedInput0 s messageOffset))
    1 (packedInput1 s messageOffset)

def activeAfterWord (current : UInt256) (offset : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.activeWordsAfter current.toNat offset.toNat 32)

def warmupActiveWords (s : State) (messageOffset : UInt256) : UInt256 :=
  let a0 := activeAfterWord s.activeWords
    (messageOffset + UInt256.ofNat 60)
  let a1 := activeAfterWord a0 messageOffset
  activeAfterWord a1 (messageOffset + UInt256.ofNat 32)

def storeAddresses (half : Nat) : List Nat :=
  (List.range 8).map (storeAddress half)

def storeActiveWords (current : UInt256) (addresses : List Nat) : UInt256 :=
  addresses.foldl
    (fun current address => activeAfterWord current (UInt256.ofNat address)) current

def expectedActiveWords (s : State) (messageOffset : UInt256) : UInt256 :=
  storeActiveWords
    (storeActiveWords (warmupActiveWords s messageOffset) (storeAddresses 0))
    (storeAddresses 1)

def scheduleEntry (s : State) (startPC messageOffset returnPC : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := startPC, stack := [messageOffset, returnPC] ++ rest }

def expectedState (s : State) (startPC messageOffset returnPC : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := StackRoundTrace.pcAfter startPC ascendingPackedTemplate
    stack := [returnPC] ++ rest
    memory := expectedMemory s messageOffset
    activeWords := expectedActiveWords s messageOffset }

@[simp] theorem expectedState_executionEnv
    (s : State) (startPC messageOffset returnPC : UInt256) (rest : List UInt256) :
    (expectedState s startPC messageOffset returnPC rest).executionEnv =
      s.executionEnv := by
  simp only [expectedState]

@[simp] theorem expectedState_halt
    (s : State) (startPC messageOffset returnPC : UInt256) (rest : List UInt256) :
    (expectedState s startPC messageOffset returnPC rest).halt = s.halt := by
  simp only [expectedState]

@[simp] theorem expectedState_callStack
    (s : State) (startPC messageOffset returnPC : UInt256) (rest : List UInt256) :
    (expectedState s startPC messageOffset returnPC rest).callStack = s.callStack := by
  simp only [expectedState]

@[simp] theorem expectedState_accountMap
    (s : State) (startPC messageOffset returnPC : UInt256) (rest : List UInt256) :
    (expectedState s startPC messageOffset returnPC rest).accountMap = s.accountMap := by
  simp only [expectedState]

@[simp] theorem expectedState_substate
    (s : State) (startPC messageOffset returnPC : UInt256) (rest : List UInt256) :
    (expectedState s startPC messageOffset returnPC rest).substate = s.substate := by
  simp only [expectedState]

@[simp] theorem expectedState_gasAvailable
    (s : State) (startPC messageOffset returnPC : UInt256) (rest : List UInt256) :
    (expectedState s startPC messageOffset returnPC rest).gasAvailable =
      s.gasAvailable := by
  simp only [expectedState]

@[simp] theorem expectedState_returnData
    (s : State) (startPC messageOffset returnPC : UInt256) (rest : List UInt256) :
    (expectedState s startPC messageOffset returnPC rest).returnData = s.returnData := by
  simp only [expectedState]

@[simp] theorem expectedState_hReturn
    (s : State) (startPC messageOffset returnPC : UInt256) (rest : List UInt256) :
    (expectedState s startPC messageOffset returnPC rest).hReturn = s.hReturn := by
  simp only [expectedState]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleTemplate
