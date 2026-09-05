import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactState

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyState

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

def tableSource (i : Nat) : Nat := 4958 + 21 * i

def preCopyState (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x132e
    stack := [UInt256.ofNat 0, UInt256.ofNat (tableSource i), UInt256.ofNat 20,
      DriverTrace.messageOffsetWord i, UInt256.ofNat 0x436,
      DriverTrace.blockOffsetWord i, Padding.paddedWord input] }

def copiedState (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x132f
    stack := [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x436,
      DriverTrace.blockOffsetWord i, Padding.paddedWord input]
    activeWords := s.activeWordsAfterUInt256 0 20
    memory := MachineState.writeBytes s.memory
      (MachineState.readPadded s.executionEnv.code (tableSource i) 20) 0 }

def activeAfter (current : UInt256) (offset size : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.activeWordsAfter current.toNat offset size)

def load4 (memory : ByteArray) (offset : Nat) : UInt256 :=
  UInt256.shiftRight (MachineState.readWord memory offset) (UInt256.ofNat 224)

def storeLoaded (memory : ByteArray) (readOffset writeOffset : Nat) : ByteArray :=
  KnownInputState.writeWord memory writeOffset (load4 memory readOffset)

def tableMemory (s : State) (i : Nat) : ByteArray :=
  MachineState.writeBytes s.memory
    (MachineState.readPadded submissionBytecode (tableSource i) 20) 0

def resultMemory (s : State) (i : Nat) : ByteArray :=
  let m0 := tableMemory s i
  let m1 := storeLoaded m0 0 32
  let m2 := storeLoaded m1 4 64
  let m3 := storeLoaded m2 8 96
  let m4 := storeLoaded m3 12 128
  storeLoaded m4 16 160

def resultActiveWords (s : State) : UInt256 :=
  let a0 := activeAfter s.activeWords 0 20
  let a1 := activeAfter a0 0 32
  let a2 := activeAfter a1 32 32
  let a3 := activeAfter a2 4 32
  let a4 := activeAfter a3 64 32
  let a5 := activeAfter a4 8 32
  let a6 := activeAfter a5 96 32
  let a7 := activeAfter a6 12 32
  let a8 := activeAfter a7 128 32
  let a9 := activeAfter a8 16 32
  activeAfter a9 160 32

def resultState (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x436
    stack := [DriverTrace.blockOffsetWord i, Padding.paddedWord input]
    memory := resultMemory s i
    activeWords := resultActiveWords s }

@[simp] theorem resultState_executionEnv (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).executionEnv = s.executionEnv := by rfl

@[simp] theorem resultState_halt (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).halt = s.halt := by rfl

@[simp] theorem resultState_callStack (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).callStack = s.callStack := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyState
