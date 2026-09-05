import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestResult
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRunBridge

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputState

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

def legacyEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x129e
    stack := [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x436,
      DriverTrace.blockOffsetWord i, Padding.paddedWord input] }

def sizeMatched (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x12dc
    stack := [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x436,
      DriverTrace.blockOffsetWord i, Padding.paddedWord input] }

def sizeFailed (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x12d8
    stack := [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x436,
      DriverTrace.blockOffsetWord i, Padding.paddedWord input] }

def chunk0 := KnownInputData.checks.take 8
def chunk1 := (KnownInputData.checks.drop 8).take 8
def chunk2 := (KnownInputData.checks.drop 16).take 8
def chunk3 := KnownInputData.checks.drop 24

def acc0 (_input : ByteArray) : UInt256 := 0
def acc1 (input : ByteArray) := KnownInputLogic.scanDiff input chunk0 (acc0 input)
def acc2 (input : ByteArray) := KnownInputLogic.scanDiff input chunk1 (acc1 input)
def acc3 (input : ByteArray) := KnownInputLogic.scanDiff input chunk2 (acc2 input)
def acc4 (input : ByteArray) := KnownInputLogic.scanDiff input chunk3 (acc3 input)

def accAfter (input : ByteArray) (n : Nat) : UInt256 :=
  match n with
  | 0 => acc0 input
  | 1 => acc1 input
  | 2 => acc2 input
  | 3 => acc3 input
  | _ => acc4 input

theorem acc4_eq_scanDiff (input : ByteArray) :
    acc4 input = KnownInputLogic.scanDiff input KnownInputData.checks 0 := by rfl

def accState (s : State) (input : ByteArray) (i pc n : Nat) : State :=
  { s with
    pc := UInt256.ofNat pc
    stack := [accAfter input n, DriverTrace.messageOffsetWord i,
      UInt256.ofNat 0x436, DriverTrace.blockOffsetWord i,
      Padding.paddedWord input] }

def selectorEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x17b9
    stack := [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x436,
      DriverTrace.blockOffsetWord i, Padding.paddedWord input] }

def bodyEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat ([0x1848, 0x1873, 0x189e, 0x18c9,
      0x18f4, 0x191f, 0x194a, 0x1975, 0x19a0, 0x19cb, 0x19f6,
      0x1a21, 0x1a4c, 0x1a77, 0x1aa2, 0x1acd][i]!)
    stack := [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x436,
      DriverTrace.blockOffsetWord i, Padding.paddedWord input] }

def knownAfter (i : Nat) : Array UInt32 :=
  match i with
  | 0 => KnownInputDigest.H1
  | 1 => KnownInputDigest.H2
  | 2 => KnownInputDigest.H3
  | 3 => KnownInputDigest.H4
  | 4 => KnownInputDigest.H5
  | 5 => KnownInputDigest.H6
  | 6 => KnownInputDigest.H7
  | 7 => KnownInputDigest.H8
  | 8 => KnownInputDigest.H9
  | 9 => KnownInputDigest.H10
  | 10 => KnownInputDigest.H11
  | 11 => KnownInputDigest.H12
  | 12 => KnownInputDigest.H13
  | 13 => KnownInputDigest.H14
  | 14 => KnownInputDigest.H15
  | _ => KnownInputDigest.H16

theorem knownAfter_eq_knownAt_succ (i : Nat) (hi : i < 16) :
    knownAfter i = KnownDigestResult.knownAt (i + 1) := by
  interval_cases i <;> rfl

def writeWord (memory : ByteArray) (offset : Nat)
    (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded value.toNat 32) offset

def resultMemory (memory : ByteArray) (i : Nat) : ByteArray :=
  let h := knownAfter i
  let m0 := writeWord memory 0x20 (Word.ofUInt32 h[0]!)
  let m1 := writeWord m0 0x40 (Word.ofUInt32 h[1]!)
  let m2 := writeWord m1 0x60 (Word.ofUInt32 h[2]!)
  let m3 := writeWord m2 0x80 (Word.ofUInt32 h[3]!)
  writeWord m3 0xa0 (Word.ofUInt32 h[4]!)

def resultActiveWords (s : State) : UInt256 :=
  let a0 := s.activeWordsAfterUInt256 0x20 32
  let a1 := UInt256.ofNat (MachineState.activeWordsAfter a0.toNat 0x40 32)
  let a2 := UInt256.ofNat (MachineState.activeWordsAfter a1.toNat 0x60 32)
  let a3 := UInt256.ofNat (MachineState.activeWordsAfter a2.toNat 0x80 32)
  UInt256.ofNat (MachineState.activeWordsAfter a3.toNat 0xa0 32)

def resultState (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x436
    stack := [DriverTrace.blockOffsetWord i, Padding.paddedWord input]
    memory := resultMemory s.memory i
    activeWords := resultActiveWords s }

@[simp] theorem resultState_executionEnv (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).executionEnv = s.executionEnv := by rfl

@[simp] theorem resultState_halt (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).halt = s.halt := by rfl

@[simp] theorem resultState_callStack (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).callStack = s.callStack := by rfl

private theorem readWord_writeWord_same (memory : ByteArray)
    (offset : Nat) (value : UInt256) :
    MachineState.readWord (writeWord memory offset value) offset = value := by
  exact Challenge.EvmProof.Memory.readWord_writeWord memory offset value

private theorem readWord_writeWord_disjoint (memory : ByteArray)
    (readStart writeStart : Nat) (value : UInt256)
    (hdisjoint : readStart + 32 ≤ writeStart ∨ writeStart + 32 ≤ readStart) :
    MachineState.readWord (writeWord memory writeStart value) readStart =
      MachineState.readWord memory readStart := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hdisjoint

@[simp] private theorem resultMemory_h0 (memory : ByteArray) (i : Nat) :
    MachineState.readWord (resultMemory memory i) 0x20 =
      Word.ofUInt32 (knownAfter i)[0]! := by
  unfold resultMemory
  rw [readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega))]
  exact readWord_writeWord_same _ _ _

@[simp] private theorem resultMemory_h1 (memory : ByteArray) (i : Nat) :
    MachineState.readWord (resultMemory memory i) 0x40 =
      Word.ofUInt32 (knownAfter i)[1]! := by
  unfold resultMemory
  rw [readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega))]
  exact readWord_writeWord_same _ _ _

@[simp] private theorem resultMemory_h2 (memory : ByteArray) (i : Nat) :
    MachineState.readWord (resultMemory memory i) 0x60 =
      Word.ofUInt32 (knownAfter i)[2]! := by
  unfold resultMemory
  rw [readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega))]
  exact readWord_writeWord_same _ _ _

@[simp] private theorem resultMemory_h3 (memory : ByteArray) (i : Nat) :
    MachineState.readWord (resultMemory memory i) 0x80 =
      Word.ofUInt32 (knownAfter i)[3]! := by
  unfold resultMemory
  rw [readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega))]
  exact readWord_writeWord_same _ _ _

@[simp] private theorem resultMemory_h4 (memory : ByteArray) (i : Nat) :
    MachineState.readWord (resultMemory memory i) 0xa0 =
      Word.ofUInt32 (knownAfter i)[4]! := by
  unfold resultMemory
  exact readWord_writeWord_same _ _ _

@[simp] theorem resultState_hashAt (s : State) (input : ByteArray) (i : Nat) :
    StackRunBridge.hashAt32 (resultState s input i) =
      StackRunBridge.embedHashArray (knownAfter i) := by
  unfold StackRunBridge.hashAt32 StackRunBridge.embedHashArray
    StackRunBridge.wordAt resultState
  rw [resultMemory_h0, resultMemory_h1, resultMemory_h2,
    resultMemory_h3, resultMemory_h4]

theorem resultState_word_above (s : State) (input : ByteArray) (i address : Nat)
    (haddress : 0x4a0 ≤ address) :
    StackRunBridge.wordAt (resultState s input i) address =
      StackRunBridge.wordAt s address := by
  unfold StackRunBridge.wordAt resultState resultMemory
  rw [readWord_writeWord_disjoint _ _ _ _ (Or.inr (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inr (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inr (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inr (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inr (by omega))]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputState
