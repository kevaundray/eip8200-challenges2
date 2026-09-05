import Challenge.EvmProof.Stepper
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Bounded raw execution of the H12 final combination

This file is independent of the generated artifact.  It evaluates the raw
instruction tail with `Stepper.runInstr`; the artifact only needs to supply
decoder and jump-destination facts when this result is lifted later.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof.Word
open Compression

def workingStack (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [right.a, right.b, right.c, right.d, right.e,
    left.a, left.b, left.c, left.d, left.e, ret] ++ rest

def tailEntry (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 0xae2
    stack := workingStack left right ret rest }

def combined (s : State) (left right : Compression.EvmWorking) :
    Compression.EvmHashState :=
  Compression.evmCombine (StackMemory.hashAt s.memory) left right

def c0Instructions : List Instr :=
  [ .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 0x40),
    .op .MLOAD,
    .op .ADD,
    .op .ADD,
    .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
    .op .AND ]

def c1Instructions : List Instr :=
  [ .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 0x60),
    .op .MLOAD,
    .op .ADD,
    .op .ADD,
    .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 0x40),
    .op .MSTORE ]

def c2Instructions : List Instr :=
  [ .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
    .op .MLOAD,
    .op .ADD,
    .op .ADD,
    .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 0x60),
    .op .MSTORE ]

def c3Instructions : List Instr :=
  [ .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 0xa0),
    .op .MLOAD,
    .op .ADD,
    .op .ADD,
    .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
    .op .MSTORE ]

def c4Instructions : List Instr :=
  [ .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 0x20),
    .op .MLOAD,
    .op .ADD,
    .op .ADD,
    .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 0xa0),
    .op .MSTORE ]

def storeH0Instructions : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 0x20),
    .op .MSTORE ]

def cleanupInstructions : List Instr :=
  [ .op .POP, .op .POP, .op .POP, .op .POP, .op .POP,
    .op .POP, .op .POP, .op .POP, .op .POP, .op .POP ]

def finalJumpInstructions : List Instr :=
  [ .op .JUMP ]

def tail60Instructions : List Instr :=
  c0Instructions ++ c1Instructions ++ c2Instructions ++ c3Instructions ++
    c4Instructions ++ storeH0Instructions ++ cleanupInstructions

def tailInstructions : List Instr := tail60Instructions ++ finalJumpInstructions

def c0Result (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 0xaef
    stack := (combined s left right).h0 :: workingStack left right ret rest }

def preJumpResult (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 0xb3c
    memory := StackMemory.storeHash s.memory (combined s left right)
    stack := ret :: rest }

def tailResult (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) : State :=
  { preJumpResult s left right ret rest with
    pc := ret
    stack := rest }

def runTailInstrs : List Instr → State → Option State
  | [], s => some s
  | instruction :: instructions, s =>
      match Challenge.EvmProof.Stepper.runInstr instruction s with
      | some next => runTailInstrs instructions next
      | none => none

private theorem activeWordsAfter_tail (s : State) (offset : Nat)
    (hoff : offset + 32 ≤ 66 * 32)
    (hactive : 66 ≤ s.activeWords.toNat) :
    s.activeWordsAfterUInt256 offset 32 = s.activeWords := by
  unfold State.activeWordsAfterUInt256
  have haw : MachineState.activeWordsAfter s.activeWords.toNat offset 32 =
      s.activeWords.toNat := by
    unfold MachineState.activeWordsAfter
    rw [if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_eq_left
    have hq : (offset + 32 - 1) / 32 < s.activeWords.toNat := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega
  rw [haw]
  cases hword : s.activeWords with
  | mk val =>
      apply congrArg UInt256.mk
      apply Fin.ext
      simp [UInt256.toNat, Fin.ofNat, Nat.mod_eq_of_lt val.isLt]

private theorem readWord_writeHashWord_disjoint (memory : ByteArray)
    (readStart writeStart value : Nat)
    (hdisjoint : readStart + 32 ≤ writeStart ∨
      writeStart + 32 ≤ readStart) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) writeStart)
        readStart = MachineState.readWord memory readStart := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  have hsize :
      (Data.Bytes.natToBytesPadded value 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  rw [hsize]
  exact hdisjoint

private theorem read96_write64 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 64) 96 =
      MachineState.readWord memory 96 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega))

private theorem read128_write64 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 64) 128 =
      MachineState.readWord memory 128 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega))

private theorem read128_write96 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 96) 128 =
      MachineState.readWord memory 128 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega))

private theorem read160_write64 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 64) 160 =
      MachineState.readWord memory 160 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega))

private theorem read160_write96 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 96) 160 =
      MachineState.readWord memory 160 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega))

private theorem read160_write128 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 128) 160 =
      MachineState.readWord memory 160 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega))

private theorem read32_write64 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 64) 32 =
      MachineState.readWord memory 32 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inl (by omega))

private theorem read32_write96 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 96) 32 =
      MachineState.readWord memory 32 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inl (by omega))

private theorem read32_write128 (memory : ByteArray) (value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) 128) 32 =
      MachineState.readWord memory 32 := by
  exact readWord_writeHashWord_disjoint _ _ _ _ (Or.inl (by omega))

private theorem mask32_push (value : UInt256) :
    UInt256.land (UInt256.ofNat 0xffffffff) value = mask32 value := by
  unfold mask32
  exact Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.land_comm
    (UInt256.ofNat 0xffffffff) value

set_option linter.unusedSimpArgs false in
theorem run_c0 (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256)
    (hactive : 66 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1009) :
    runTailInstrs c0Instructions (tailEntry s left right ret rest) =
      some (c0Result s left right ret rest) := by
  have hcap11 : rest.length + 11 < 1024 := by omega
  have hcap12 : rest.length + 12 < 1024 := by omega
  have hcap13 : rest.length + 13 < 1024 := by omega
  have hcap14 : rest.length + 14 < 1024 := by omega
  simp (config := { maxSteps := 100000 }) (discharger := omega)
    [runTailInstrs, c0Instructions, tailEntry, c0Result, workingStack,
      combined, Challenge.EvmProof.Stepper.runInstr,
      activeWordsAfter_tail, hactive, hstack, hcap11, hcap12, hcap13, hcap14,
      Nat.add_assoc, List.getElem?_cons_zero, List.getElem?_cons_succ]
  constructor
  · decide
  · simp only [Compression.evmCombine, StackMemory.hashAt]
    unfold mask32
    exact (Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.land_comm
      (UInt256.ofNat 0xffffffff)
      (MachineState.readWord s.memory 64 + left.c + right.d))

set_option linter.unusedSimpArgs false in
theorem run_tail60 (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256)
    (hactive : 66 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1009) :
    runTailInstrs tail60Instructions (tailEntry s left right ret rest) =
      some (preJumpResult s left right ret rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hcap7 : rest.length + 7 < 1024 := by omega
  have hcap8 : rest.length + 8 < 1024 := by omega
  have hcap9 : rest.length + 9 < 1024 := by omega
  have hcap10 : rest.length + 10 < 1024 := by omega
  have hcap11 : rest.length + 11 < 1024 := by omega
  have hcap12 : rest.length + 12 < 1024 := by omega
  have hcap13 : rest.length + 13 < 1024 := by omega
  have hcap14 : rest.length + 14 < 1024 := by omega
  have hcap15 : rest.length + 15 < 1024 := by omega
  simp (config := { maxSteps := 1000000 }) (discharger := omega)
    [runTailInstrs, tail60Instructions, c0Instructions, c1Instructions,
      c2Instructions, c3Instructions, c4Instructions, storeH0Instructions,
      cleanupInstructions, tailEntry, preJumpResult, workingStack, combined,
      Challenge.EvmProof.Stepper.runInstr, StackMemory.storeHash,
      activeWordsAfter_tail, readWord_writeHashWord_disjoint,
      read96_write64, read128_write64, read128_write96, read160_write64,
      read160_write96, read160_write128, read32_write64, read32_write96,
      read32_write128, mask32_push,
      hactive, hstack, hcap0, hcap1, hcap2, hcap3, hcap4, hcap5, hcap6,
      hcap7, hcap8, hcap9, hcap10, hcap11, hcap12, hcap13, hcap14, hcap15,
      Nat.add_assoc, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Challenge.EvmProof.Word.mask32_toNat, Compression.evmCombine,
      StackMemory.hashAt]
  decide

theorem run_tail_jump (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256)
    (_hactive : 66 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1009)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    runTailInstrs finalJumpInstructions (preJumpResult s left right ret rest) =
      some (tailResult s left right ret rest) := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  simp [runTailInstrs, finalJumpInstructions, preJumpResult, tailResult,
    Challenge.EvmProof.Stepper.runInstr, hvalid, hcap1]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail
