import Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
import Challenge.EvmProof.Memory

set_option warningAsError true

/-!
# Functional memory model for the H10 final hash stores

This module describes only the five final `MSTORE` operations.  It does not
state or prove a bytecode execution trace.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression

/-- The five chaining words at their H10 input locations. -/
def hashAt (memory : ByteArray) : Compression.EvmHashState :=
  { h0 := MachineState.readWord memory 32
    h1 := MachineState.readWord memory 64
    h2 := MachineState.readWord memory 96
    h3 := MachineState.readWord memory 128
    h4 := MachineState.readWord memory 160 }

/-- The H10 final stores, in their emitted order: `H1`, `H2`, `H3`, `H4`, `H0`. -/
def storeHash (memory : ByteArray) (value : Compression.EvmHashState) : ByteArray :=
  let m1 := MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded value.h1.toNat 32) 0x40
  let m2 := MachineState.writeBytes m1
    (Data.Bytes.natToBytesPadded value.h2.toNat 32) 0x60
  let m3 := MachineState.writeBytes m2
    (Data.Bytes.natToBytesPadded value.h3.toNat 32) 0x80
  let m4 := MachineState.writeBytes m3
    (Data.Bytes.natToBytesPadded value.h4.toNat 32) 0xa0
  MachineState.writeBytes m4
    (Data.Bytes.natToBytesPadded value.h0.toNat 32) 0x20

private theorem readWord_writeHashWord_disjoint (memory : ByteArray)
    (readStart writeStart : Nat) (value : UInt256)
    (hdisjoint : readStart + 32 ≤ writeStart ∨
      writeStart + 32 ≤ readStart) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value.toNat 32) writeStart)
        readStart = MachineState.readWord memory readStart := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  have hsize :
      (Data.Bytes.natToBytesPadded value.toNat 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  rw [hsize]
  exact hdisjoint

private theorem readWord_writeHashWord_same (memory : ByteArray)
    (writeStart : Nat) (value : UInt256) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value.toNat 32) writeStart)
        writeStart = value := by
  exact Challenge.EvmProof.Memory.readWord_writeWord memory writeStart value

@[simp] theorem readWord_storeHash_h0 (memory : ByteArray)
    (value : Compression.EvmHashState) :
    MachineState.readWord (storeHash memory value) 32 = value.h0 := by
  unfold storeHash
  exact readWord_writeHashWord_same _ _ _

@[simp] theorem readWord_storeHash_h1 (memory : ByteArray)
    (value : Compression.EvmHashState) :
    MachineState.readWord (storeHash memory value) 64 = value.h1 := by
  unfold storeHash
  rw [readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega)),
    readWord_writeHashWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeHashWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeHashWord_disjoint _ _ _ _ (Or.inl (by omega))]
  exact readWord_writeHashWord_same _ _ _

@[simp] theorem readWord_storeHash_h2 (memory : ByteArray)
    (value : Compression.EvmHashState) :
    MachineState.readWord (storeHash memory value) 96 = value.h2 := by
  unfold storeHash
  rw [readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega)),
    readWord_writeHashWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeHashWord_disjoint _ _ _ _ (Or.inl (by omega))]
  exact readWord_writeHashWord_same _ _ _

@[simp] theorem readWord_storeHash_h3 (memory : ByteArray)
    (value : Compression.EvmHashState) :
    MachineState.readWord (storeHash memory value) 128 = value.h3 := by
  unfold storeHash
  rw [readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega)),
    readWord_writeHashWord_disjoint _ _ _ _ (Or.inl (by omega))]
  exact readWord_writeHashWord_same _ _ _

@[simp] theorem readWord_storeHash_h4 (memory : ByteArray)
    (value : Compression.EvmHashState) :
    MachineState.readWord (storeHash memory value) 160 = value.h4 := by
  unfold storeHash
  rw [readWord_writeHashWord_disjoint _ _ _ _ (Or.inr (by omega))]
  exact readWord_writeHashWord_same _ _ _

private theorem readWord_writeHashWord_outside (memory : ByteArray)
    (address writeStart : Nat) (value : UInt256)
    (hwrite : 0x20 ≤ writeStart ∧ writeStart + 32 ≤ 0xc0)
    (houtside : address + 32 ≤ 0x20 ∨ 0xc0 ≤ address) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value.toNat 32) writeStart)
        address = MachineState.readWord memory address := by
  apply readWord_writeHashWord_disjoint
  rcases houtside with hbefore | hafter
  · left
    omega
  · right
    omega

theorem readWord_storeHash_outside (memory : ByteArray)
    (value : Compression.EvmHashState) (address : Nat)
    (houtside : address + 32 ≤ 0x20 ∨ 0xc0 ≤ address) :
    MachineState.readWord (storeHash memory value) address =
      MachineState.readWord memory address := by
  unfold storeHash
  rw [readWord_writeHashWord_outside _ address 32 value.h0 (by omega) houtside,
    readWord_writeHashWord_outside _ address 160 value.h4 (by omega) houtside,
    readWord_writeHashWord_outside _ address 128 value.h3 (by omega) houtside,
    readWord_writeHashWord_outside _ address 96 value.h2 (by omega) houtside,
    readWord_writeHashWord_outside _ address 64 value.h1 (by omega) houtside]

theorem readWord_storeHash_ge_4a0 (memory : ByteArray)
    (value : Compression.EvmHashState) (address : Nat)
    (haddress : 0x4a0 ≤ address) :
    MachineState.readWord (storeHash memory value) address =
      MachineState.readWord memory address := by
  apply readWord_storeHash_outside
  right
  omega

theorem hashAt_storeHash (memory : ByteArray)
    (value : Compression.EvmHashState) :
    hashAt (storeHash memory value) = value := by
  unfold hashAt
  rw [readWord_storeHash_h0, readWord_storeHash_h1,
    readWord_storeHash_h2, readWord_storeHash_h3, readWord_storeHash_h4]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory
