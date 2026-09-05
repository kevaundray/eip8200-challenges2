import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyState
import Challenge.EvmProof.Bytes

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyCorrect

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputState KnownInputCompactBodyState

def tablePayload (i : Nat) : ByteArray :=
  MachineState.readPadded submissionBytecode (tableSource i) 20

private theorem tablePayload_eq_chunk14 (i : Nat) :
    tablePayload i =
      MachineState.readPadded submissionByteChunk14 (173 + 21 * i) 20 := by
  apply ByteArray.ext_getElem
  · simp [tablePayload]
  · intro k hk₁ hk₂
    unfold tablePayload at hk₁ ⊢
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hk₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hk₂,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD]
    have hk : k < 20 := by simpa [tablePayload] using hk₁
    rw [if_pos hk, if_pos hk]
    unfold submissionBytecode submissionBytes
    rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_neg (by
      simp [tableSource]
      omega)]
    congr 2
    simp [tableSource]
    omega

theorem tablePayload_size (i : Nat) : (tablePayload i).size = 20 := by
  simp [tablePayload]

private theorem readPadded_four_eq (bs : ByteArray) (off : Nat) :
    MachineState.readPadded bs off 4 = ByteArray.mk #[
      bs[off]?.getD 0, bs[off + 1]?.getD 0,
      bs[off + 2]?.getD 0, bs[off + 3]?.getD 0] := by
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    rfl
  · intro k hk₁ hk₂
    have hk : k < 4 := by simpa using hk₁
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hk₁,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hk]
    interval_cases k <;> rfl

private theorem bytesToBigEndianNat_readPadded_four (bs : ByteArray)
    (off : Nat) :
    Data.Bytes.bytesToBigEndianNat (MachineState.readPadded bs off 4) =
      ((((bs[off]?.getD 0).toNat * 256 +
          (bs[off + 1]?.getD 0).toNat) * 256 +
          (bs[off + 2]?.getD 0).toNat) * 256) +
        (bs[off + 3]?.getD 0).toNat := by
  rw [readPadded_four_eq]
  simp [Data.Bytes.bytesToBigEndianNat,
    Challenge.EvmProof.Bytecode.toList_eq_data]

private theorem readPadded_readPadded_four (bs : ByteArray) (start off : Nat)
    (hoff : off + 4 ≤ 20) :
    MachineState.readPadded (MachineState.readPadded bs start 20) off 4 =
      MachineState.readPadded bs (start + off) 4 := by
  apply ByteArray.ext_getElem
  · simp
  · intro k hk₁ hk₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hk₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hk₂,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD]
    have hk : k < 4 := by simpa using hk₁
    rw [if_pos hk,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      if_pos (by omega),
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      if_pos hk]
    congr 2
    omega

theorem tablePayload_word (i j : Nat) (hi : i < 16) (hj : j < 5) :
    Precompile.bytesToNatPadded (tablePayload i) (4 * j) 4 =
      (knownAfter i)[j]!.toNat := by
  rw [tablePayload_eq_chunk14]
  unfold Precompile.bytesToNatPadded
  rw [readPadded_readPadded_four _ _ _ (by omega)]
  rw [bytesToBigEndianNat_readPadded_four]
  interval_cases i <;> interval_cases j <;>
    norm_num (config := { maxSteps := 1000000 })
      [submissionByteChunk14,
        knownAfter, KnownInputDigest.H1, KnownInputDigest.H2,
        KnownInputDigest.H3, KnownInputDigest.H4, KnownInputDigest.H5,
        KnownInputDigest.H6, KnownInputDigest.H7, KnownInputDigest.H8,
        KnownInputDigest.H9, KnownInputDigest.H10, KnownInputDigest.H11,
        KnownInputDigest.H12, KnownInputDigest.H13, KnownInputDigest.H14,
        KnownInputDigest.H15, KnownInputDigest.H16,
        Challenge.EvmProof.Memory.getD0_eq_getElem!,
        ByteArray.getElem_eq_getElem_data]
  all_goals decide

private theorem readPadded_writeBytes_window
    (memory bytes : ByteArray) (offset : Nat)
    (hoff : offset + 4 ≤ bytes.size) :
    MachineState.readPadded (MachineState.writeBytes memory bytes 0)
        offset 4 = MachineState.readPadded bytes offset 4 := by
  apply ByteArray.ext_getElem
  · simp only [Challenge.EvmProof.Memory.readPadded_size]
  · intro k hk₁ hk₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hk₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hk₂,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD]
    have hk : k < 4 := by simpa using hk₁
    rw [if_pos hk, if_pos hk, MachineState.writeBytes_getElem?_getD]
    rw [if_pos (by omega)]
    congr 2

private theorem bytesToNatPadded_writeBytes_window
    (memory bytes : ByteArray) (offset : Nat)
    (hoff : offset + 4 ≤ bytes.size) :
    Precompile.bytesToNatPadded (MachineState.writeBytes memory bytes 0)
        offset 4 = Precompile.bytesToNatPadded bytes offset 4 := by
  unfold Precompile.bytesToNatPadded
  rw [readPadded_writeBytes_window memory bytes offset hoff]

theorem load4_tableMemory (s : State) (i j : Nat) (hi : i < 16) (hj : j < 5) :
    load4 (tableMemory s i) (4 * j) = Word.ofUInt32 (knownAfter i)[j]! := by
  unfold load4
  rw [Challenge.EvmProof.Bytes.shiftRight_readWord _ _ 4 (by omega) (by omega)]
  have hwindow := bytesToNatPadded_writeBytes_window s.memory (tablePayload i)
    (4 * j) (by rw [tablePayload_size]; omega)
  unfold tableMemory tablePayload at hwindow
  unfold tableMemory
  rw [hwindow]
  change UInt256.ofNat
    (Precompile.bytesToNatPadded (tablePayload i) (4 * j) 4) = _
  rw [tablePayload_word i j hi hj]
  rfl

@[simp] theorem readWord_storeLoaded_same (memory : ByteArray)
    (readOffset writeOffset : Nat) :
    MachineState.readWord (storeLoaded memory readOffset writeOffset) writeOffset =
      load4 memory readOffset := by
  unfold storeLoaded KnownInputState.writeWord
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem readWord_storeLoaded_disjoint (memory : ByteArray)
    (readOffset writeOffset sourceOffset : Nat)
    (hdisjoint : readOffset + 32 ≤ writeOffset ∨ writeOffset + 32 ≤ readOffset) :
    MachineState.readWord (storeLoaded memory sourceOffset writeOffset) readOffset =
      MachineState.readWord memory readOffset := by
  unfold storeLoaded KnownInputState.writeWord
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hdisjoint

theorem load4_storeLoaded_before (memory : ByteArray)
    (readOffset sourceOffset writeOffset : Nat) (hbefore : readOffset + 4 ≤ writeOffset) :
    load4 (storeLoaded memory sourceOffset writeOffset) readOffset =
      load4 memory readOffset := by
  unfold load4
  rw [Challenge.EvmProof.Bytes.shiftRight_readWord _ _ 4 (by omega) (by omega),
    Challenge.EvmProof.Bytes.shiftRight_readWord _ _ 4 (by omega) (by omega)]
  congr 1
  unfold Precompile.bytesToNatPadded storeLoaded KnownInputState.writeWord
  rw [Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint]
  exact Or.inl hbefore

theorem resultMemory_h0 (s : State) (i : Nat) (hi : i < 16)
    :
    MachineState.readWord (KnownInputCompactBodyState.resultMemory s i) 32 =
      Word.ofUInt32 (knownAfter i)[0]! := by
  unfold KnownInputCompactBodyState.resultMemory
  rw [readWord_storeLoaded_disjoint _ 32 160 16 (Or.inl (by omega)),
    readWord_storeLoaded_disjoint _ 32 128 12 (Or.inl (by omega)),
    readWord_storeLoaded_disjoint _ 32 96 8 (Or.inl (by omega)),
    readWord_storeLoaded_disjoint _ 32 64 4 (Or.inl (by omega)),
    readWord_storeLoaded_same]
  exact load4_tableMemory s i 0 hi (by omega)

theorem resultMemory_h1 (s : State) (i : Nat) (hi : i < 16)
    :
    MachineState.readWord (KnownInputCompactBodyState.resultMemory s i) 64 =
      Word.ofUInt32 (knownAfter i)[1]! := by
  unfold KnownInputCompactBodyState.resultMemory
  rw [readWord_storeLoaded_disjoint _ 64 160 16 (Or.inl (by omega)),
    readWord_storeLoaded_disjoint _ 64 128 12 (Or.inl (by omega)),
    readWord_storeLoaded_disjoint _ 64 96 8 (Or.inl (by omega)),
    readWord_storeLoaded_same,
    load4_storeLoaded_before _ 4 0 32 (by omega)]
  exact load4_tableMemory s i 1 hi (by omega)

theorem resultMemory_h2 (s : State) (i : Nat) (hi : i < 16)
    :
    MachineState.readWord (KnownInputCompactBodyState.resultMemory s i) 96 =
      Word.ofUInt32 (knownAfter i)[2]! := by
  unfold KnownInputCompactBodyState.resultMemory
  rw [readWord_storeLoaded_disjoint _ 96 160 16 (Or.inl (by omega)),
    readWord_storeLoaded_disjoint _ 96 128 12 (Or.inl (by omega)),
    readWord_storeLoaded_same,
    load4_storeLoaded_before _ 8 4 64 (by omega),
    load4_storeLoaded_before _ 8 0 32 (by omega)]
  exact load4_tableMemory s i 2 hi (by omega)

theorem resultMemory_h3 (s : State) (i : Nat) (hi : i < 16)
    :
    MachineState.readWord (KnownInputCompactBodyState.resultMemory s i) 128 =
      Word.ofUInt32 (knownAfter i)[3]! := by
  unfold KnownInputCompactBodyState.resultMemory
  rw [readWord_storeLoaded_disjoint _ 128 160 16 (Or.inl (by omega)),
    readWord_storeLoaded_same,
    load4_storeLoaded_before _ 12 8 96 (by omega),
    load4_storeLoaded_before _ 12 4 64 (by omega),
    load4_storeLoaded_before _ 12 0 32 (by omega)]
  exact load4_tableMemory s i 3 hi (by omega)

theorem resultMemory_h4 (s : State) (i : Nat) (hi : i < 16)
    :
    MachineState.readWord (KnownInputCompactBodyState.resultMemory s i) 160 =
      Word.ofUInt32 (knownAfter i)[4]! := by
  unfold KnownInputCompactBodyState.resultMemory
  rw [readWord_storeLoaded_same,
    load4_storeLoaded_before _ 16 12 128 (by omega),
    load4_storeLoaded_before _ 16 8 96 (by omega),
    load4_storeLoaded_before _ 16 4 64 (by omega),
    load4_storeLoaded_before _ 16 0 32 (by omega)]
  exact load4_tableMemory s i 4 hi (by omega)

theorem resultState_hashAt (s : State) (input : ByteArray) (i : Nat)
    (hi : i < 16) :
    StackRunBridge.hashAt32 (KnownInputCompactBodyState.resultState s input i) =
      StackRunBridge.embedHashArray (knownAfter i) := by
  unfold StackRunBridge.hashAt32 StackRunBridge.embedHashArray
    StackRunBridge.wordAt KnownInputCompactBodyState.resultState
  rw [resultMemory_h0 s i hi, resultMemory_h1 s i hi,
    resultMemory_h2 s i hi, resultMemory_h3 s i hi,
    resultMemory_h4 s i hi]

theorem resultState_word_above (s : State) (input : ByteArray) (i address : Nat)
    (haddress : 0x4a0 ≤ address) :
    StackRunBridge.wordAt (KnownInputCompactBodyState.resultState s input i) address =
      StackRunBridge.wordAt s address := by
  unfold StackRunBridge.wordAt KnownInputCompactBodyState.resultState
    KnownInputCompactBodyState.resultMemory storeLoaded tableMemory
    KnownInputState.writeWord
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  all_goals simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    Challenge.EvmProof.Memory.readPadded_size]
  all_goals omega

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyCorrect
