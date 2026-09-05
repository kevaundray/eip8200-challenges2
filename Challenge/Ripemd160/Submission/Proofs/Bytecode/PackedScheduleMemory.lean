import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleMath

set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleMemory

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof

def naturalp (p : Nat) : UInt256 := UInt256.ofNat p

def packedWord (bytes : ByteArray) (p i : Nat) : UInt256 :=
  let h := i / 8
  let j := i % 8
  let v := PackedScheduleMath.packed
    (MachineState.readWord bytes (p + 32 * h))
  if j = 0 then
    PackedScheduleMath.shr v 224
  else if j = 7 then
    Word.mask32 v
  else
    Word.mask32 (PackedScheduleMath.shr v (32 * (7 - j)))

def storeWords (bytes : ByteArray) (p : Nat) : Nat → ByteArray
  | 0 => bytes
  | n + 1 =>
      MachineState.writeBytes (storeWords bytes p n)
        (Data.Bytes.natToBytesPadded (packedWord bytes p n).toNat 32)
        (672 + 32 * n)

theorem loadOffsetWord_toNat (p i : Nat) (hi : i < 16)
    (hbound : p + 64 < 2 ^ 256) :
    (Schedule.loadOffsetWord (naturalp p) i).toNat = p + 4 * i := by
  unfold naturalp Schedule.loadOffsetWord
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide)
    (by omega : i * 2 ^ 2 < 2 ^ 256)]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

private theorem packedWord_base (bytes : ByteArray) (p i : Nat)
    (hi : i < 16) (hbound : p + 64 < 2 ^ 256) :
    PackedScheduleMath.le4
        (MachineState.readWord bytes (p + 32 * (i / 8))) (i % 8) =
      Schedule.readLEWord bytes (Schedule.loadOffsetWord (naturalp p) i) := by
  have hj : i % 8 < 8 := Nat.mod_lt _ (by omega)
  have hdivmod : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
  have hsource : p + 32 * (i / 8) + 4 * (i % 8) = p + 4 * i := by
    omega
  rw [PackedScheduleMath.le4_readWord_offset bytes
    (p + 32 * (i / 8)) (i % 8) hj]
  rw [hsource]
  unfold Schedule.readLEWord
  rw [loadOffsetWord_toNat p i hi hbound]
  rfl

private theorem shr_zero (v : UInt256) :
    PackedScheduleMath.shr v 0 = v := by
  apply Challenge.EvmProof.Word.word_ext
  unfold PackedScheduleMath.shr UInt256.shiftRight
  have hz : (UInt256.ofNat 0).toNat = 0 := by
    rfl
  rw [hz]
  split
  · omega
  change (v.val >>> (UInt256.ofNat 0).val).val = v.val.val
  rw [Fin.shiftRight_val]
  rw [show (UInt256.ofNat 0).val.val = 0 by rfl, Nat.shiftRight_zero]

theorem packedWord_eq_expectedWord (bytes : ByteArray) (p i : Nat)
    (hi : i < 16) (hbound : p + 64 < 2 ^ 256) :
    packedWord bytes p i =
      ScheduleCorrect.expectedWord bytes (naturalp p) i := by
  have hj : i % 8 < 8 := Nat.mod_lt _ (by omega)
  have hbase := packedWord_base bytes p i hi hbound
  by_cases hj0 : i % 8 = 0
  · simp only [packedWord, hj0, ↓reduceIte]
    calc
      PackedScheduleMath.shr
          (PackedScheduleMath.packed
            (MachineState.readWord bytes (p + 32 * (i / 8)))) 224 = Word.mask32
          (PackedScheduleMath.shr
            (PackedScheduleMath.packed
              (MachineState.readWord bytes (p + 32 * (i / 8)))) 224) :=
        (PackedScheduleMath.mask32_shr224 _).symm
      _ = Word.mask32
          (PackedScheduleMath.le4
            (MachineState.readWord bytes (p + 32 * (i / 8))) (i % 8)) := by
        simpa [hj0] using
          (PackedScheduleMath.packed_extract
            (MachineState.readWord bytes (p + 32 * (i / 8))) (i % 8) hj)
      _ = ScheduleCorrect.expectedWord bytes (naturalp p) i := by
        rw [hbase]
        rfl
  · by_cases hj7 : i % 8 = 7
    · simp only [packedWord, hj7, ↓reduceIte]
      calc
        Word.mask32
            (PackedScheduleMath.packed
              (MachineState.readWord bytes (p + 32 * (i / 8)))) =
            Word.mask32 (PackedScheduleMath.shr
              (PackedScheduleMath.packed
                (MachineState.readWord bytes (p + 32 * (i / 8))))
              (32 * (7 - (i % 8)))) := by
          simp [hj7, shr_zero]
        _ = Word.mask32
            (PackedScheduleMath.le4
              (MachineState.readWord bytes (p + 32 * (i / 8))) (i % 8)) :=
          PackedScheduleMath.packed_extract
            (MachineState.readWord bytes (p + 32 * (i / 8))) (i % 8) hj
        _ = ScheduleCorrect.expectedWord bytes (naturalp p) i := by
          rw [hbase]
          rfl
    · simp only [packedWord, hj0, hj7, ↓reduceIte]
      calc
        Word.mask32 (PackedScheduleMath.shr
            (PackedScheduleMath.packed
              (MachineState.readWord bytes (p + 32 * (i / 8))))
            (32 * (7 - (i % 8)))) = Word.mask32
            (PackedScheduleMath.le4
              (MachineState.readWord bytes (p + 32 * (i / 8))) (i % 8)) :=
          PackedScheduleMath.packed_extract
            (MachineState.readWord bytes (p + 32 * (i / 8))) (i % 8) hj
        _ = ScheduleCorrect.expectedWord bytes (naturalp p) i := by
          rw [hbase]
          rfl

theorem storeWords_loopState_memory (s : State) (p n : Nat)
    (returnPC : UInt256) (rest : List UInt256) (hn : n ≤ 16)
    (hp : 0x4a0 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    storeWords s.memory p n =
      (Schedule.loopState s (naturalp p) returnPC rest n).memory := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn16 : n < 16 := by omega
      have hread := ScheduleCorrect.loopState_readLEWord s (naturalp p)
        returnPC rest n n (by omega) hn16 (by
          rw [loadOffsetWord_toNat p n hn16 hbound]
          omega)
      rw [storeWords, Schedule.loopState,
        ScheduleCorrect.afterIteration_memory, ih (by omega)]
      have hexpected :
          ScheduleCorrect.expectedWord
              (Schedule.loopState s (naturalp p) returnPC rest n).memory
              (naturalp p) n =
            ScheduleCorrect.expectedWord s.memory (naturalp p) n := by
        unfold ScheduleCorrect.expectedWord
        rw [hread]
      rw [hexpected, packedWord_eq_expectedWord s.memory p n hn16 hbound]
      rw [ScheduleCorrect.xSlotWord_toNat n hn16]
      simp [Nat.mul_comm]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleMemory
