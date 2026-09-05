import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleMemory

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleMemoryBridge

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof

private theorem and_eq_land (a b : UInt256) :
    a &&& b = UInt256.land a b := by
  rfl

private theorem or_eq_lor (a b : UInt256) :
    a ||| b = UInt256.lor a b := by
  rfl

private theorem packedStage_eq_math (value : UInt256) (shift : Nat)
    (mask : UInt256) :
    PackedScheduleTemplate.packedStage value shift mask =
      UInt256.lor
        (UInt256.land (PackedScheduleMath.shr value shift) mask)
        (PackedScheduleMath.shl (UInt256.land value mask) shift) := by
  unfold PackedScheduleTemplate.packedStage PackedScheduleMath.shr
    PackedScheduleMath.shl
  exact Word.lor_comm _ _

private theorem packedWord_eq_math (value : UInt256) :
    PackedScheduleTemplate.packedWord value =
      PackedScheduleMath.packed value := by
  unfold PackedScheduleTemplate.packedWord PackedScheduleMath.packed
  rw [packedStage_eq_math, packedStage_eq_math]
  simp only [PackedScheduleTemplate.mask8, PackedScheduleTemplate.mask16,
    PackedScheduleMath.mask8, PackedScheduleMath.mask16, and_eq_land,
    or_eq_lor]

private theorem shr_zero (value : UInt256) :
    PackedScheduleMath.shr value 0 = value := by
  apply Challenge.EvmProof.Word.word_ext
  unfold PackedScheduleMath.shr UInt256.shiftRight
  have hz : (UInt256.ofNat 0).toNat = 0 := by
    rfl
  rw [hz]
  split
  · omega
  change (value.val >>> (UInt256.ofNat 0).val).val = value.val.val
  rw [Fin.shiftRight_val]
  rw [show (UInt256.ofNat 0).val.val = 0 by rfl, Nat.shiftRight_zero]

private theorem shiftRight_zero (value : UInt256) :
    UInt256.shiftRight value (UInt256.ofNat 0) = value := by
  change PackedScheduleMath.shr value 0 = value
  exact shr_zero value

private theorem packedInput0_eq_math (s : State) (p : Nat)
    (hbound : p + 64 < 2 ^ 256) :
    PackedScheduleTemplate.packedInput0 s (UInt256.ofNat p) =
      PackedScheduleMath.packed (MachineState.readWord s.memory p) := by
  have hp256 : p < 2 ^ 256 := by
    omega
  have hpword : (UInt256.ofNat p).toNat = p := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hp256]
  unfold PackedScheduleTemplate.packedInput0
    PackedScheduleTemplate.inputWord0
  rw [hpword, packedWord_eq_math]

private theorem packedInput1_eq_math (s : State) (p : Nat)
    (hbound : p + 64 < 2 ^ 256) :
    PackedScheduleTemplate.packedInput1 s (UInt256.ofNat p) =
      PackedScheduleMath.packed (MachineState.readWord s.memory (p + 32)) := by
  have hp32 : p + 32 < 2 ^ 256 := by
    omega
  have hmsg32 :
      (UInt256.ofNat p + UInt256.ofNat 32).toNat = p + 32 := by
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat hp32,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hp32]
  unfold PackedScheduleTemplate.packedInput1
    PackedScheduleTemplate.inputWord1
  rw [hmsg32, packedWord_eq_math]

private theorem packedChunk_input0 (s : State) (p j : Nat)
    (hj : j < 8) (hbound : p + 64 < 2 ^ 256) :
    PackedScheduleTemplate.packedChunk
        (PackedScheduleTemplate.packedInput0 s (UInt256.ofNat p)) j =
      PackedScheduleMemory.packedWord s.memory p j := by
  rw [packedInput0_eq_math s p hbound]
  unfold PackedScheduleMemory.packedWord
  interval_cases j <;>
    simp [PackedScheduleTemplate.packedChunk, PackedScheduleMath.shr,
      PackedScheduleTemplate.mask32, Word.mask32, and_eq_land, shiftRight_zero]

private theorem packedChunk_input1 (s : State) (p j : Nat)
    (hj : j < 8) (hbound : p + 64 < 2 ^ 256) :
    PackedScheduleTemplate.packedChunk
        (PackedScheduleTemplate.packedInput1 s (UInt256.ofNat p)) j =
      PackedScheduleMemory.packedWord s.memory p (j + 8) := by
  rw [packedInput1_eq_math s p hbound]
  unfold PackedScheduleMemory.packedWord
  interval_cases j <;>
    simp [PackedScheduleTemplate.packedChunk, PackedScheduleMath.shr,
      PackedScheduleTemplate.mask32, Word.mask32, and_eq_land, shiftRight_zero]

private theorem packedChunks_input0 (s : State) (p : Nat)
    (hbound : p + 64 < 2 ^ 256) :
    PackedScheduleTemplate.packedChunks
        (PackedScheduleTemplate.packedInput0 s (UInt256.ofNat p)) =
      (List.range 8).map (PackedScheduleMemory.packedWord s.memory p) := by
  unfold PackedScheduleTemplate.packedChunks
  apply List.map_congr_left
  intro j hj
  exact packedChunk_input0 s p j (by simpa using hj) hbound

private theorem packedChunks_input1 (s : State) (p : Nat)
    (hbound : p + 64 < 2 ^ 256) :
    PackedScheduleTemplate.packedChunks
        (PackedScheduleTemplate.packedInput1 s (UInt256.ofNat p)) =
      (List.range 8).map (fun j =>
        PackedScheduleMemory.packedWord s.memory p (j + 8)) := by
  unfold PackedScheduleTemplate.packedChunks
  apply List.map_congr_left
  intro j hj
  exact packedChunk_input1 s p j (by simpa using hj) hbound

private theorem ascending_fold16 (memory : ByteArray) (p : Nat) :
    PackedScheduleTemplate.writeWordsAscending
        (PackedScheduleTemplate.writeWordsAscending memory 672
          ((List.range 8).map (PackedScheduleMemory.packedWord memory p)))
        928
        ((List.range 8).map (fun j =>
          PackedScheduleMemory.packedWord memory p (j + 8))) =
      PackedScheduleMemory.storeWords memory p 16 := by
  simp [PackedScheduleTemplate.writeWordsAscending,
    PackedScheduleTemplate.wordBytes, PackedScheduleMemory.storeWords,
    List.range_succ]

theorem expectedMemory_eq_loopState_memory (s : State) (p : Nat)
    (ret : UInt256) (rest : List UInt256)
    (hp : 0x4a0 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    PackedScheduleTemplate.expectedMemory s (UInt256.ofNat p) =
      (Schedule.loopState s (UInt256.ofNat p) ret rest 16).memory := by
  have hstore :
      PackedScheduleMemory.storeWords s.memory p 16 =
        (Schedule.loopState s (UInt256.ofNat p) ret rest 16).memory := by
    simpa [PackedScheduleMemory.naturalp] using
      (PackedScheduleMemory.storeWords_loopState_memory s p 16 ret rest
        (by omega) hp hbound)
  rw [← hstore]
  rw [PackedScheduleTemplate.expectedMemory]
  unfold PackedScheduleTemplate.writePackedHalf
  rw [
    packedChunks_input0 s p hbound, packedChunks_input1 s p hbound]
  exact ascending_fold16 s.memory p

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleMemoryBridge
