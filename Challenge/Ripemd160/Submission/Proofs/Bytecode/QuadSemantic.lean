import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleWord

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-!
# H23 dense four-round semantic interface

This file relates the generic four-round raw state to the two direct
RIPEMD-160 lines.  It has no concrete sites or artifact dependency.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSemantic

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleWord
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.ScratchLow
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression

def quadIndex (k : Fin 20) (offset : Fin 4) : Nat :=
  4 * k.val + offset.val

def quadLeftAddress (k : Fin 20) (offset : Fin 4) : UInt256 :=
  UInt256.ofNat (644 + 4 * Crypto.Ripemd160.r[quadIndex k offset]!)

def quadRightAddress (k : Fin 20) (offset : Fin 4) : UInt256 :=
  UInt256.ofNat (644 + 4 * Crypto.Ripemd160.rP[quadIndex k offset]!)

def quadLeftRotation (k : Fin 20) (offset : Fin 4) : Nat :=
  Crypto.Ripemd160.s[quadIndex k offset]!

def quadRightRotation (k : Fin 20) (offset : Fin 4) : Nat :=
  Crypto.Ripemd160.sP[quadIndex k offset]!

def quadLeftConstant (k : Fin 20) : UInt256 :=
  ofUInt32 (Crypto.Ripemd160.K[k.val / 4]!)

def quadRightConstant (k : Fin 20) : UInt256 :=
  ofUInt32 (Crypto.Ripemd160.KP[k.val / 4]!)

def DenseWordsAt (s : State) (word : Nat → UInt32) : Prop :=
  ∀ i, i < 16 →
    Word.toUInt32 (MachineState.readWord s.memory (644 + 4 * i)) = word i

private theorem leftScheduleIndex_lt (k : Fin 20) (offset : Fin 4) :
    Crypto.Ripemd160.r[quadIndex k offset]! < 16 := by
  fin_cases k <;> fin_cases offset <;> decide

private theorem rightScheduleIndex_lt (k : Fin 20) (offset : Fin 4) :
    Crypto.Ripemd160.rP[quadIndex k offset]! < 16 := by
  fin_cases k <;> fin_cases offset <;> decide

theorem quadLeftAddress_toNat (k : Fin 20) (offset : Fin 4) :
    (quadLeftAddress k offset).toNat =
      644 + 4 * Crypto.Ripemd160.r[quadIndex k offset]! := by
  unfold quadLeftAddress
  rw [Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hi := leftScheduleIndex_lt k offset
  omega

theorem quadRightAddress_toNat (k : Fin 20) (offset : Fin 4) :
    (quadRightAddress k offset).toNat =
      644 + 4 * Crypto.Ripemd160.rP[quadIndex k offset]! := by
  unfold quadRightAddress
  rw [Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hi := rightScheduleIndex_lt k offset
  omega

theorem quadLeftRotation_le_32 (k : Fin 20) (offset : Fin 4) :
    quadLeftRotation k offset ≤ 32 := by
  fin_cases k <;> fin_cases offset <;> decide

theorem quadRightRotation_le_32 (k : Fin 20) (offset : Fin 4) :
    quadRightRotation k offset ≤ 32 := by
  fin_cases k <;> fin_cases offset <;> decide

private theorem leftWord (s : State) (word : Nat → UInt32)
    (k : Fin 20) (offset : Fin 4) (hwords : DenseWordsAt s word) :
    Word.toUInt32
        (MachineState.readWord s.memory (quadLeftAddress k offset).toNat) =
      word (Crypto.Ripemd160.r[quadIndex k offset]!) := by
  rw [quadLeftAddress_toNat k offset]
  exact hwords _ (by
    have hi := leftScheduleIndex_lt k offset
    omega)

private theorem rightWord (s : State) (word : Nat → UInt32)
    (k : Fin 20) (offset : Fin 4) (hwords : DenseWordsAt s word) :
    Word.toUInt32
        (MachineState.readWord s.memory (quadRightAddress k offset).toNat) =
      word (Crypto.Ripemd160.rP[quadIndex k offset]!) := by
  rw [quadRightAddress_toNat k offset]
  exact hwords _ (by
    have hi := rightScheduleIndex_lt k offset
    omega)

private theorem leftPairWorking (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (k : Fin 20)
    (offset0 offset1 : Fin 4) (hwords : DenseWordsAt s word) :
    PairRoundState.pairWorking s working (k.val / 4)
        (quadLeftAddress k offset0) (quadLeftAddress k offset1)
        (quadLeftRotation k offset0) (quadLeftRotation k offset1)
        (quadLeftConstant k) =
      StackCompression.leftStep word (quadIndex k offset1)
        (StackCompression.leftStep word (quadIndex k offset0) working) := by
  unfold PairRoundState.pairWorking
  rw [DenseScheduleWord.twoRawRound_eq_of_toUInt32_eq working (k.val / 4)
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.r[quadIndex k offset0]!)))
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.r[quadIndex k offset1]!)))
    _ _ _
    (by simpa only [Word.toUInt32_ofUInt32] using
      leftWord s word k offset0 hwords)
    (by simpa only [Word.toUInt32_ofUInt32] using
      leftWord s word k offset1 hwords)]
  fin_cases k <;> fin_cases offset0 <;> fin_cases offset1 <;> rfl

private theorem rightPairWorking (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (k : Fin 20)
    (offset0 offset1 : Fin 4) (hwords : DenseWordsAt s word) :
    PairRoundState.pairWorking s working (4 - k.val / 4)
        (quadRightAddress k offset0) (quadRightAddress k offset1)
        (quadRightRotation k offset0) (quadRightRotation k offset1)
        (quadRightConstant k) =
      StackCompression.rightStep word (quadIndex k offset1)
        (StackCompression.rightStep word (quadIndex k offset0) working) := by
  unfold PairRoundState.pairWorking
  rw [DenseScheduleWord.twoRawRound_eq_of_toUInt32_eq working (4 - k.val / 4)
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.rP[quadIndex k offset0]!)))
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.rP[quadIndex k offset1]!)))
    _ _ _
    (by simpa only [Word.toUInt32_ofUInt32] using
      rightWord s word k offset0 hwords)
    (by simpa only [Word.toUInt32_ofUInt32] using
      rightWord s word k offset1 hwords)]
  fin_cases k <;> fin_cases offset0 <;> fin_cases offset1 <;> rfl

theorem quadWorking_left (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (k : Fin 20)
    (hwords : DenseWordsAt s word) :
    QuadRoundState.quadWorking s working (k.val / 4)
        (quadLeftAddress k 0) (quadLeftAddress k 1)
        (quadLeftAddress k 2) (quadLeftAddress k 3)
        (quadLeftRotation k 0) (quadLeftRotation k 1)
        (quadLeftRotation k 2) (quadLeftRotation k 3)
        (quadLeftConstant k) =
      StackCompression.leftStep word (quadIndex k 3)
        (StackCompression.leftStep word (quadIndex k 2)
          (StackCompression.leftStep word (quadIndex k 1)
            (StackCompression.leftStep word (quadIndex k 0) working))) := by
  have hwords' : DenseWordsAt
      (QuadRoundState.quadFirstState s
        (quadLeftAddress k 0) (quadLeftAddress k 1)) word := by
    intro i hi
    simpa [DenseWordsAt, QuadRoundState.quadFirstState] using hwords i hi
  unfold QuadRoundState.quadWorking QuadRoundState.quadFirstWorking
  rw [leftPairWorking
    (QuadRoundState.quadFirstState s
      (quadLeftAddress k 0) (quadLeftAddress k 1)) word
    (PairRoundState.pairWorking s working (k.val / 4)
      (quadLeftAddress k 0) (quadLeftAddress k 1)
      (quadLeftRotation k 0) (quadLeftRotation k 1) (quadLeftConstant k))
    k 2 3 hwords']
  rw [leftPairWorking s word working k 0 1 hwords]

theorem quadWorking_right (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (k : Fin 20)
    (hwords : DenseWordsAt s word) :
    QuadRoundState.quadWorking s working (4 - k.val / 4)
        (quadRightAddress k 0) (quadRightAddress k 1)
        (quadRightAddress k 2) (quadRightAddress k 3)
        (quadRightRotation k 0) (quadRightRotation k 1)
        (quadRightRotation k 2) (quadRightRotation k 3)
        (quadRightConstant k) =
      StackCompression.rightStep word (quadIndex k 3)
        (StackCompression.rightStep word (quadIndex k 2)
          (StackCompression.rightStep word (quadIndex k 1)
            (StackCompression.rightStep word (quadIndex k 0) working))) := by
  have hwords' : DenseWordsAt
      (QuadRoundState.quadFirstState s
        (quadRightAddress k 0) (quadRightAddress k 1)) word := by
    intro i hi
    simpa [DenseWordsAt, QuadRoundState.quadFirstState] using hwords i hi
  unfold QuadRoundState.quadWorking QuadRoundState.quadFirstWorking
  rw [rightPairWorking
    (QuadRoundState.quadFirstState s
      (quadRightAddress k 0) (quadRightAddress k 1)) word
    (PairRoundState.pairWorking s working (4 - k.val / 4)
      (quadRightAddress k 0) (quadRightAddress k 1)
      (quadRightRotation k 0) (quadRightRotation k 1) (quadRightConstant k))
    k 2 3 hwords']
  rw [rightPairWorking s word working k 0 1 hwords]

private theorem activeWordsAfter_eq_of_end_le (curr offset size : Nat)
    (hend : offset + size ≤ curr * 32) :
    MachineState.activeWordsAfter curr offset size = curr := by
  unfold MachineState.activeWordsAfter
  split
  · rfl
  · dsimp only
    apply Nat.max_eq_left
    have hq : (offset + size - 1) / 32 < curr :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega

private theorem ofNat_toNat (w : UInt256) : UInt256.ofNat w.toNat = w := by
  cases w with
  | mk val => simp [UInt256.ofNat, UInt256.toNat, UInt256.size]

theorem activeWordsAfterUInt256_2_eq_of_end_le (s : State)
    (off0 size0 off1 size1 : Nat)
    (hend0 : off0 + size0 ≤ s.activeWords.toNat * 32)
    (hend1 : off1 + size1 ≤ s.activeWords.toNat * 32) :
    s.activeWordsAfterUInt256_2 off0 size0 off1 size1 = s.activeWords := by
  unfold State.activeWordsAfterUInt256_2
  rw [activeWordsAfter_eq_of_end_le _ _ _ hend0,
    activeWordsAfter_eq_of_end_le _ _ _ hend1, ofNat_toNat]

theorem quadActiveWordsAfterUInt256_4_eq_of_end_le (s : State)
    (off0 off1 off2 off3 : Nat)
    (hend0 : off0 + 32 ≤ s.activeWords.toNat * 32)
    (hend1 : off1 + 32 ≤ s.activeWords.toNat * 32)
    (hend2 : off2 + 32 ≤ s.activeWords.toNat * 32)
    (hend3 : off3 + 32 ≤ s.activeWords.toNat * 32) :
    QuadRoundState.quadActiveWordsAfterUInt256_4 s off0 off1 off2 off3 =
      s.activeWords := by
  let s1 : State :=
    {s with activeWords := s.activeWordsAfterUInt256_2 off0 32 off1 32}
  have h1 : s1.activeWords = s.activeWords := by
    dsimp [s1]
    exact activeWordsAfterUInt256_2_eq_of_end_le s off0 32 off1 32
      hend0 hend1
  have h2 : s1.activeWordsAfterUInt256_2 off2 32 off3 32 = s1.activeWords := by
    apply activeWordsAfterUInt256_2_eq_of_end_le
    · simpa [h1] using hend2
    · simpa [h1] using hend3
  calc
    QuadRoundState.quadActiveWordsAfterUInt256_4 s off0 off1 off2 off3 =
        s1.activeWordsAfterUInt256_2 off2 32 off3 32 := by rfl
    _ = s1.activeWords := h2
    _ = s.activeWords := h1

theorem quadLeftAddress_end_le (s : State) (k : Fin 20) (offset : Fin 4)
    (hactive : 66 ≤ s.activeWords.toNat) :
    (quadLeftAddress k offset).toNat + 32 ≤ s.activeWords.toNat * 32 := by
  rw [quadLeftAddress_toNat k offset]
  have hi := leftScheduleIndex_lt k offset
  omega

theorem quadRightAddress_end_le (s : State) (k : Fin 20) (offset : Fin 4)
    (hactive : 66 ≤ s.activeWords.toNat) :
    (quadRightAddress k offset).toNat + 32 ≤ s.activeWords.toNat * 32 := by
  rw [quadRightAddress_toNat k offset]
  have hi := rightScheduleIndex_lt k offset
  omega

theorem quadLeftActiveWords_unchanged (s : State) (k : Fin 20)
    (hactive : 66 ≤ s.activeWords.toNat) :
    QuadRoundState.quadActiveWordsAfterUInt256_4 s
        (quadLeftAddress k 0).toNat (quadLeftAddress k 1).toNat
        (quadLeftAddress k 2).toNat (quadLeftAddress k 3).toNat =
      s.activeWords := by
  apply quadActiveWordsAfterUInt256_4_eq_of_end_le
  · exact quadLeftAddress_end_le s k 0 hactive
  · exact quadLeftAddress_end_le s k 1 hactive
  · exact quadLeftAddress_end_le s k 2 hactive
  · exact quadLeftAddress_end_le s k 3 hactive

theorem quadRightActiveWords_unchanged (s : State) (k : Fin 20)
    (hactive : 66 ≤ s.activeWords.toNat) :
    QuadRoundState.quadActiveWordsAfterUInt256_4 s
        (quadRightAddress k 0).toNat (quadRightAddress k 1).toNat
        (quadRightAddress k 2).toNat (quadRightAddress k 3).toNat =
      s.activeWords := by
  apply quadActiveWordsAfterUInt256_4_eq_of_end_le
  · exact quadRightAddress_end_le s k 0 hactive
  · exact quadRightAddress_end_le s k 1 hactive
  · exact quadRightAddress_end_le s k 2 hactive
  · exact quadRightAddress_end_le s k 3 hactive

theorem leftRounds_quad (word : Nat → UInt32) (k : Nat)
    (working : Compression.EvmWorking) :
    StackCompression.leftRounds word (4 * (k + 1)) working =
      StackCompression.leftStep word (4 * k + 3)
        (StackCompression.leftStep word (4 * k + 2)
          (StackCompression.leftStep word (4 * k + 1)
            (StackCompression.leftStep word (4 * k)
              (StackCompression.leftRounds word (4 * k) working)))) := by
  have hcount : 4 * (k + 1) = (4 * k + 3) + 1 := by omega
  rw [hcount]
  simp only [StackCompression.leftRounds]

theorem rightRounds_quad (word : Nat → UInt32) (k : Nat)
    (working : Compression.EvmWorking) :
    StackCompression.rightRounds word (4 * (k + 1)) working =
      StackCompression.rightStep word (4 * k + 3)
        (StackCompression.rightStep word (4 * k + 2)
          (StackCompression.rightStep word (4 * k + 1)
            (StackCompression.rightStep word (4 * k)
              (StackCompression.rightRounds word (4 * k) working)))) := by
  have hcount : 4 * (k + 1) = (4 * k + 3) + 1 := by omega
  rw [hcount]
  simp only [StackCompression.rightRounds]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSemantic
