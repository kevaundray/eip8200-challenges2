import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRawTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleWord

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-!
# H24 paired-round certificates

Each certificate composes one six-push call, one paired helper, and one return
jump.  The raw helper evaluator is supplied by `PairRawTrace`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundCertificates

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairHelperTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairSites
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

abbrev Artifact := PairSites.Artifact

private theorem leftIndex_lt (i : Fin 80) :
    Crypto.Ripemd160.r[i.val]! < 16 := by
  fin_cases i <;> decide

private theorem rightIndex_lt (i : Fin 80) :
    Crypto.Ripemd160.rP[i.val]! < 16 := by
  fin_cases i <;> decide

theorem leftAddress_toNat (i : Fin 80) :
    (StackRoundData.leftAddress i.val).toNat =
      644 + 4 * Crypto.Ripemd160.r[i.val]! := by
  have hi := leftIndex_lt i
  unfold StackRoundData.leftAddress
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem rightAddress_toNat (i : Fin 80) :
    (StackRoundData.rightAddress i.val).toNat =
      644 + 4 * Crypto.Ripemd160.rP[i.val]! := by
  have hi := rightIndex_lt i
  unfold StackRoundData.rightAddress
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem leftAddress0_toNat (k : Fin 40) :
    (PairSites.leftAddress0 k).toNat =
      644 + 4 * Crypto.Ripemd160.r[2 * k.val]! := by
  simpa [PairSites.leftAddress0] using
    (leftAddress_toNat ⟨2 * k.val, by omega⟩)

theorem leftAddress1_toNat (k : Fin 40) :
    (PairSites.leftAddress1 k).toNat =
      644 + 4 * Crypto.Ripemd160.r[2 * k.val + 1]! := by
  simpa [PairSites.leftAddress1] using
    (leftAddress_toNat ⟨2 * k.val + 1, by omega⟩)

theorem rightAddress0_toNat (k : Fin 40) :
    (PairSites.rightAddress0 k).toNat =
      644 + 4 * Crypto.Ripemd160.rP[2 * k.val]! := by
  simpa [PairSites.rightAddress0] using
    (rightAddress_toNat ⟨2 * k.val, by omega⟩)

theorem rightAddress1_toNat (k : Fin 40) :
    (PairSites.rightAddress1 k).toNat =
      644 + 4 * Crypto.Ripemd160.rP[2 * k.val + 1]! := by
  simpa [PairSites.rightAddress1] using
    (rightAddress_toNat ⟨2 * k.val + 1, by omega⟩)

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
    (off₁ size₁ off₂ size₂ : Nat)
    (hend₁ : off₁ + size₁ ≤ s.activeWords.toNat * 32)
    (hend₂ : off₂ + size₂ ≤ s.activeWords.toNat * 32) :
    s.activeWordsAfterUInt256_2 off₁ size₁ off₂ size₂ = s.activeWords := by
  unfold State.activeWordsAfterUInt256_2
  rw [activeWordsAfter_eq_of_end_le _ _ _ hend₁,
    activeWordsAfter_eq_of_end_le _ _ _ hend₂, ofNat_toNat]

theorem leftPair_activeWords (s : State) (k : Fin 40)
    (hactive : 67 ≤ s.activeWords.toNat) :
    s.activeWordsAfterUInt256_2
        (PairSites.leftAddress0 k).toNat 32
        (PairSites.leftAddress1 k).toNat 32 = s.activeWords := by
  apply activeWordsAfterUInt256_2_eq_of_end_le
  · rw [leftAddress0_toNat k]
    have hi : Crypto.Ripemd160.r[2 * k.val]! < 16 := by
      simpa using (leftIndex_lt ⟨2 * k.val, by omega⟩)
    omega
  · rw [leftAddress1_toNat k]
    have hi : Crypto.Ripemd160.r[2 * k.val + 1]! < 16 := by
      simpa using (leftIndex_lt ⟨2 * k.val + 1, by omega⟩)
    omega

theorem rightPair_activeWords (s : State) (k : Fin 40)
    (hactive : 67 ≤ s.activeWords.toNat) :
    s.activeWordsAfterUInt256_2
        (PairSites.rightAddress0 k).toNat 32
        (PairSites.rightAddress1 k).toNat 32 = s.activeWords := by
  apply activeWordsAfterUInt256_2_eq_of_end_le
  · rw [rightAddress0_toNat k]
    have hi : Crypto.Ripemd160.rP[2 * k.val]! < 16 := by
      simpa using (rightIndex_lt ⟨2 * k.val, by omega⟩)
    omega
  · rw [rightAddress1_toNat k]
    have hi : Crypto.Ripemd160.rP[2 * k.val + 1]! < 16 := by
      simpa using (rightIndex_lt ⟨2 * k.val + 1, by omega⟩)
    omega

private theorem leftWord0 (s : State) (word : Nat → UInt32) (k : Fin 40)
    (hwords : ∀ i, i < 16 →
      Word.toUInt32 (MachineState.readWord s.memory (644 + 4 * i)) = word i) :
    Word.toUInt32 (MachineState.readWord s.memory (PairSites.leftAddress0 k).toNat) =
      word (Crypto.Ripemd160.r[2 * k.val]!) := by
  rw [leftAddress0_toNat k]
  exact hwords _ (by
    have hi := leftIndex_lt ⟨2 * k.val, by omega⟩
    omega)

private theorem leftWord1 (s : State) (word : Nat → UInt32) (k : Fin 40)
    (hwords : ∀ i, i < 16 →
      Word.toUInt32 (MachineState.readWord s.memory (644 + 4 * i)) = word i) :
    Word.toUInt32 (MachineState.readWord s.memory (PairSites.leftAddress1 k).toNat) =
      word (Crypto.Ripemd160.r[2 * k.val + 1]!) := by
  rw [leftAddress1_toNat k]
  exact hwords _ (by
    have hi := leftIndex_lt ⟨2 * k.val + 1, by omega⟩
    omega)

private theorem rightWord0 (s : State) (word : Nat → UInt32) (k : Fin 40)
    (hwords : ∀ i, i < 16 →
      Word.toUInt32 (MachineState.readWord s.memory (644 + 4 * i)) = word i) :
    Word.toUInt32 (MachineState.readWord s.memory (PairSites.rightAddress0 k).toNat) =
      word (Crypto.Ripemd160.rP[2 * k.val]!) := by
  rw [rightAddress0_toNat k]
  exact hwords _ (by
    have hi := rightIndex_lt ⟨2 * k.val, by omega⟩
    omega)

private theorem rightWord1 (s : State) (word : Nat → UInt32) (k : Fin 40)
    (hwords : ∀ i, i < 16 →
      Word.toUInt32 (MachineState.readWord s.memory (644 + 4 * i)) = word i) :
    Word.toUInt32 (MachineState.readWord s.memory (PairSites.rightAddress1 k).toNat) =
      word (Crypto.Ripemd160.rP[2 * k.val + 1]!) := by
  rw [rightAddress1_toNat k]
  exact hwords _ (by
    have hi := rightIndex_lt ⟨2 * k.val + 1, by omega⟩
    omega)

def purePairWorking (s : State) (working : Compression.EvmWorking)
    (j : Nat) (p0 p1 : UInt256) (r0 r1 : Nat) (constant : UInt256) :
    Compression.EvmWorking :=
  PairRoundState.pairWorking s working j p0 p1 r0 r1 constant

theorem purePairWorking_left (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (k : Fin 40)
    (hwords : ∀ i, i < 16 →
      Word.toUInt32 (MachineState.readWord s.memory (644 + 4 * i)) = word i) :
    purePairWorking s working (k.val / 8)
        (PairSites.leftAddress0 k) (PairSites.leftAddress1 k)
        (PairSites.leftRotation0 k) (PairSites.leftRotation1 k)
        (PairSites.leftConstant k) =
      StackCompression.leftStep word (2 * k.val + 1)
        (StackCompression.leftStep word (2 * k.val) working) := by
  unfold purePairWorking PairRoundState.pairWorking
  rw [DenseScheduleWord.twoRawRound_eq_of_toUInt32_eq working (k.val / 8)
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.r[2 * k.val]!)))
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.r[2 * k.val + 1]!)))
    _ _ _
    (by simpa only [Word.toUInt32_ofUInt32] using leftWord0 s word k hwords)
    (by simpa only [Word.toUInt32_ofUInt32] using leftWord1 s word k hwords)]
  fin_cases k <;>
    rfl

theorem purePairWorking_right (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (k : Fin 40)
    (hwords : ∀ i, i < 16 →
      Word.toUInt32 (MachineState.readWord s.memory (644 + 4 * i)) = word i) :
    purePairWorking s working (4 - k.val / 8)
        (PairSites.rightAddress0 k) (PairSites.rightAddress1 k)
        (PairSites.rightRotation0 k) (PairSites.rightRotation1 k)
        (PairSites.rightConstant k) =
      StackCompression.rightStep word (2 * k.val + 1)
        (StackCompression.rightStep word (2 * k.val) working) := by
  unfold purePairWorking PairRoundState.pairWorking
  rw [DenseScheduleWord.twoRawRound_eq_of_toUInt32_eq working (4 - k.val / 8)
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.rP[2 * k.val]!)))
    _ (Word.ofUInt32 (word (Crypto.Ripemd160.rP[2 * k.val + 1]!)))
    _ _ _
    (by simpa only [Word.toUInt32_ofUInt32] using rightWord0 s word k hwords)
    (by simpa only [Word.toUInt32_ofUInt32] using rightWord1 s word k hwords)]
  fin_cases k <;>
    rfl

private theorem leftConstant_zero (k : Fin 40)
    (hzero : k.val / 8 = 0) : PairSites.leftConstant k = 0 := by
  fin_cases k <;>
    simp_all [PairSites.leftConstant, StackRoundData.leftConstant] <;>
    decide

private theorem rightConstant_zero (k : Fin 40)
    (hzero : 4 - k.val / 8 = 0) : PairSites.rightConstant k = 0 := by
  fin_cases k <;>
    simp_all [PairSites.rightConstant, StackRoundData.rightConstant] <;>
    decide

def gasSteps_leftPair (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rest : List UInt256) (k : Fin 40)
    (_hwords : ∀ i, i < 16 →
      Word.toUInt32 (MachineState.readWord s.memory (644 + 4 * i)) = word i)
    (hactive : 67 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (roundEntry s (PairSites.leftPC k.val) working.a working.b working.c
        working.d working.e rest)
      {s with
        pc := PairSites.leftPC (k.val + 1)
        stack := roundWords
          (purePairWorking s working (k.val / 8)
            (PairSites.leftAddress0 k) (PairSites.leftAddress1 k)
            (PairSites.leftRotation0 k) (PairSites.leftRotation1 k)
            (PairSites.leftConstant k)) ++ rest
        activeWords := s.activeWords} := by
  let site := PairSites.leftRoundSite k
  have hraw :
      runInstrSeq (pairBeforeJumpTemplate (k.val / 8) (PairSites.leftConstant k))
        (pairHelperEntry s site.helper.startPC (PairSites.leftAddress0 k)
          (PairSites.leftAddress1 k) site.returnPC
          (PairSites.leftRotation0 k) (PairSites.leftRotation1 k)
          working rest) =
      some (pairAfterHelperBeforeJump s
        (pcAfter site.helper.startPC
          (pairBeforeJumpTemplate (k.val / 8) (PairSites.leftConstant k)))
        site.returnPC (k.val / 8) working
        (PairSites.leftAddress0 k) (PairSites.leftAddress1 k)
        (PairSites.leftRotation0 k) (PairSites.leftRotation1 k)
        (PairSites.leftConstant k) rest) := by
    exact PairRawTrace.runInstrSeq_template (k.val / 8) (by omega) s
      site.helper.startPC (PairSites.leftAddress0 k) (PairSites.leftAddress1 k)
      site.returnPC (PairSites.leftRotation0 k) (PairSites.leftRotation1 k)
      working (PairSites.leftConstant k) rest
      (fun h => leftConstant_zero k h) hstack hrun
      (PairSites.leftRotation0_le32 k) (PairSites.leftRotation1_le32 k)
  have ghelper := PairHelperTrace.gasSteps_helper_of_raw
    (j := k.val / 8) (hj := by omega) (p0 := PairSites.leftAddress0 k)
    (p1 := PairSites.leftAddress1 k)
    (r0 := PairSites.leftRotation0 k) (r1 := PairSites.leftRotation1 k)
    (constant := PairSites.leftConstant k) site.helper s site.returnPC working rest
    hraw hrun hcode hfork hnp
  have g := PairHelperTrace.gasSteps_pair_of_helper
    (j := k.val / 8) (p0 := PairSites.leftAddress0 k)
    (p1 := PairSites.leftAddress1 k)
    (r0 := PairSites.leftRotation0 k) (r1 := PairSites.leftRotation1 k)
    (constant := PairSites.leftConstant k) site s working rest hstack hrun hcode
    hfork hnp ghelper
  have ha := leftPair_activeWords s k hactive
  have g' := g.cast
    (by
      rw [PairSites.leftRoundSite_start k])
    (by
      rw [PairSites.leftRoundSite_end k, ha]
      )
  exact g'

def gasSteps_rightPair (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rest : List UInt256) (k : Fin 40)
    (_hwords : ∀ i, i < 16 →
      Word.toUInt32 (MachineState.readWord s.memory (644 + 4 * i)) = word i)
    (hactive : 67 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (roundEntry s (PairSites.rightPC k.val) working.a working.b working.c
        working.d working.e rest)
      {s with
        pc := PairSites.rightPC (k.val + 1)
        stack := roundWords
          (purePairWorking s working (4 - k.val / 8)
            (PairSites.rightAddress0 k) (PairSites.rightAddress1 k)
            (PairSites.rightRotation0 k) (PairSites.rightRotation1 k)
            (PairSites.rightConstant k)) ++ rest
        activeWords := s.activeWords} := by
  let site := PairSites.rightRoundSite k
  have hraw :
      runInstrSeq
          (pairBeforeJumpTemplate (4 - k.val / 8) (PairSites.rightConstant k))
        (pairHelperEntry s site.helper.startPC (PairSites.rightAddress0 k)
          (PairSites.rightAddress1 k) site.returnPC
          (PairSites.rightRotation0 k) (PairSites.rightRotation1 k)
          working rest) =
      some (pairAfterHelperBeforeJump s
        (pcAfter site.helper.startPC
          (pairBeforeJumpTemplate (4 - k.val / 8) (PairSites.rightConstant k)))
        site.returnPC (4 - k.val / 8) working
        (PairSites.rightAddress0 k) (PairSites.rightAddress1 k)
        (PairSites.rightRotation0 k) (PairSites.rightRotation1 k)
        (PairSites.rightConstant k) rest) := by
    exact PairRawTrace.runInstrSeq_template (4 - k.val / 8) (by omega) s
      site.helper.startPC (PairSites.rightAddress0 k) (PairSites.rightAddress1 k)
      site.returnPC (PairSites.rightRotation0 k) (PairSites.rightRotation1 k)
      working (PairSites.rightConstant k) rest
      (fun h => rightConstant_zero k h) hstack hrun
      (PairSites.rightRotation0_le32 k) (PairSites.rightRotation1_le32 k)
  have ghelper := PairHelperTrace.gasSteps_helper_of_raw
    (j := 4 - k.val / 8) (hj := by omega) (p0 := PairSites.rightAddress0 k)
    (p1 := PairSites.rightAddress1 k)
    (r0 := PairSites.rightRotation0 k) (r1 := PairSites.rightRotation1 k)
    (constant := PairSites.rightConstant k) site.helper s site.returnPC working rest
    hraw hrun hcode hfork hnp
  have g := PairHelperTrace.gasSteps_pair_of_helper
    (j := 4 - k.val / 8) (p0 := PairSites.rightAddress0 k)
    (p1 := PairSites.rightAddress1 k)
    (r0 := PairSites.rightRotation0 k) (r1 := PairSites.rightRotation1 k)
    (constant := PairSites.rightConstant k) site s working rest hstack hrun hcode
    hfork hnp ghelper
  have ha := rightPair_activeWords s k hactive
  have g' := g.cast
    (by
      rw [PairSites.rightRoundSite_start k])
    (by
      rw [PairSites.rightRoundSite_end k, ha]
      )
  exact g'

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundCertificates
