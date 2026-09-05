import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSemantic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSitesLeft
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSitesRight
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-!
# H30b four-round certificates

This module composes the generic quad raw trace with the concrete combined
artifact sites.  It contains no outer frame, schedule, tail, or correctness
theorem.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundCertificates

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCallTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSemantic
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression

abbrev Artifact := QuadSites.Artifact
abbrev low32DenseWordsAt := QuadSemantic.DenseWordsAt

def stateAt (s : State) (pc : UInt256) (working : Compression.EvmWorking)
    (rho : List UInt256) : State :=
  roundEntry s pc working.a working.b working.c working.d working.e
    (QuadRoundTemplate.factor :: rho)

def left4 (word : Nat → UInt32) (k : Fin 20)
    (working : Compression.EvmWorking) : Compression.EvmWorking :=
  StackCompression.leftStep word (quadIndex k 3)
    (StackCompression.leftStep word (quadIndex k 2)
      (StackCompression.leftStep word (quadIndex k 1)
        (StackCompression.leftStep word (quadIndex k 0) working)))

def right4 (word : Nat → UInt32) (k : Fin 20)
    (working : Compression.EvmWorking) : Compression.EvmWorking :=
  StackCompression.rightStep word (quadIndex k 3)
    (StackCompression.rightStep word (quadIndex k 2)
      (StackCompression.rightStep word (quadIndex k 1)
        (StackCompression.rightStep word (quadIndex k 0) working)))

private theorem leftAddress0_eq (k : Fin 20) :
    QuadSites.leftAddress0 k = quadLeftAddress k 0 := by
  fin_cases k <;> rfl

private theorem leftAddress1_eq (k : Fin 20) :
    QuadSites.leftAddress1 k = quadLeftAddress k 1 := by
  fin_cases k <;> rfl

private theorem leftAddress2_eq (k : Fin 20) :
    QuadSites.leftAddress2 k = quadLeftAddress k 2 := by
  fin_cases k <;> rfl

private theorem leftAddress3_eq (k : Fin 20) :
    QuadSites.leftAddress3 k = quadLeftAddress k 3 := by
  fin_cases k <;> rfl

private theorem rightAddress0_eq (k : Fin 20) :
    QuadSites.rightAddress0 k = quadRightAddress k 0 := by
  fin_cases k <;> rfl

private theorem rightAddress1_eq (k : Fin 20) :
    QuadSites.rightAddress1 k = quadRightAddress k 1 := by
  fin_cases k <;> rfl

private theorem rightAddress2_eq (k : Fin 20) :
    QuadSites.rightAddress2 k = quadRightAddress k 2 := by
  fin_cases k <;> rfl

private theorem rightAddress3_eq (k : Fin 20) :
    QuadSites.rightAddress3 k = quadRightAddress k 3 := by
  fin_cases k <;> rfl

private theorem leftRotation0_eq (k : Fin 20) :
    QuadSites.leftRotation0 k = quadLeftRotation k 0 := by
  fin_cases k <;> rfl

private theorem leftRotation1_eq (k : Fin 20) :
    QuadSites.leftRotation1 k = quadLeftRotation k 1 := by
  fin_cases k <;> rfl

private theorem leftRotation2_eq (k : Fin 20) :
    QuadSites.leftRotation2 k = quadLeftRotation k 2 := by
  fin_cases k <;> rfl

private theorem leftRotation3_eq (k : Fin 20) :
    QuadSites.leftRotation3 k = quadLeftRotation k 3 := by
  fin_cases k <;> rfl

private theorem rightRotation0_eq (k : Fin 20) :
    QuadSites.rightRotation0 k = quadRightRotation k 0 := by
  fin_cases k <;> rfl

private theorem rightRotation1_eq (k : Fin 20) :
    QuadSites.rightRotation1 k = quadRightRotation k 1 := by
  fin_cases k <;> rfl

private theorem rightRotation2_eq (k : Fin 20) :
    QuadSites.rightRotation2 k = quadRightRotation k 2 := by
  fin_cases k <;> rfl

private theorem rightRotation3_eq (k : Fin 20) :
    QuadSites.rightRotation3 k = quadRightRotation k 3 := by
  fin_cases k <;> rfl

private theorem leftConstant_eq (k : Fin 20) :
    QuadSites.leftConstant k = quadLeftConstant k := by
  fin_cases k <;> rfl

private theorem rightConstant_eq (k : Fin 20) :
    QuadSites.rightConstant k = quadRightConstant k := by
  fin_cases k <;> rfl

private theorem leftConstant_zero (k : Fin 20)
    (hzero : k.val / 4 = 0) : QuadSites.leftConstant k = 0 := by
  fin_cases k <;>
    simp_all [QuadSites.leftConstant, StackRoundData.leftConstant] <;>
    decide

private theorem rightConstant_zero (k : Fin 20)
    (hzero : 4 - k.val / 4 = 0) : QuadSites.rightConstant k = 0 := by
  fin_cases k <;>
    simp_all [QuadSites.rightConstant, StackRoundData.rightConstant] <;>
    decide

private theorem leftRotation0_le32 (k : Fin 20) :
    QuadSites.leftRotation0 k ≤ 32 := by
  rw [leftRotation0_eq k]
  exact quadLeftRotation_le_32 k 0

private theorem leftRotation1_le32 (k : Fin 20) :
    QuadSites.leftRotation1 k ≤ 32 := by
  rw [leftRotation1_eq k]
  exact quadLeftRotation_le_32 k 1

private theorem leftRotation2_le32 (k : Fin 20) :
    QuadSites.leftRotation2 k ≤ 32 := by
  rw [leftRotation2_eq k]
  exact quadLeftRotation_le_32 k 2

private theorem leftRotation3_le32 (k : Fin 20) :
    QuadSites.leftRotation3 k ≤ 32 := by
  rw [leftRotation3_eq k]
  exact quadLeftRotation_le_32 k 3

private theorem rightRotation0_le32 (k : Fin 20) :
    QuadSites.rightRotation0 k ≤ 32 := by
  rw [rightRotation0_eq k]
  exact quadRightRotation_le_32 k 0

private theorem rightRotation1_le32 (k : Fin 20) :
    QuadSites.rightRotation1 k ≤ 32 := by
  rw [rightRotation1_eq k]
  exact quadRightRotation_le_32 k 1

private theorem rightRotation2_le32 (k : Fin 20) :
    QuadSites.rightRotation2 k ≤ 32 := by
  rw [rightRotation2_eq k]
  exact quadRightRotation_le_32 k 2

private theorem rightRotation3_le32 (k : Fin 20) :
    QuadSites.rightRotation3 k ≤ 32 := by
  rw [rightRotation3_eq k]
  exact quadRightRotation_le_32 k 3

private theorem leftWorking_eq (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (k : Fin 20)
    (hwords : low32DenseWordsAt s word) :
    QuadRoundState.quadWorking s working (k.val / 4)
        (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k)
        (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k)
        (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k)
        (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k)
        (QuadSites.leftConstant k) = left4 word k working := by
  have h := QuadSemantic.quadWorking_left s word working k hwords
  rw [leftAddress0_eq k, leftAddress1_eq k, leftAddress2_eq k,
    leftAddress3_eq k, leftRotation0_eq k, leftRotation1_eq k,
    leftRotation2_eq k, leftRotation3_eq k, leftConstant_eq k]
  simpa [left4] using h

private theorem rightWorking_eq (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (k : Fin 20)
    (hwords : low32DenseWordsAt s word) :
    QuadRoundState.quadWorking s working (4 - k.val / 4)
        (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k)
        (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k)
        (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k)
        (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k)
        (QuadSites.rightConstant k) = right4 word k working := by
  have h := QuadSemantic.quadWorking_right s word working k hwords
  rw [rightAddress0_eq k, rightAddress1_eq k, rightAddress2_eq k,
    rightAddress3_eq k, rightRotation0_eq k, rightRotation1_eq k,
    rightRotation2_eq k, rightRotation3_eq k, rightConstant_eq k]
  simpa [right4] using h

private theorem leftActiveWords_eq (s : State) (k : Fin 20)
    (hactive : 66 ≤ s.activeWords.toNat) :
    QuadRoundState.quadActiveWordsAfterUInt256_4 s
        (QuadSites.leftAddress0 k).toNat (QuadSites.leftAddress1 k).toNat
        (QuadSites.leftAddress2 k).toNat (QuadSites.leftAddress3 k).toNat =
      s.activeWords := by
  rw [leftAddress0_eq k, leftAddress1_eq k, leftAddress2_eq k,
    leftAddress3_eq k]
  exact QuadSemantic.quadLeftActiveWords_unchanged s k hactive

private theorem rightActiveWords_eq (s : State) (k : Fin 20)
    (hactive : 66 ≤ s.activeWords.toNat) :
    QuadRoundState.quadActiveWordsAfterUInt256_4 s
        (QuadSites.rightAddress0 k).toNat (QuadSites.rightAddress1 k).toNat
        (QuadSites.rightAddress2 k).toNat (QuadSites.rightAddress3 k).toNat =
      s.activeWords := by
  rw [rightAddress0_eq k, rightAddress1_eq k, rightAddress2_eq k,
    rightAddress3_eq k]
  exact QuadSemantic.quadRightActiveWords_unchanged s k hactive

def gasSteps_leftQuad (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256) (k : Fin 20)
    (hwords : low32DenseWordsAt s word)
    (hactive : 66 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1007)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (stateAt s (QuadSites.leftPC k.val) working rho)
      (stateAt s (QuadSites.leftPC (k.val + 1)) (left4 word k working) rho) := by
  let site := QuadSites.leftRoundSite k
  have hraw :
      runInstrSeq
          (quadBeforeJumpTemplate (k.val / 4) (QuadSites.leftConstant k))
        (quadHelperEntry s site.helper.startPC
          (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k)
          (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k)
          site.returnPC (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k)
          (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k)
          working rho) =
      some (quadAfterHelperBeforeJump s
        (pcAfter site.helper.startPC
          (quadBeforeJumpTemplate (k.val / 4) (QuadSites.leftConstant k)))
        site.returnPC (k.val / 4) working
        (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k)
        (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k)
        (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k)
        (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k)
        (QuadSites.leftConstant k) rho) := by
    exact QuadRoundTrace.runInstrSeq_quad (k.val / 4) (by omega) s
      site.helper.startPC (QuadSites.leftAddress0 k) (QuadSites.leftAddress1 k)
      (QuadSites.leftAddress2 k) (QuadSites.leftAddress3 k) site.returnPC
      (QuadSites.leftRotation0 k) (QuadSites.leftRotation1 k)
      (QuadSites.leftRotation2 k) (QuadSites.leftRotation3 k) working
      (QuadSites.leftConstant k) rho
      (fun h => leftConstant_zero k h) hstack hrun
      (leftRotation0_le32 k) (leftRotation1_le32 k)
      (leftRotation2_le32 k) (leftRotation3_le32 k)
  have ghelper := QuadHelperTrace.gasSteps_helper_of_raw
    (j := k.val / 4) (hj := by omega)
    (p0 := QuadSites.leftAddress0 k) (p1 := QuadSites.leftAddress1 k)
    (p2 := QuadSites.leftAddress2 k) (p3 := QuadSites.leftAddress3 k)
    (r0 := QuadSites.leftRotation0 k) (r1 := QuadSites.leftRotation1 k)
    (r2 := QuadSites.leftRotation2 k) (r3 := QuadSites.leftRotation3 k)
    (constant := QuadSites.leftConstant k) site.helper s site.returnPC working rho
    hraw hrun hcode hfork hnp
  have g := QuadHelperTrace.gasSteps_quad_of_helper
    (j := k.val / 4) (p0 := QuadSites.leftAddress0 k)
    (p1 := QuadSites.leftAddress1 k) (p2 := QuadSites.leftAddress2 k)
    (p3 := QuadSites.leftAddress3 k)
    (r0 := QuadSites.leftRotation0 k) (r1 := QuadSites.leftRotation1 k)
    (r2 := QuadSites.leftRotation2 k) (r3 := QuadSites.leftRotation3 k)
    (constant := QuadSites.leftConstant k) site s working rho hstack hrun hcode
    hfork hnp ghelper
  have hw := leftWorking_eq s word working k hwords
  have ha := leftActiveWords_eq s k hactive
  exact g.cast
    (by
      simp only [stateAt]
      rw [QuadSites.leftRoundSite_start k])
    (by
      simp only [stateAt, StackRoundTrace.roundEntry, StackRoundTrace.roundWords]
      rw [QuadSites.leftRoundSite_end k, hw, ha]
      rfl)

def gasSteps_rightQuad (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256) (k : Fin 20)
    (hwords : low32DenseWordsAt s word)
    (hactive : 66 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1007)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (stateAt s (QuadSites.rightPC k.val) working rho)
      (stateAt s (QuadSites.rightPC (k.val + 1)) (right4 word k working) rho) := by
  let site := QuadSites.rightRoundSite k
  have hraw :
      runInstrSeq
          (quadBeforeJumpTemplate (4 - k.val / 4) (QuadSites.rightConstant k))
        (quadHelperEntry s site.helper.startPC
          (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k)
          (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k)
          site.returnPC (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k)
          (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k)
          working rho) =
      some (quadAfterHelperBeforeJump s
        (pcAfter site.helper.startPC
          (quadBeforeJumpTemplate (4 - k.val / 4) (QuadSites.rightConstant k)))
        site.returnPC (4 - k.val / 4) working
        (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k)
        (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k)
        (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k)
        (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k)
        (QuadSites.rightConstant k) rho) := by
    exact QuadRoundTrace.runInstrSeq_quad (4 - k.val / 4) (by omega) s
      site.helper.startPC (QuadSites.rightAddress0 k) (QuadSites.rightAddress1 k)
      (QuadSites.rightAddress2 k) (QuadSites.rightAddress3 k) site.returnPC
      (QuadSites.rightRotation0 k) (QuadSites.rightRotation1 k)
      (QuadSites.rightRotation2 k) (QuadSites.rightRotation3 k) working
      (QuadSites.rightConstant k) rho
      (fun h => rightConstant_zero k h) hstack hrun
      (rightRotation0_le32 k) (rightRotation1_le32 k)
      (rightRotation2_le32 k) (rightRotation3_le32 k)
  have ghelper := QuadHelperTrace.gasSteps_helper_of_raw
    (j := 4 - k.val / 4) (hj := by omega)
    (p0 := QuadSites.rightAddress0 k) (p1 := QuadSites.rightAddress1 k)
    (p2 := QuadSites.rightAddress2 k) (p3 := QuadSites.rightAddress3 k)
    (r0 := QuadSites.rightRotation0 k) (r1 := QuadSites.rightRotation1 k)
    (r2 := QuadSites.rightRotation2 k) (r3 := QuadSites.rightRotation3 k)
    (constant := QuadSites.rightConstant k) site.helper s site.returnPC working rho
    hraw hrun hcode hfork hnp
  have g := QuadHelperTrace.gasSteps_quad_of_helper
    (j := 4 - k.val / 4) (p0 := QuadSites.rightAddress0 k)
    (p1 := QuadSites.rightAddress1 k) (p2 := QuadSites.rightAddress2 k)
    (p3 := QuadSites.rightAddress3 k)
    (r0 := QuadSites.rightRotation0 k) (r1 := QuadSites.rightRotation1 k)
    (r2 := QuadSites.rightRotation2 k) (r3 := QuadSites.rightRotation3 k)
    (constant := QuadSites.rightConstant k) site s working rho hstack hrun hcode
    hfork hnp ghelper
  have hw := rightWorking_eq s word working k hwords
  have ha := rightActiveWords_eq s k hactive
  exact g.cast
    (by
      simp only [stateAt]
      rw [QuadSites.rightRoundSite_start k])
    (by
      simp only [stateAt, StackRoundTrace.roundEntry, StackRoundTrace.roundWords]
      rw [QuadSites.rightRoundSite_end k, hw, ha]
      rfl)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundCertificates
