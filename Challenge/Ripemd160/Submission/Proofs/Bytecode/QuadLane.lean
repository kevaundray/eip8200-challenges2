import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundCertificates

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-!
# H30b four-round lanes

This module iterates the concrete four-round certificates.  Frame, schedule,
tail, and full correctness composition remain outside this file.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLane

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundCertificates
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSemantic
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression

abbrev Artifact := QuadSites.Artifact
abbrev low32DenseWordsAt := QuadSemantic.DenseWordsAt

def stateAt (s : State) (pc : UInt256) (working : Compression.EvmWorking)
    (rho : List UInt256) : State :=
  StackRoundTrace.roundEntry s pc working.a working.b working.c working.d working.e
    (QuadRoundTemplate.factor :: rho)

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
      (stateAt s (QuadSites.leftPC (k.val + 1))
        (QuadRoundCertificates.left4 word k working) rho) := by
  simpa only [stateAt, QuadRoundCertificates.stateAt] using
    (QuadRoundCertificates.gasSteps_leftQuad s word working rho k
      hwords hactive hstack hcode hfork hrun hnp)

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
      (stateAt s (QuadSites.rightPC (k.val + 1))
        (QuadRoundCertificates.right4 word k working) rho) := by
  simpa only [stateAt, QuadRoundCertificates.stateAt] using
    (QuadRoundCertificates.gasSteps_rightQuad s word working rho k
      hwords hactive hstack hcode hfork hrun hnp)

def gasSteps_left80 (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hwords : low32DenseWordsAt s word)
    (hactive : 66 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1007)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (stateAt s (QuadSites.leftPC 0) working rho)
      (stateAt s (QuadSites.leftPC 20)
        (StackCompression.leftRounds word 80 working) rho) := by
  let states := fun n => stateAt s (QuadSites.leftPC n)
    (StackCompression.leftRounds word (4 * n) working) rho
  have step (i : Nat) (hi : i < 20) :
      GasSteps (states i) (states (i + 1)) := by
    let k : Fin 20 := ⟨i, hi⟩
    have g := gasSteps_leftQuad s word
      (StackCompression.leftRounds word (4 * i) working) rho k
      hwords hactive hstack hcode hfork hrun hnp
    have hnext :
        StackCompression.leftRounds word (4 * (i + 1)) working =
          QuadRoundCertificates.left4 word k
            (StackCompression.leftRounds word (4 * i) working) := by
      rw [QuadSemantic.leftRounds_quad word i working]
      rfl
    apply g.cast
    · rfl
    · simp only [states, stateAt, StackRoundTrace.roundEntry, k]
      rw [hnext]
  have g := GasSteps.iterateBounded 20 step
  simpa only [states, Nat.mul_zero, StackCompression.leftRounds] using g

def gasSteps_right80 (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hwords : low32DenseWordsAt s word)
    (hactive : 66 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1007)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (stateAt s (QuadSites.rightPC 0) working rho)
      (stateAt s (QuadSites.rightPC 20)
        (StackCompression.rightRounds word 80 working) rho) := by
  let states := fun n => stateAt s (QuadSites.rightPC n)
    (StackCompression.rightRounds word (4 * n) working) rho
  have step (i : Nat) (hi : i < 20) :
      GasSteps (states i) (states (i + 1)) := by
    let k : Fin 20 := ⟨i, hi⟩
    have g := gasSteps_rightQuad s word
      (StackCompression.rightRounds word (4 * i) working) rho k
      hwords hactive hstack hcode hfork hrun hnp
    have hnext :
        StackCompression.rightRounds word (4 * (i + 1)) working =
          QuadRoundCertificates.right4 word k
            (StackCompression.rightRounds word (4 * i) working) := by
      rw [QuadSemantic.rightRounds_quad word i working]
      rfl
    apply g.cast
    · rfl
    · simp only [states, stateAt, StackRoundTrace.roundEntry, k]
      rw [hnext]
  have g := GasSteps.iterateBounded 20 step
  simpa only [states, Nat.mul_zero, StackCompression.rightRounds] using g

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLane
