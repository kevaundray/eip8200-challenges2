import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactPaths

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactCodecopy

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactBodyState

def gasSteps_codecopy (s : State) (input : ByteArray) (i : Nat)
    (hi : i < 16)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (preCopyState s input i) (copiedState s input i) := by
  let pre := preCopyState s input i
  let cost := Gas.codecopyTotal pre (UInt256.ofNat 0) (UInt256.ofNat 20)
  refine GasSteps.one cost ?_
  intro gas hgas
  have hcode' : (withGas pre gas).executionEnv.code =
      Artifact.submissionArtifact.code := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  have hpc : (withGas pre gas).pc.toNat =
      Artifact.submissionArtifact.instructionPC 2876 := by
    change (UInt256.ofNat 0x132e).toNat =
      Artifact.submissionArtifact.instructionPC 2876
    rw [KnownInputCompactPaths.pc2876]
    decide
  have hdec := Challenge.EvmProof.Stepper.decodes_of_artifact
    Artifact.submissionArtifact (withGas pre gas) 2876 (.op .CODECOPY)
    hcode' hpc (by rfl) (by exact ⟨by decide, trivial, rfl⟩)
  change (withGas pre gas).decodedOp = some .CODECOPY at hdec
  apply EVM.Step.running
  · simpa [pre, preCopyState, withGas] using hrun
  · simpa [pre, preCopyState, withGas] using hnp
  · have hstack : (withGas pre gas).stack =
        UInt256.ofNat 0 :: UInt256.ofNat (tableSource i) ::
          UInt256.ofNat 20 ::
          [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x436,
            DriverTrace.blockOffsetWord i, Padding.paddedWord input] := by
      rfl
    have hcap : (withGas pre gas).stack.length +
        Operation.pushArity .CODECOPY ≤ 1024 + Operation.popArity .CODECOPY := by
      norm_num [pre, preCopyState, withGas, Operation.pushArity,
        Operation.popArity]
    have hsource : tableSource i < 2 ^ 256 := by
      unfold tableSource
      omega
    have hsource' : 4958 + 21 * i < 2 ^ 256 := by
      simpa [tableSource] using hsource
    have hsourceMod :
        (4958 + 21 * i) %
            115792089237316195423570985008687907853269984665640564039457584007913129639936 =
          4958 + 21 * i := by
      apply Nat.mod_eq_of_lt
      simpa using hsource'
    have hstep := StepRunning.codecopy (withGas pre gas)
      (UInt256.ofNat 0) (UInt256.ofNat (tableSource i)) (UInt256.ofNat 20)
      [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x436,
        DriverTrace.blockOffsetWord i, Padding.paddedWord input]
      hdec hstack hgas hcap
    simpa [pre, cost, preCopyState, copiedState, withGas,
      Gas.codecopyTotal, tableSource,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hsource, Nat.mod_eq_of_lt hsource',
      hsourceMod,
      Challenge.EvmProof.Word.succ_ofNat (n := 4910) (by norm_num)] using hstep

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactCodecopy
