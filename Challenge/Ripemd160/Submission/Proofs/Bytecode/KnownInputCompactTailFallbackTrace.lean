import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactGuardTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactTailFallbackTrace

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputState KnownInputCompactPaths KnownInputCompactState

private abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

theorem run_tail_fallback (s : State) (input : ByteArray) (i : Nat)
    (hsize : input.size = 1000) (hne : input ≠ KnownInputData.targetInput)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run tailPath (loopExitState s input i) = some (legacyEntry s input i) := by
  have hneAcc : finalAcc input ≠ 0 := by
    intro hz
    exact hne ((KnownInputCompactLogic.finalAcc_zero_iff_target input hsize).1 hz)
  have htrue : UInt256.isTrue (finalAcc input) := by
    intro hnat
    apply hneAcc
    apply Challenge.EvmProof.Word.word_ext
    simpa using hnat
  have htrue' : UInt256.isTrue
      (UInt256.lor
        (UInt256.xor
          (UInt256.shiftRight (referenceWord input) (UInt256.ofNat 192))
          (UInt256.shiftRight (MachineState.readWord input 992)
            (UInt256.ofNat 192)))
        (loopAcc input 30)) := by
    have hxor : UInt256.xor
        (UInt256.shiftRight (referenceWord input) (UInt256.ofNat 192))
        (UInt256.shiftRight (MachineState.readWord input 992)
          (UInt256.ofNat 192)) =
      UInt256.xor
        (UInt256.shiftRight (MachineState.readWord input 992)
          (UInt256.ofNat 192))
        (UInt256.shiftRight (referenceWord input) (UInt256.ofNat 192)) :=
      BooleanSelect.xor_comm _ _
    have heq : UInt256.lor
        (UInt256.xor
          (UInt256.shiftRight (referenceWord input) (UInt256.ofNat 192))
          (UInt256.shiftRight (MachineState.readWord input 992)
            (UInt256.ofNat 192)))
        (loopAcc input 30) = finalAcc input := by
      rw [finalAcc]
      exact congrArg (fun x => UInt256.lor x (loopAcc input 30)) hxor
    rw [heq]
    exact htrue
  have hdest : Decode.isValidJumpDest submissionBytecode 0x129e = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2792 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [tailPath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
    KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopExitState, legacyEntry, finalAcc, hcalldata, hcode, hrun, htrue', hdest,
    List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactTailFallbackTrace
