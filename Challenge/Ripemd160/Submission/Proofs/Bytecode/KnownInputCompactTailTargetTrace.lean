import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactGuardTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactTailTargetTrace

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputState KnownInputCompactPaths KnownInputCompactState

private abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

theorem run_tail_target (s : State) (i : Nat)
    (hcalldata : s.executionEnv.calldata = KnownInputData.targetInput)
    (hrun : s.halt = .Running) :
    run tailPath (loopExitState s KnownInputData.targetInput i) =
      some (KnownInputCompactState.bodyEntry s KnownInputData.targetInput i) := by
  have hzero : finalAcc KnownInputData.targetInput = 0 :=
    (KnownInputCompactLogic.finalAcc_zero_iff_target _
      KnownInputData.targetInput_size).2 rfl
  have hzero' : UInt256.lor
      (UInt256.xor
        (UInt256.shiftRight (referenceWord KnownInputData.targetInput)
          (UInt256.ofNat 192))
        (UInt256.shiftRight
          (MachineState.readWord KnownInputData.targetInput 992)
          (UInt256.ofNat 192)))
      (loopAcc KnownInputData.targetInput 30) = 0 := by
    have hxor : UInt256.xor
        (UInt256.shiftRight (referenceWord KnownInputData.targetInput)
          (UInt256.ofNat 192))
        (UInt256.shiftRight
          (MachineState.readWord KnownInputData.targetInput 992)
          (UInt256.ofNat 192)) =
      UInt256.xor
        (UInt256.shiftRight
          (MachineState.readWord KnownInputData.targetInput 992)
          (UInt256.ofNat 192))
        (UInt256.shiftRight (referenceWord KnownInputData.targetInput)
          (UInt256.ofNat 192)) := BooleanSelect.xor_comm _ _
    calc
      _ = UInt256.lor
          (UInt256.xor
            (UInt256.shiftRight
              (MachineState.readWord KnownInputData.targetInput 992)
              (UInt256.ofNat 192))
            (UInt256.shiftRight (referenceWord KnownInputData.targetInput)
              (UInt256.ofNat 192)))
          (loopAcc KnownInputData.targetInput 30) := congrArg
            (fun x => UInt256.lor x (loopAcc KnownInputData.targetInput 30)) hxor
      _ = 0 := by simpa only [finalAcc] using hzero
  simp (config := { maxSteps := 1000000 })
    [tailPath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
    KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopExitState, KnownInputCompactState.bodyEntry, finalAcc, hcalldata, hrun,
    hzero', List.exchange,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactTailTargetTrace
