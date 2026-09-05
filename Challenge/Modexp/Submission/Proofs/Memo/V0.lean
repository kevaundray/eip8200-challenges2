import Challenge.Modexp.Submission.Proofs.Memo.Dispatch

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V0

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo
open Dispatch

def returnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1036 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 1037 0 0,
   Main.pushAt 1038 0 0,
   Main.opAt 1039 (EvmSemantics.Operation.System (EvmSemantics.Operation.SystemOps.RETURN))
  ]

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1412
      stack := [UInt256.ofNat input.size]
      activeWords := UInt256.ofNat 0
      halt := .Returned
      hReturn := MachineState.readPadded ByteArray.empty 0 0 }

theorem run_return (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock returnPath (sizeState input 1409) =
      some (returnedState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [returnPath, sizeState, returnedState, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def gasSteps_match (input : ByteArray) :
    Challenge.EvmProof.GasSteps (sizeState input 1409) (returnedState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka returnPath
    rfl rfl (run_return input) rfl deployAddress_not_precompile

@[simp] theorem returnedState_isDone (input : ByteArray) :
    (returnedState input).isDone = true := by
  simp [returnedState, State.isDone, State.isHalted, State.isRunning]
  rfl

theorem returnedState_result (input : ByteArray) (h : input.size = 0) :
    (returnedState input).toResult = .returned (spec input) := by
  rw [State.toResult_returned _ (by rfl)]
  change ExecutionResult.returned (MachineState.readPadded ByteArray.empty 0 0) = _
  rw [Logic.eq_empty_of_size_eq_zero input h]
  rw [show MachineState.readPadded ByteArray.empty 0 0 = ByteArray.empty by decide +kernel,
    show spec ByteArray.empty = ByteArray.empty by decide +kernel]

end Challenge.Modexp.Submission.Proofs.Memo.V0
