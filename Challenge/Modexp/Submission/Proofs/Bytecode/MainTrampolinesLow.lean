import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
import Challenge.Modexp.Submission.Proofs.Memo.Step
import Challenge.Modexp.Submission.Proofs.Bytecode.MainTrampolinesLow.T1
import Challenge.Modexp.Submission.Proofs.Bytecode.MainTrampolinesLow.T2
import Challenge.Modexp.Submission.Proofs.Bytecode.MainTrampolinesLow.T3
import Challenge.Modexp.Submission.Proofs.Bytecode.MainTrampolinesLow.T4
import Challenge.Modexp.Submission.Proofs.Bytecode.MainTrampolinesLow.T5
import Challenge.Modexp.Submission.Proofs.Bytecode.MainTrampolinesLow.T6
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

private def tramp0MidState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 3
      stack := [UInt256.ofNat 1314] }

theorem run_tramp0_push (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated tramp0PushLocated
      (initialState submissionBytecode input 0) = some (tramp0MidState input) := by
  have hpc : (initialState submissionBytecode input 0).pc.toNat =
      Artifact.submissionArtifact.instructionPC 0 := by rfl
  unfold Challenge.EvmProof.Stepper.runLocated
  change (if (initialState submissionBytecode input 0).pc.toNat =
      Artifact.submissionArtifact.instructionPC 0 then
      Challenge.EvmProof.Stepper.runInstr (.push 2 (UInt256.ofNat 1314))
        (initialState submissionBytecode input 0) else none) = _
  rw [if_pos hpc]
  have hcap : (initialState submissionBytecode input 0).stack.length < 1024 := by
    change [].length < 1024
    decide
  have hwidth : ¬ (2 : Fin 33).val = 0 := by decide
  have hthree : (2 : Fin 33).val + 1 = 3 := by decide
  have hadd : UInt256.ofNat 0 + UInt256.ofNat 3 = UInt256.ofNat 3 :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos hcap]
  simp only
  rw [if_neg hwidth]
  simp only [tramp0MidState, hthree]
  rw [show (initialState submissionBytecode input 0).pc = UInt256.ofNat 0 by rfl,
    show (initialState submissionBytecode input 0).stack = [] by rfl, hadd]

theorem run_tramp0_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated tramp0JumpLocated
      (tramp0MidState input) = some (trampolineState input 1314) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1314 = true :=
    Artifact.isValidJumpDest_index 977 (by rfl)
  have hpc : (tramp0MidState input).pc.toNat =
      Artifact.submissionArtifact.instructionPC 1 := by
    simp [tramp0MidState, initialState, headerPCs0,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Challenge.Modexp.Submission.Proofs.Memo.Step.runLocated_jump tramp0JumpLocated rfl
    (tramp0MidState input) 1314 [] hpc rfl (by decide) rfl (by norm_num) hjump).trans rfl

theorem run_tramp0 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp0Path
      (initialState submissionBytecode input 0) = some (trampolineState input 1314) :=
  Challenge.Modexp.Submission.Proofs.Memo.Step.runLocatedBlock_two _ _ _ _ _
    (run_tramp0_push input) rfl (run_tramp0_jump input)

end Challenge.Modexp.Submission.Proofs.Bytecode.Main
