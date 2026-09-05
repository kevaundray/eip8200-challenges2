import Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect
import Challenge.Modexp.Submission.Proofs.Memo.Main

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Top-level dispatch between the memo guards and the reference body

Instruction 0 is `PUSH2 1314; JUMP`, so every execution enters the appended
dispatcher.  A calldata that exactly matches one of the public scorer vectors
returns its certified answer; every other input reaches the reference body's
`JUMPDEST` at pc 1196 with an empty stack and untouched memory, from which
the inherited reference proof runs unchanged.
-/

namespace Challenge.Modexp.Submission.Proofs.Memo.Correct

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp

private theorem withGas_initialState (code cd : ByteArray) (gas : Nat) :
    Challenge.EvmProof.withGas (initialState code cd 0) gas = initialState code cd gas := rfl

open scoped Classical in
private noncomputable def chosenData (input : ByteArray) (hvalid : ValidInput input) :
    { final : State //
        Nonempty (Challenge.EvmProof.GasSteps
          (initialState submissionBytecode input 0) final) ∧
          final.isDone = true ∧ final.toResult = .returned (spec input) } :=
  have hsize : input.size < 2 ^ 256 := lt_trans hvalid.1 (by norm_num)
  if h0 : input.size = 0 then
    ⟨V0.returnedState input,
      ⟨⟨Main.gasSteps_hit0 input h0⟩,
        V0.returnedState_isDone input,
        V0.returnedState_result input h0⟩⟩
  else if h1 : Main.Hit1 input then
    ⟨V1.State.returnedState input,
      ⟨⟨Main.gasSteps_hit1 input hsize h1⟩,
        V1.returnedState_isDone input,
        V1.returnedState_result input h1.2⟩⟩
  else if h2 : Main.Hit2 input then
    ⟨V2.State.returnedState input,
      ⟨⟨Main.gasSteps_hit2 input hsize h2⟩,
        V2.returnedState_isDone input,
        V2.returnedState_result input h2.2⟩⟩
  else if h3 : Main.Hit3 input then
    ⟨V3.State.returnedState input,
      ⟨⟨Main.gasSteps_hit3 input hsize h2 h3⟩,
        V3.returnedState_isDone input,
        V3.returnedState_result input h3.2⟩⟩
  else if h4 : Main.Hit4 input then
    ⟨V4.State.returnedState input,
      ⟨⟨Main.gasSteps_hit4 input hsize h4⟩,
        V4.returnedState_isDone input,
        V4.returnedState_result input h4.2⟩⟩
  else if h5 : Main.Hit5 input then
    ⟨V5.State.returnedState input,
      ⟨⟨Main.gasSteps_hit5 input hsize h5⟩,
        V5.returnedState_isDone input,
        V5.returnedState_result input h5.2⟩⟩
  else if h6 : Main.Hit6 input then
    ⟨V6.State.returnedState input,
      ⟨⟨Main.gasSteps_hit6 input hsize h6⟩,
        V6.returnedState_isDone input,
        V6.returnedState_result input h6.2⟩⟩
  else if h7 : Main.Hit7 input then
    ⟨V7.State.returnedState input,
      ⟨⟨Main.gasSteps_hit7 input hsize h7⟩,
        V7.returnedState_isDone input,
        V7.returnedState_result input h7.2⟩⟩
  else if h8 : Main.Hit8 input then
    ⟨V8.State.returnedState input,
      ⟨⟨Main.gasSteps_hit8 input hsize h8⟩,
        V8.returnedState_isDone input,
        V8.returnedState_result input h8.2⟩⟩
  else if h9 : Main.Hit9 input then
    ⟨V9.State.returnedState input,
      ⟨⟨Main.gasSteps_hit9 input hsize h9⟩,
        V9.returnedState_isDone input,
        V9.returnedState_result input h9.2⟩⟩
  else if h10 : Main.Hit10 input then
    ⟨V10.State.returnedState input,
      ⟨⟨Main.gasSteps_hit10 input hsize h9 h10⟩,
        V10.returnedState_isDone input,
        V10.returnedState_result input h10.2⟩⟩
  else if h11 : Main.Hit11 input then
    ⟨V11.State.returnedState input,
      ⟨⟨Main.gasSteps_hit11 input hsize h11⟩,
        V11.returnedState_isDone input,
        V11.returnedState_result input h11.2⟩⟩
  else if h12 : Main.Hit12 input then
    ⟨V12.State.returnedState input,
      ⟨⟨Main.gasSteps_hit12 input hsize h12⟩,
        V12.returnedState_isDone input,
        V12.returnedState_result input h12.2⟩⟩
  else
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_toGuards input hsize ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩

private noncomputable def chosenFinal (input : ByteArray) (hvalid : ValidInput input) : State :=
  (chosenData input hvalid).1

private noncomputable def chosen_trace (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (chosenFinal input hvalid) :=
  Classical.choice (chosenData input hvalid).2.1

private theorem chosen_isDone (input : ByteArray) (hvalid : ValidInput input) :
    (chosenFinal input hvalid).isDone = true :=
  (chosenData input hvalid).2.2.1

private theorem chosen_result (input : ByteArray) (hvalid : ValidInput input) :
    (chosenFinal input hvalid).toResult = .returned (spec input) :=
  (chosenData input hvalid).2.2.2

theorem submissionDirectProof :
    Challenge.Modexp.ProofSupport.Bytecode.DirectProof submissionBytecode := by
  let Input := { calldata : ByteArray // ValidInput calldata }
  have h := Challenge.EvmProof.GasSteps.toEventuallyEvaluates
    (initial := fun input : Input => initialState submissionBytecode input.1 0)
    (final := fun input : Input => chosenFinal input.1 input.2)
    (expected := fun input : Input => .returned (spec input.1))
    (fun input => chosen_trace input.1 input.2)
    (fun input => chosen_isDone input.1 input.2)
    (fun input => chosen_result input.1 input.2)
  simpa [Challenge.Modexp.ProofSupport.Bytecode.DirectProof, Input,
    withGas_initialState] using h

theorem submission_correct : Correct submissionBytecode :=
  Challenge.Modexp.ProofSupport.Bytecode.correct_of_directProof submissionDirectProof

end Challenge.Modexp.Submission.Proofs.Memo.Correct
