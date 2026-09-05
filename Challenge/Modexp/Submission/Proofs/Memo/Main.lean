import Challenge.Modexp.Submission.Proofs.Memo.V0
import Challenge.Modexp.Submission.Proofs.Memo.V1
import Challenge.Modexp.Submission.Proofs.Memo.V2
import Challenge.Modexp.Submission.Proofs.Memo.V3
import Challenge.Modexp.Submission.Proofs.Memo.V4
import Challenge.Modexp.Submission.Proofs.Memo.V5
import Challenge.Modexp.Submission.Proofs.Memo.V6
import Challenge.Modexp.Submission.Proofs.Memo.V7
import Challenge.Modexp.Submission.Proofs.Memo.V8
import Challenge.Modexp.Submission.Proofs.Memo.V9
import Challenge.Modexp.Submission.Proofs.Memo.V10
import Challenge.Modexp.Submission.Proofs.Memo.V11
import Challenge.Modexp.Submission.Proofs.Memo.V12
import Challenge.Modexp.Submission.Proofs.Bytecode.MainGas

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.Main

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Dispatch

private def sound {s t : State} (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka))
    (hrun : s.halt = .Running)
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

private def soundOne {s t : State}
    {located : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka}
    (hrun : s.halt = .Running)
    (h : Challenge.EvmProof.Stepper.runLocated located s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocated_sound hcode hfork h hrun hnp

abbrev init (input : ByteArray) : State := initialState submissionBytecode input 0

def Hit1 (input : ByteArray) : Prop :=
  input.size = 99 ∧ guardDiff V1.Data.checks input = 0

def Hit2 (input : ByteArray) : Prop :=
  input.size = 98 ∧ guardDiff V2.Data.checks input = 0

def Hit3 (input : ByteArray) : Prop :=
  input.size = 98 ∧ guardDiff V3.Data.checks input = 0

def Hit4 (input : ByteArray) : Prop :=
  input.size = 110 ∧ guardDiff V4.Data.checks input = 0

def Hit5 (input : ByteArray) : Prop :=
  input.size = 161 ∧ guardDiff V5.Data.checks input = 0

def Hit6 (input : ByteArray) : Prop :=
  input.size = 160 ∧ guardDiff V6.Data.checks input = 0

def Hit7 (input : ByteArray) : Prop :=
  input.size = 100 ∧ guardDiff V7.Data.checks input = 0

def Hit8 (input : ByteArray) : Prop :=
  input.size = 163 ∧ guardDiff V8.Data.checks input = 0

def Hit9 (input : ByteArray) : Prop :=
  input.size = 192 ∧ guardDiff V9.Data.checks input = 0

def Hit10 (input : ByteArray) : Prop :=
  input.size = 192 ∧ guardDiff V10.Data.checks input = 0

def Hit11 (input : ByteArray) : Prop :=
  input.size = 353 ∧ guardDiff V11.Data.checks input = 0

def Hit12 (input : ByteArray) : Prop :=
  input.size = 611 ∧ guardDiff V12.Data.checks input = 0

structure NoHit (input : ByteArray) : Prop where
  h0 : input.size ≠ 0
  h1 : ¬ Hit1 input
  h2 : ¬ Hit2 input
  h3 : ¬ Hit3 input
  h4 : ¬ Hit4 input
  h5 : ¬ Hit5 input
  h6 : ¬ Hit6 input
  h7 : ¬ Hit7 input
  h8 : ¬ Hit8 input
  h9 : ¬ Hit9 input
  h10 : ¬ Hit10 input
  h11 : ¬ Hit11 input
  h12 : ¬ Hit12 input

def gasSteps_entry (input : ByteArray) (hsize : input.size < 2 ^ 256) (h0 : input.size ≠ 0) :
    Challenge.EvmProof.GasSteps (init input) (sizeState input 1322) :=
  (Bytecode.Main.gasSteps_entryHop input).trans
    (sound entryPath rfl (run_entry_nonempty input hsize h0) rfl rfl deployAddress_not_precompile)

def gasSteps_hit0 (input : ByteArray) (h0 : input.size = 0) :
    Challenge.EvmProof.GasSteps (init input) (V0.returnedState input) :=
  (((Bytecode.Main.gasSteps_entryHop input).trans
    (sound entryPrefixPath rfl (run_entry_empty_prefix input h0) rfl rfl deployAddress_not_precompile)).trans
    (soundOne rfl (run_entry_empty_jump input) rfl rfl deployAddress_not_precompile)).trans
    (V0.gasSteps_match input)

def gasSteps_hit1 (input : ByteArray) (hsize : input.size < 2 ^ 256) (h : Hit1 input) :
    Challenge.EvmProof.GasSteps (init input) (V1.State.returnedState input) :=
  ((gasSteps_entry input hsize (by rw [h.1]; decide)).trans
    ((sound check0PrefixPath rfl (run_check0_taken_prefix input h.1) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check0_jump input) rfl rfl deployAddress_not_precompile))).trans
    (V1.gasSteps_match input h.2)

def gasSteps_hit2 (input : ByteArray) (hsize : input.size < 2 ^ 256) (h : Hit2 input) :
    Challenge.EvmProof.GasSteps (init input) (V2.State.returnedState input) :=
  (((gasSteps_entry input hsize (by rw [h.1]; decide)).trans
    (sound check0Path rfl (run_check0_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    ((sound check1PrefixPath rfl (run_check1_taken_prefix input h.1) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check1_jump input) rfl rfl deployAddress_not_precompile))).trans
    (V2.gasSteps_match input h.2)

def gasSteps_hit3 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hk : ¬ Hit2 input) (h : Hit3 input) :
    Challenge.EvmProof.GasSteps (init input) (V3.State.returnedState input) :=
  ((((gasSteps_entry input hsize (by rw [h.1]; decide)).trans
    (sound check0Path rfl (run_check0_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    ((sound check1PrefixPath rfl (run_check1_taken_prefix input h.1) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check1_jump input) rfl rfl deployAddress_not_precompile))).trans
    (V2.gasSteps_fallback input (fun hz => hk ⟨h.1, hz⟩))).trans
    (V3.gasSteps_match input h.2)

def gasSteps_hit4 (input : ByteArray) (hsize : input.size < 2 ^ 256) (h : Hit4 input) :
    Challenge.EvmProof.GasSteps (init input) (V4.State.returnedState input) :=
  ((((gasSteps_entry input hsize (by rw [h.1]; decide)).trans
    (sound check0Path rfl (run_check0_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check1Path rfl (run_check1_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    ((sound check2PrefixPath rfl (run_check2_taken_prefix input h.1) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check2_jump input) rfl rfl deployAddress_not_precompile))).trans
    (V4.gasSteps_match input h.2)

def gasSteps_hit5 (input : ByteArray) (hsize : input.size < 2 ^ 256) (h : Hit5 input) :
    Challenge.EvmProof.GasSteps (init input) (V5.State.returnedState input) :=
  (((((gasSteps_entry input hsize (by rw [h.1]; decide)).trans
    (sound check0Path rfl (run_check0_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check1Path rfl (run_check1_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check2Path rfl (run_check2_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    ((sound check3PrefixPath rfl (run_check3_taken_prefix input h.1) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check3_jump input) rfl rfl deployAddress_not_precompile))).trans
    (V5.gasSteps_match input h.2)

def gasSteps_hit6 (input : ByteArray) (hsize : input.size < 2 ^ 256) (h : Hit6 input) :
    Challenge.EvmProof.GasSteps (init input) (V6.State.returnedState input) :=
  ((((((gasSteps_entry input hsize (by rw [h.1]; decide)).trans
    (sound check0Path rfl (run_check0_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check1Path rfl (run_check1_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check2Path rfl (run_check2_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check3Path rfl (run_check3_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    ((sound check4PrefixPath rfl (run_check4_taken_prefix input h.1) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check4_jump input) rfl rfl deployAddress_not_precompile))).trans
    (V6.gasSteps_match input h.2)

def gasSteps_hit7 (input : ByteArray) (hsize : input.size < 2 ^ 256) (h : Hit7 input) :
    Challenge.EvmProof.GasSteps (init input) (V7.State.returnedState input) :=
  (((((((gasSteps_entry input hsize (by rw [h.1]; decide)).trans
    (sound check0Path rfl (run_check0_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check1Path rfl (run_check1_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check2Path rfl (run_check2_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check3Path rfl (run_check3_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check4Path rfl (run_check4_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    ((sound check5PrefixPath rfl (run_check5_taken_prefix input h.1) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check5_jump input) rfl rfl deployAddress_not_precompile))).trans
    (V7.gasSteps_match input h.2)

def gasSteps_hit8 (input : ByteArray) (hsize : input.size < 2 ^ 256) (h : Hit8 input) :
    Challenge.EvmProof.GasSteps (init input) (V8.State.returnedState input) :=
  ((((((((gasSteps_entry input hsize (by rw [h.1]; decide)).trans
    (sound check0Path rfl (run_check0_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check1Path rfl (run_check1_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check2Path rfl (run_check2_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check3Path rfl (run_check3_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check4Path rfl (run_check4_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check5Path rfl (run_check5_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    ((sound check6PrefixPath rfl (run_check6_taken_prefix input h.1) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check6_jump input) rfl rfl deployAddress_not_precompile))).trans
    (V8.gasSteps_match input h.2)

def gasSteps_hit9 (input : ByteArray) (hsize : input.size < 2 ^ 256) (h : Hit9 input) :
    Challenge.EvmProof.GasSteps (init input) (V9.State.returnedState input) :=
  (((((((((gasSteps_entry input hsize (by rw [h.1]; decide)).trans
    (sound check0Path rfl (run_check0_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check1Path rfl (run_check1_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check2Path rfl (run_check2_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check3Path rfl (run_check3_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check4Path rfl (run_check4_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check5Path rfl (run_check5_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check6Path rfl (run_check6_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    ((sound check7PrefixPath rfl (run_check7_taken_prefix input h.1) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check7_jump input) rfl rfl deployAddress_not_precompile))).trans
    (V9.gasSteps_match input h.2)

def gasSteps_hit10 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hk : ¬ Hit9 input) (h : Hit10 input) :
    Challenge.EvmProof.GasSteps (init input) (V10.State.returnedState input) :=
  ((((((((((gasSteps_entry input hsize (by rw [h.1]; decide)).trans
    (sound check0Path rfl (run_check0_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check1Path rfl (run_check1_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check2Path rfl (run_check2_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check3Path rfl (run_check3_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check4Path rfl (run_check4_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check5Path rfl (run_check5_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check6Path rfl (run_check6_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    ((sound check7PrefixPath rfl (run_check7_taken_prefix input h.1) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check7_jump input) rfl rfl deployAddress_not_precompile))).trans
    (V9.gasSteps_fallback input (fun hz => hk ⟨h.1, hz⟩))).trans
    (V10.gasSteps_match input h.2)

def gasSteps_hit11 (input : ByteArray) (hsize : input.size < 2 ^ 256) (h : Hit11 input) :
    Challenge.EvmProof.GasSteps (init input) (V11.State.returnedState input) :=
  ((((((((((gasSteps_entry input hsize (by rw [h.1]; decide)).trans
    (sound check0Path rfl (run_check0_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check1Path rfl (run_check1_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check2Path rfl (run_check2_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check3Path rfl (run_check3_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check4Path rfl (run_check4_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check5Path rfl (run_check5_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check6Path rfl (run_check6_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check7Path rfl (run_check7_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    ((sound check8PrefixPath rfl (run_check8_taken_prefix input h.1) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check8_jump input) rfl rfl deployAddress_not_precompile))).trans
    (V11.gasSteps_match input h.2)

def gasSteps_hit12 (input : ByteArray) (hsize : input.size < 2 ^ 256) (h : Hit12 input) :
    Challenge.EvmProof.GasSteps (init input) (V12.State.returnedState input) :=
  (((((((((((gasSteps_entry input hsize (by rw [h.1]; decide)).trans
    (sound check0Path rfl (run_check0_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check1Path rfl (run_check1_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check2Path rfl (run_check2_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check3Path rfl (run_check3_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check4Path rfl (run_check4_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check5Path rfl (run_check5_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check6Path rfl (run_check6_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check7Path rfl (run_check7_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    (sound check8Path rfl (run_check8_skip input hsize (by rw [h.1]; decide)) rfl rfl deployAddress_not_precompile)).trans
    ((sound check9PrefixPath rfl (run_check9_taken_prefix input h.1) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check9_jump input) rfl rfl deployAddress_not_precompile))).trans
    (V12.gasSteps_match input h.2)

noncomputable def gasSteps_toGuards (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hno : NoHit input) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_entry input hsize hno.h0).trans (rest0 input hsize hno)
where
  rest0 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hno : NoHit input) :
      Challenge.EvmProof.GasSteps (sizeState input 1322) (Bytecode.Main.trampolineState input 1196) :=
    if hs : input.size = 99 then
      ((sound check0PrefixPath rfl (run_check0_taken_prefix input hs) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check0_jump input) rfl rfl deployAddress_not_precompile)).trans
        (V1.gasSteps_fallback input (fun hz => hno.h1 ⟨hs, hz⟩))
    else
      (sound check0Path rfl (run_check0_skip input hsize hs) rfl rfl deployAddress_not_precompile).trans
        (rest1 input hsize hno)
  rest1 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hno : NoHit input) :
      Challenge.EvmProof.GasSteps (sizeState input 1330) (Bytecode.Main.trampolineState input 1196) :=
    if hs : input.size = 98 then
      (((sound check1PrefixPath rfl (run_check1_taken_prefix input hs) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check1_jump input) rfl rfl deployAddress_not_precompile)).trans
        (V2.gasSteps_fallback input (fun hz => hno.h2 ⟨hs, hz⟩))).trans
        (V3.gasSteps_fallback input (fun hz => hno.h3 ⟨hs, hz⟩))
    else
      (sound check1Path rfl (run_check1_skip input hsize hs) rfl rfl deployAddress_not_precompile).trans
        (rest2 input hsize hno)
  rest2 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hno : NoHit input) :
      Challenge.EvmProof.GasSteps (sizeState input 1338) (Bytecode.Main.trampolineState input 1196) :=
    if hs : input.size = 110 then
      ((sound check2PrefixPath rfl (run_check2_taken_prefix input hs) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check2_jump input) rfl rfl deployAddress_not_precompile)).trans
        (V4.gasSteps_fallback input (fun hz => hno.h4 ⟨hs, hz⟩))
    else
      (sound check2Path rfl (run_check2_skip input hsize hs) rfl rfl deployAddress_not_precompile).trans
        (rest3 input hsize hno)
  rest3 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hno : NoHit input) :
      Challenge.EvmProof.GasSteps (sizeState input 1346) (Bytecode.Main.trampolineState input 1196) :=
    if hs : input.size = 161 then
      ((sound check3PrefixPath rfl (run_check3_taken_prefix input hs) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check3_jump input) rfl rfl deployAddress_not_precompile)).trans
        (V5.gasSteps_fallback input (fun hz => hno.h5 ⟨hs, hz⟩))
    else
      (sound check3Path rfl (run_check3_skip input hsize hs) rfl rfl deployAddress_not_precompile).trans
        (rest4 input hsize hno)
  rest4 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hno : NoHit input) :
      Challenge.EvmProof.GasSteps (sizeState input 1354) (Bytecode.Main.trampolineState input 1196) :=
    if hs : input.size = 160 then
      ((sound check4PrefixPath rfl (run_check4_taken_prefix input hs) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check4_jump input) rfl rfl deployAddress_not_precompile)).trans
        (V6.gasSteps_fallback input (fun hz => hno.h6 ⟨hs, hz⟩))
    else
      (sound check4Path rfl (run_check4_skip input hsize hs) rfl rfl deployAddress_not_precompile).trans
        (rest5 input hsize hno)
  rest5 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hno : NoHit input) :
      Challenge.EvmProof.GasSteps (sizeState input 1362) (Bytecode.Main.trampolineState input 1196) :=
    if hs : input.size = 100 then
      ((sound check5PrefixPath rfl (run_check5_taken_prefix input hs) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check5_jump input) rfl rfl deployAddress_not_precompile)).trans
        (V7.gasSteps_fallback input (fun hz => hno.h7 ⟨hs, hz⟩))
    else
      (sound check5Path rfl (run_check5_skip input hsize hs) rfl rfl deployAddress_not_precompile).trans
        (rest6 input hsize hno)
  rest6 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hno : NoHit input) :
      Challenge.EvmProof.GasSteps (sizeState input 1370) (Bytecode.Main.trampolineState input 1196) :=
    if hs : input.size = 163 then
      ((sound check6PrefixPath rfl (run_check6_taken_prefix input hs) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check6_jump input) rfl rfl deployAddress_not_precompile)).trans
        (V8.gasSteps_fallback input (fun hz => hno.h8 ⟨hs, hz⟩))
    else
      (sound check6Path rfl (run_check6_skip input hsize hs) rfl rfl deployAddress_not_precompile).trans
        (rest7 input hsize hno)
  rest7 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hno : NoHit input) :
      Challenge.EvmProof.GasSteps (sizeState input 1378) (Bytecode.Main.trampolineState input 1196) :=
    if hs : input.size = 192 then
      (((sound check7PrefixPath rfl (run_check7_taken_prefix input hs) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check7_jump input) rfl rfl deployAddress_not_precompile)).trans
        (V9.gasSteps_fallback input (fun hz => hno.h9 ⟨hs, hz⟩))).trans
        (V10.gasSteps_fallback input (fun hz => hno.h10 ⟨hs, hz⟩))
    else
      (sound check7Path rfl (run_check7_skip input hsize hs) rfl rfl deployAddress_not_precompile).trans
        (rest8 input hsize hno)
  rest8 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hno : NoHit input) :
      Challenge.EvmProof.GasSteps (sizeState input 1386) (Bytecode.Main.trampolineState input 1196) :=
    if hs : input.size = 353 then
      ((sound check8PrefixPath rfl (run_check8_taken_prefix input hs) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check8_jump input) rfl rfl deployAddress_not_precompile)).trans
        (V11.gasSteps_fallback input (fun hz => hno.h11 ⟨hs, hz⟩))
    else
      (sound check8Path rfl (run_check8_skip input hsize hs) rfl rfl deployAddress_not_precompile).trans
        (rest9 input hsize hno)
  rest9 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hno : NoHit input) :
      Challenge.EvmProof.GasSteps (sizeState input 1395) (Bytecode.Main.trampolineState input 1196) :=
    if hs : input.size = 611 then
      ((sound check9PrefixPath rfl (run_check9_taken_prefix input hs) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_check9_jump input) rfl rfl deployAddress_not_precompile)).trans
        (V12.gasSteps_fallback input (fun hz => hno.h12 ⟨hs, hz⟩))
    else
      (sound check9Path rfl (run_check9_skip input hsize hs) rfl rfl deployAddress_not_precompile).trans
        ((sound exitPrefixPath rfl (run_exit_prefix input) rfl rfl deployAddress_not_precompile).trans
        (soundOne rfl (run_exit_jump input) rfl rfl deployAddress_not_precompile))

end Challenge.Modexp.Submission.Proofs.Memo.Main
