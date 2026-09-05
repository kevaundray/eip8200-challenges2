import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputBodyTrace0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputBodyTrace1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputBodyTrace2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputBodyTrace3

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/- The concrete cases are split across four imported modules. -/
/-
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputBodyTrace

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open KnownInputPaths KnownInputState

private abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

private theorem bodyValid (i : Nat) (hi : i < 16) :
    Decode.isValidJumpDest submissionBytecode
      ([0x1848, 0x1873, 0x189e, 0x18c9, 0x18f4, 0x191f, 0x194a,
        0x1975, 0x19a0, 0x19cb, 0x19f6, 0x1a21, 0x1a4c, 0x1a77,
        0x1aa2, 0x1acd][i]!) = true := by
  interval_cases i <;>
    first
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3067 (by rfl)
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3085 (by rfl)
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3103 (by rfl)
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3121 (by rfl)
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3139 (by rfl)
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3157 (by rfl)
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3175 (by rfl)
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3193 (by rfl)
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3211 (by rfl)
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3229 (by rfl)
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3247 (by rfl)
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3265 (by rfl)
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3283 (by rfl)
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3301 (by rfl)
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3319 (by rfl)
    | exact Artifact.submissionArtifact.isValidJumpDest_index 3337 (by rfl)

theorem run_selector (s : State) (i : Nat) (hi : i < 16)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath i) (selectorEntry s KnownInputData.targetInput i) =
      some (bodyEntry s KnownInputData.targetInput i) := by
  have hdest := bodyValid i hi
  interval_cases i <;>
    simp (config := { maxSteps := 1000000 })
      [selectorPath, selectorPath0, selectorPath1, selectorPath2, selectorPath3,
        selectorPath4, selectorPath5, selectorPath6, selectorPath7,
        selectorPath8, selectorPath9, selectorPath10, selectorPath11,
        selectorPath12, selectorPath13, selectorPath14, selectorPath15,
        selectorGroup0, selectorGroup1, selectorGroup2, selectorGroup3,
        selectorGroup4, selectorGroup5, selectorGroup6, selectorGroup7,
        selectorGroup8, selectorGroup9, selectorGroup10, selectorGroup11,
        selectorGroup12, selectorGroup13, selectorGroup14, selectorGroup15,
        KnownInputPaths.opAt, KnownInputPaths.pushAt, KnownInputPaths.wfOp,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
        selectorEntry, bodyEntry, DriverTrace.blockOffsetWord,
        DriverTrace.blockOffset, hcode, hrun, hdest,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod,
        Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.isTrue]

theorem run_body (s : State) (i : Nat) (hi : i < 16)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath i) (bodyEntry s KnownInputData.targetInput i) =
      some (resultState s KnownInputData.targetInput i) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  interval_cases i <;>
    simp (config := { maxSteps := 1000000 })
      [bodyPath, bodyPath0, bodyPath1, bodyPath2, bodyPath3, bodyPath4,
        bodyPath5, bodyPath6, bodyPath7, bodyPath8, bodyPath9, bodyPath10,
        bodyPath11, bodyPath12, bodyPath13, bodyPath14, bodyPath15,
        KnownInputPaths.opAt, KnownInputPaths.pushAt, KnownInputPaths.wfOp,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
        bodyEntry, resultState, resultMemory, resultActiveWords, knownAfter,
        KnownInputDigest.H1, KnownInputDigest.H2, KnownInputDigest.H3,
        KnownInputDigest.H4, KnownInputDigest.H5, KnownInputDigest.H6,
        KnownInputDigest.H7, KnownInputDigest.H8, KnownInputDigest.H9,
        KnownInputDigest.H10, KnownInputDigest.H11, KnownInputDigest.H12,
        KnownInputDigest.H13, KnownInputDigest.H14, KnownInputDigest.H15,
        KnownInputDigest.H16, KnownInputState.writeWord,
        hcode, hrun, hdest, State.activeWordsAfterUInt256,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod,
        Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofUInt32]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputBodyTrace
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputBodyTrace

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputPaths KnownInputState

private abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

theorem run_selector (s : State) (i : Nat) (hi : i < 16)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath i) (selectorEntry s KnownInputData.targetInput i) =
      some (bodyEntry s KnownInputData.targetInput i) := by
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
      i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hi' with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst i; exact run_selector_0 s hcode hrun
  · subst i; exact run_selector_1 s hcode hrun
  · subst i; exact run_selector_2 s hcode hrun
  · subst i; exact run_selector_3 s hcode hrun
  · subst i; exact run_selector_4 s hcode hrun
  · subst i; exact run_selector_5 s hcode hrun
  · subst i; exact run_selector_6 s hcode hrun
  · subst i; exact run_selector_7 s hcode hrun
  · subst i; exact run_selector_8 s hcode hrun
  · subst i; exact run_selector_9 s hcode hrun
  · subst i; exact run_selector_10 s hcode hrun
  · subst i; exact run_selector_11 s hcode hrun
  · subst i; exact run_selector_12 s hcode hrun
  · subst i; exact run_selector_13 s hcode hrun
  · subst i; exact run_selector_14 s hcode hrun
  · subst i; exact run_selector_15 s hcode hrun

theorem run_body (s : State) (i : Nat) (hi : i < 16)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath i) (bodyEntry s KnownInputData.targetInput i) =
      some (resultState s KnownInputData.targetInput i) := by
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
      i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hi' with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst i; exact run_body_0 s hcode hrun
  · subst i; exact run_body_1 s hcode hrun
  · subst i; exact run_body_2 s hcode hrun
  · subst i; exact run_body_3 s hcode hrun
  · subst i; exact run_body_4 s hcode hrun
  · subst i; exact run_body_5 s hcode hrun
  · subst i; exact run_body_6 s hcode hrun
  · subst i; exact run_body_7 s hcode hrun
  · subst i; exact run_body_8 s hcode hrun
  · subst i; exact run_body_9 s hcode hrun
  · subst i; exact run_body_10 s hcode hrun
  · subst i; exact run_body_11 s hcode hrun
  · subst i; exact run_body_12 s hcode hrun
  · subst i; exact run_body_13 s hcode hrun
  · subst i; exact run_body_14 s hcode hrun
  · subst i; exact run_body_15 s hcode hrun

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputBodyTrace
