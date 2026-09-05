import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputState

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputBodyTrace

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputPaths KnownInputState

private abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

theorem run_selector_0 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 0) (selectorEntry s KnownInputData.targetInput 0) =
      some (bodyEntry s KnownInputData.targetInput 0) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6216 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3067 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath0,
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
      Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.eq, UInt256.isTrue]

theorem run_body_0 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 0) (bodyEntry s KnownInputData.targetInput 0) =
      some (resultState s KnownInputData.targetInput 0) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath0, KnownInputPaths.opAt, KnownInputPaths.pushAt,
      KnownInputPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bodyEntry, resultState, resultMemory, resultActiveWords, knownAfter,
      KnownInputDigest.H1, KnownInputDigest.H2, KnownInputDigest.H3,
      KnownInputDigest.H4, KnownInputDigest.H5, KnownInputDigest.H6,
      KnownInputDigest.H7, KnownInputDigest.H8, KnownInputDigest.H9,
      KnownInputDigest.H10, KnownInputDigest.H11, KnownInputDigest.H12,
      KnownInputDigest.H13, KnownInputDigest.H14, KnownInputDigest.H15,
      KnownInputDigest.H16, KnownInputState.writeWord, hcode, hrun, hdest,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofUInt32]

theorem run_selector_1 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 1) (selectorEntry s KnownInputData.targetInput 1) =
      some (bodyEntry s KnownInputData.targetInput 1) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6259 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3085 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath1,
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
      Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.eq, UInt256.isTrue]

theorem run_body_1 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 1) (bodyEntry s KnownInputData.targetInput 1) =
      some (resultState s KnownInputData.targetInput 1) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath1, KnownInputPaths.opAt, KnownInputPaths.pushAt,
      KnownInputPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bodyEntry, resultState, resultMemory, resultActiveWords, knownAfter,
      KnownInputDigest.H1, KnownInputDigest.H2, KnownInputDigest.H3,
      KnownInputDigest.H4, KnownInputDigest.H5, KnownInputDigest.H6,
      KnownInputDigest.H7, KnownInputDigest.H8, KnownInputDigest.H9,
      KnownInputDigest.H10, KnownInputDigest.H11, KnownInputDigest.H12,
      KnownInputDigest.H13, KnownInputDigest.H14, KnownInputDigest.H15,
      KnownInputDigest.H16, KnownInputState.writeWord, hcode, hrun, hdest,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofUInt32]

theorem run_selector_2 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 2) (selectorEntry s KnownInputData.targetInput 2) =
      some (bodyEntry s KnownInputData.targetInput 2) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6302 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3103 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath2,
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
      Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.eq, UInt256.isTrue]

theorem run_body_2 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 2) (bodyEntry s KnownInputData.targetInput 2) =
      some (resultState s KnownInputData.targetInput 2) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath2, KnownInputPaths.opAt, KnownInputPaths.pushAt,
      KnownInputPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bodyEntry, resultState, resultMemory, resultActiveWords, knownAfter,
      KnownInputDigest.H1, KnownInputDigest.H2, KnownInputDigest.H3,
      KnownInputDigest.H4, KnownInputDigest.H5, KnownInputDigest.H6,
      KnownInputDigest.H7, KnownInputDigest.H8, KnownInputDigest.H9,
      KnownInputDigest.H10, KnownInputDigest.H11, KnownInputDigest.H12,
      KnownInputDigest.H13, KnownInputDigest.H14, KnownInputDigest.H15,
      KnownInputDigest.H16, KnownInputState.writeWord, hcode, hrun, hdest,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofUInt32]

theorem run_selector_3 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 3) (selectorEntry s KnownInputData.targetInput 3) =
      some (bodyEntry s KnownInputData.targetInput 3) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6345 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3121 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath3,
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
      Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.eq, UInt256.isTrue]

theorem run_body_3 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 3) (bodyEntry s KnownInputData.targetInput 3) =
      some (resultState s KnownInputData.targetInput 3) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath3, KnownInputPaths.opAt, KnownInputPaths.pushAt,
      KnownInputPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bodyEntry, resultState, resultMemory, resultActiveWords, knownAfter,
      KnownInputDigest.H1, KnownInputDigest.H2, KnownInputDigest.H3,
      KnownInputDigest.H4, KnownInputDigest.H5, KnownInputDigest.H6,
      KnownInputDigest.H7, KnownInputDigest.H8, KnownInputDigest.H9,
      KnownInputDigest.H10, KnownInputDigest.H11, KnownInputDigest.H12,
      KnownInputDigest.H13, KnownInputDigest.H14, KnownInputDigest.H15,
      KnownInputDigest.H16, KnownInputState.writeWord, hcode, hrun, hdest,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofUInt32]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputBodyTrace
