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

theorem run_selector_4 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 4) (selectorEntry s KnownInputData.targetInput 4) =
      some (bodyEntry s KnownInputData.targetInput 4) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6388 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3139 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath4,
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

theorem run_body_4 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 4) (bodyEntry s KnownInputData.targetInput 4) =
      some (resultState s KnownInputData.targetInput 4) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath4, KnownInputPaths.opAt, KnownInputPaths.pushAt,
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

theorem run_selector_5 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 5) (selectorEntry s KnownInputData.targetInput 5) =
      some (bodyEntry s KnownInputData.targetInput 5) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6431 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3157 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath5,
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

theorem run_body_5 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 5) (bodyEntry s KnownInputData.targetInput 5) =
      some (resultState s KnownInputData.targetInput 5) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath5, KnownInputPaths.opAt, KnownInputPaths.pushAt,
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

theorem run_selector_6 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 6) (selectorEntry s KnownInputData.targetInput 6) =
      some (bodyEntry s KnownInputData.targetInput 6) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6474 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3175 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath6,
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

theorem run_body_6 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 6) (bodyEntry s KnownInputData.targetInput 6) =
      some (resultState s KnownInputData.targetInput 6) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath6, KnownInputPaths.opAt, KnownInputPaths.pushAt,
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

theorem run_selector_7 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 7) (selectorEntry s KnownInputData.targetInput 7) =
      some (bodyEntry s KnownInputData.targetInput 7) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6517 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3193 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath7,
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

theorem run_body_7 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 7) (bodyEntry s KnownInputData.targetInput 7) =
      some (resultState s KnownInputData.targetInput 7) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath7, KnownInputPaths.opAt, KnownInputPaths.pushAt,
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
