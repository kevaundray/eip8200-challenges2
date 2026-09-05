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

theorem run_selector_12 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 12) (selectorEntry s KnownInputData.targetInput 12) =
      some (bodyEntry s KnownInputData.targetInput 12) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6732 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3283 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath12,
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

theorem run_body_12 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 12) (bodyEntry s KnownInputData.targetInput 12) =
      some (resultState s KnownInputData.targetInput 12) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath12, KnownInputPaths.opAt, KnownInputPaths.pushAt,
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

theorem run_selector_13 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 13) (selectorEntry s KnownInputData.targetInput 13) =
      some (bodyEntry s KnownInputData.targetInput 13) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6775 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3301 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath13,
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

theorem run_body_13 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 13) (bodyEntry s KnownInputData.targetInput 13) =
      some (resultState s KnownInputData.targetInput 13) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath13, KnownInputPaths.opAt, KnownInputPaths.pushAt,
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

theorem run_selector_14 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 14) (selectorEntry s KnownInputData.targetInput 14) =
      some (bodyEntry s KnownInputData.targetInput 14) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6818 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3319 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath14,
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

theorem run_body_14 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 14) (bodyEntry s KnownInputData.targetInput 14) =
      some (resultState s KnownInputData.targetInput 14) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath14, KnownInputPaths.opAt, KnownInputPaths.pushAt,
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

theorem run_selector_15 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 15) (selectorEntry s KnownInputData.targetInput 15) =
      some (bodyEntry s KnownInputData.targetInput 15) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6861 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3337 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath15,
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

theorem run_body_15 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 15) (bodyEntry s KnownInputData.targetInput 15) =
      some (resultState s KnownInputData.targetInput 15) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath15, KnownInputPaths.opAt, KnownInputPaths.pushAt,
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
