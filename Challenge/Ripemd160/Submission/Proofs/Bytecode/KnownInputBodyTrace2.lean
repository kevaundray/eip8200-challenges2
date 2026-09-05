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

theorem run_selector_8 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 8) (selectorEntry s KnownInputData.targetInput 8) =
      some (bodyEntry s KnownInputData.targetInput 8) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6560 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3211 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath8,
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

theorem run_body_8 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 8) (bodyEntry s KnownInputData.targetInput 8) =
      some (resultState s KnownInputData.targetInput 8) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath8, KnownInputPaths.opAt, KnownInputPaths.pushAt,
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

theorem run_selector_9 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 9) (selectorEntry s KnownInputData.targetInput 9) =
      some (bodyEntry s KnownInputData.targetInput 9) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6603 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3229 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath9,
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

theorem run_body_9 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 9) (bodyEntry s KnownInputData.targetInput 9) =
      some (resultState s KnownInputData.targetInput 9) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath9, KnownInputPaths.opAt, KnownInputPaths.pushAt,
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

theorem run_selector_10 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 10) (selectorEntry s KnownInputData.targetInput 10) =
      some (bodyEntry s KnownInputData.targetInput 10) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6646 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3247 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath10,
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

theorem run_body_10 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 10) (bodyEntry s KnownInputData.targetInput 10) =
      some (resultState s KnownInputData.targetInput 10) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath10, KnownInputPaths.opAt, KnownInputPaths.pushAt,
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

theorem run_selector_11 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (selectorPath 11) (selectorEntry s KnownInputData.targetInput 11) =
      some (bodyEntry s KnownInputData.targetInput 11) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 6689 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3265 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [selectorPath, selectorPath11,
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

theorem run_body_11 (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run (bodyPath 11) (bodyEntry s KnownInputData.targetInput 11) =
      some (resultState s KnownInputData.targetInput 11) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [bodyPath, bodyPath11, KnownInputPaths.opAt, KnownInputPaths.pushAt,
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
