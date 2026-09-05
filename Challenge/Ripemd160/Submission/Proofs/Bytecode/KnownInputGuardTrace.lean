import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputState

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputGuardTrace

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open KnownInputPaths KnownInputState

private abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

private theorem chunk0_value : chunk0 =
    [(0, KnownInputData.fullWord), (32, KnownInputData.fullWord),
      (64, KnownInputData.fullWord), (96, KnownInputData.fullWord),
      (128, KnownInputData.fullWord), (160, KnownInputData.fullWord),
      (192, KnownInputData.fullWord), (224, KnownInputData.fullWord)] := by rfl

private theorem chunk1_value : chunk1 =
    [(256, KnownInputData.fullWord), (288, KnownInputData.fullWord),
      (320, KnownInputData.fullWord), (352, KnownInputData.fullWord),
      (384, KnownInputData.fullWord), (416, KnownInputData.fullWord),
      (448, KnownInputData.fullWord), (480, KnownInputData.fullWord)] := by rfl

private theorem chunk2_value : chunk2 =
    [(512, KnownInputData.fullWord), (544, KnownInputData.fullWord),
      (576, KnownInputData.fullWord), (608, KnownInputData.fullWord),
      (640, KnownInputData.fullWord), (672, KnownInputData.fullWord),
      (704, KnownInputData.fullWord), (736, KnownInputData.fullWord)] := by rfl

private theorem chunk3_value : chunk3 =
    [(768, KnownInputData.fullWord), (800, KnownInputData.fullWord),
      (832, KnownInputData.fullWord), (864, KnownInputData.fullWord),
      (896, KnownInputData.fullWord), (928, KnownInputData.fullWord),
      (960, KnownInputData.fullWord), (992, KnownInputData.finalWord)] := by rfl

private theorem size1000True :
    UInt256.isTrue (UInt256.eq (UInt256.ofNat 1000)
      (UInt256.ofNat 1000)) := by decide

theorem run_size_target (s : State) (i : Nat)
    (hcalldata : s.executionEnv.calldata = KnownInputData.targetInput)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run sizePath (DriverTrace.dispatchEntry s KnownInputData.targetInput i) =
      some (sizeMatched s KnownInputData.targetInput i) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x12dc = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2821 (by rfl)
  simp [sizePath, KnownInputPaths.opAt, KnownInputPaths.pushAt,
    KnownInputPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    DriverTrace.dispatchEntry, sizeMatched, hcalldata, hcode, hrun, hdest,
    size1000True, KnownInputData.targetInput_size,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_size_match (s : State) (input : ByteArray) (i : Nat)
    (hsize : input.size = 1000)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run sizePath (DriverTrace.dispatchEntry s input i) =
      some (sizeMatched s input i) := by
  have heqTrue : UInt256.isTrue
      (UInt256.eq (UInt256.ofNat 1000) (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  have hdest : Decode.isValidJumpDest submissionBytecode 0x12dc = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2821 (by rfl)
  simp [sizePath, KnownInputPaths.opAt, KnownInputPaths.pushAt,
    KnownInputPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    DriverTrace.dispatchEntry, sizeMatched, hcalldata, hcode, hrun, hdest,
    hsize, heqTrue, size1000True, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_size_fail (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hsize : input.size ≠ 1000)
    (hcalldata : s.executionEnv.calldata = input)
    (hrun : s.halt = .Running) :
    run sizePath (DriverTrace.dispatchEntry s input i) =
      some (sizeFailed s input i) := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hsize' : 1000 ≠ input.size := Ne.symm hsize
  have heq : UInt256.eq (UInt256.ofNat 1000) (UInt256.ofNat input.size) =
      UInt256.ofNat 0 := by
    unfold UInt256.eq
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num), Nat.mod_eq_of_lt hlt]
    simp [hsize']
  have hfalse : ¬ UInt256.isTrue
      (UInt256.eq (UInt256.ofNat 1000) (UInt256.ofNat input.size)) := by
    rw [heq]
    decide
  simp [sizePath, KnownInputPaths.opAt, KnownInputPaths.pushAt,
    KnownInputPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    DriverTrace.dispatchEntry, sizeFailed, hcalldata, hrun, heq, hfalse,
    UInt256.isTrue,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_size_fallback (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run sizeFallbackPath (sizeFailed s input i) = some (legacyEntry s input i) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x129e = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2792 (by rfl)
  simp [sizeFallbackPath, KnownInputPaths.opAt, KnownInputPaths.pushAt,
    KnownInputPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    sizeFailed, legacyEntry, hcode, hrun, hdest,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_checkEntry (s : State) (input : ByteArray) (i : Nat)
    (hrun : s.halt = .Running) :
    run checkEntryPath (sizeMatched s input i) =
      some (accState s input i 0x12de 0) := by
  simp [checkEntryPath, KnownInputPaths.opAt, KnownInputPaths.pushAt,
    KnownInputPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    sizeMatched, accState, accAfter, acc0, hrun,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_check0 (s : State) (input : ByteArray) (i : Nat)
    (hcalldata : s.executionEnv.calldata = input) (hrun : s.halt = .Running) :
    run checkPath0 (accState s input i 0x12de 0) =
      some (accState s input i 0x140d 1) := by
  simp [checkPath0, KnownInputPaths.opAt, KnownInputPaths.pushAt,
    KnownInputPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    accState, accAfter, acc0, acc1, chunk0_value, KnownInputLogic.scanDiff,
    KnownInputData.checks, KnownInputData.expectedWord, KnownInputData.fullWord,
    hcalldata, hrun, Challenge.EvmProof.Word.literal_eq_ofNat,
    BooleanSelect.xor_comm,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_check1 (s : State) (input : ByteArray) (i : Nat)
    (hcalldata : s.executionEnv.calldata = input) (hrun : s.halt = .Running) :
    run checkPath1 (accState s input i 0x140d 1) =
      some (accState s input i 0x1545 2) := by
  simp [checkPath1, KnownInputPaths.opAt, KnownInputPaths.pushAt,
    KnownInputPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    accState, accAfter, acc1, acc2, chunk1_value, KnownInputLogic.scanDiff,
    KnownInputData.checks, KnownInputData.expectedWord, KnownInputData.fullWord,
    hcalldata, hrun, Challenge.EvmProof.Word.literal_eq_ofNat,
    BooleanSelect.xor_comm,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_check2 (s : State) (input : ByteArray) (i : Nat)
    (hcalldata : s.executionEnv.calldata = input) (hrun : s.halt = .Running) :
    run checkPath2 (accState s input i 0x1545 2) =
      some (accState s input i 0x167d 3) := by
  simp [checkPath2, KnownInputPaths.opAt, KnownInputPaths.pushAt,
    KnownInputPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    accState, accAfter, acc2, acc3, chunk2_value, KnownInputLogic.scanDiff,
    KnownInputData.checks, KnownInputData.expectedWord, KnownInputData.fullWord,
    hcalldata, hrun, Challenge.EvmProof.Word.literal_eq_ofNat,
    BooleanSelect.xor_comm,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_check3 (s : State) (input : ByteArray) (i : Nat)
    (hcalldata : s.executionEnv.calldata = input) (hrun : s.halt = .Running) :
    run checkPath3 (accState s input i 0x167d 3) =
      some (accState s input i 0x17b5 4) := by
  simp [checkPath3, KnownInputPaths.opAt, KnownInputPaths.pushAt,
    KnownInputPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    accState, accAfter, acc3, acc4, chunk3_value, KnownInputLogic.scanDiff,
    KnownInputData.checks, KnownInputData.expectedWord, KnownInputData.fullWord,
    KnownInputData.finalWord, hcalldata, hrun,
    BooleanSelect.xor_comm,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem target_acc4_zero : acc4 KnownInputData.targetInput = 0 := by
  rw [acc4_eq_scanDiff, KnownInputLogic.scanChecks_eq_zero_iff]
  intro i hi
  exact KnownInputData.targetInput_readWord i hi

theorem run_match_target (s : State) (i : Nat)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run matchBranchPath
      (accState s KnownInputData.targetInput i 0x17b5 4) =
      some (selectorEntry s KnownInputData.targetInput i) := by
  simp [matchBranchPath, KnownInputPaths.opAt, KnownInputPaths.pushAt,
    KnownInputPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    accState, accAfter, selectorEntry, target_acc4_zero, hrun,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem nonTarget_acc4_ne (input : ByteArray) (hsize : input.size = 1000)
    (hne : input ≠ KnownInputData.targetInput) : acc4 input ≠ 0 := by
  intro hzero
  apply hne
  apply KnownInputLogic.matches_eq_targetInput input
  refine ⟨hsize, ?_⟩
  rw [← KnownInputLogic.scanChecks_eq_zero_iff]
  rw [← acc4_eq_scanDiff]
  exact hzero

theorem run_match_fallback (s : State) (input : ByteArray) (i : Nat)
    (hsize : input.size = 1000) (hne : input ≠ KnownInputData.targetInput)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run matchBranchPath (accState s input i 0x17b5 4) =
      some (legacyEntry s input i) := by
  have hneAcc := nonTarget_acc4_ne input hsize hne
  have hneNat : (acc4 input).toNat ≠ 0 := by
    intro hzero
    apply hneAcc
    apply Challenge.EvmProof.Word.word_ext
    rw [show (0 : UInt256).toNat = 0 by decide]
    exact hzero
  have htrue : UInt256.isTrue (acc4 input) := hneNat
  have hdest : Decode.isValidJumpDest submissionBytecode 0x129e = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2792 (by rfl)
  simp [matchBranchPath, KnownInputPaths.opAt, KnownInputPaths.pushAt,
    KnownInputPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    accState, accAfter, legacyEntry, hcode, hrun, hdest, htrue,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputGuardTrace
