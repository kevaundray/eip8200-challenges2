import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactPaths

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactGuardTrace

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputState KnownInputCompactPaths
open KnownInputCompactState

private abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

private theorem size1000True :
    UInt256.isTrue (UInt256.eq (UInt256.ofNat 1000)
      (UInt256.ofNat 1000)) := by decide

private theorem size1000Nonzero :
    (UInt256.eq (UInt256.ofNat 1000) (UInt256.ofNat 1000)).toNat ≠ 0 :=
  size1000True

private theorem expandedFullWord :
    UInt256.lor
      (UInt256.shiftLeft
        (UInt256.lor
          (UInt256.shiftLeft (UInt256.ofNat 7016996765293437281)
            (UInt256.ofNat 64))
          (UInt256.ofNat 7016996765293437281))
        (UInt256.ofNat 128))
      (UInt256.lor
        (UInt256.shiftLeft (UInt256.ofNat 7016996765293437281)
          (UInt256.ofNat 64))
        (UInt256.ofNat 7016996765293437281)) = KnownInputData.fullWord := by
  decide

theorem run_size_target (s : State) (i : Nat)
    (hcalldata : s.executionEnv.calldata = KnownInputData.targetInput)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run sizePath (DriverTrace.dispatchEntry s KnownInputData.targetInput i) =
      some (sizeMatched s KnownInputData.targetInput i) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x12dc = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2821 (by rfl)
  simp [sizePath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
    KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    DriverTrace.dispatchEntry, sizeMatched, hcalldata, hcode, hrun, hdest,
    KnownInputData.targetInput_size, size1000True, size1000Nonzero,
    UInt256.isTrue,
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
  simp [sizePath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
    KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    DriverTrace.dispatchEntry, sizeMatched, hcalldata, hcode, hrun, hdest,
    hsize, heqTrue, size1000True, size1000Nonzero, UInt256.isTrue,
    Challenge.EvmProof.Word.literal_eq_ofNat,
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
  simp [sizePath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
    KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    DriverTrace.dispatchEntry, sizeFailed, hcalldata, hrun, heq, hfalse,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_size_fallback (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run sizeFallbackPath (sizeFailed s input i) = some (legacyEntry s input i) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x129e = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2792 (by rfl)
  simp [sizeFallbackPath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
    KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    sizeFailed, legacyEntry, hcode, hrun, hdest,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_checkEntry (s : State) (input : ByteArray) (i : Nat)
    (hcalldata : s.executionEnv.calldata = input)
    (hrun : s.halt = .Running) :
    run checkEntryPath (sizeMatched s input i) = some (loopState s input i 0) := by
  have hxor : UInt256.xor
      (UInt256.ofNat
        44046402572626160612103472728795008085361523578694645928734845681441465000289)
      (MachineState.readWord input 0) =
      UInt256.xor (MachineState.readWord input 0)
        (UInt256.ofNat
          44046402572626160612103472728795008085361523578694645928734845681441465000289) :=
    BooleanSelect.xor_comm _ _
  simp (config := { maxSteps := 1000000 })
    [checkEntryPath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
    KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    sizeMatched, loopState, loopAcc, referenceWord, KnownInputData.fullWord,
    hcalldata, hrun, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    hxor, expandedFullWord, KnownInputData.fullWord]

/- TEMP diagnostic split: loop and tail compile in their own module. -/
/-
theorem run_loop_more (s : State) (input : ByteArray) (i n : Nat)
    (hn : n < 29) (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run loopPath (loopState s input i n) = some (loopState s input i (n + 1)) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x12f6 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2836 (by rfl)
  have hptr : 32 * (n + 2) < 992 := by omega
  have hstart : 32 * n + 32 < 2 ^ 256 := by omega
  have hnext : 32 * n + 64 < 2 ^ 256 := by omega
  have hmod : (32 * n + 32) % 2 ^ 256 = 32 * n + 32 :=
    Nat.mod_eq_of_lt hstart
  have hsum : 32 + (32 * n + 32) = 32 * n + 64 := by omega
  have hcond : UInt256.isTrue
      (UInt256.lt (UInt256.ofNat (32 + (32 * n + 32)))
        (UInt256.ofNat 992)) := by
    unfold UInt256.isTrue UInt256.lt
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hnext,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num : 992 < 2 ^ 256)]
    simpa [hsum] using hptr
  have hxor : UInt256.xor (referenceWord input)
      (MachineState.readWord input (32 * n + 32)) =
      UInt256.xor (MachineState.readWord input (32 * n + 32))
        (referenceWord input) := BooleanSelect.xor_comm _ _
  have hacc : loopAcc input (n + 1) =
      UInt256.lor
        (UInt256.xor (MachineState.readWord input (32 * (n + 1)))
          (referenceWord input)) (loopAcc input n) := by
    rw [loopAcc]
  simp (config := { maxSteps := 1000000 })
    [loopPath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
    KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopState, referenceWord, hcalldata, hcode, hrun, hdest, hptr,
    hstart, hnext, hmod, hsum, hcond, hacc, hxor, Word.lor_comm,
    List.exchange, Nat.add_assoc, Nat.mul_add,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_loop_last (s : State) (input : ByteArray) (i : Nat)
    (hcalldata : s.executionEnv.calldata = input)
    (hrun : s.halt = .Running) :
    run loopPath (loopState s input i 29) = some (loopExitState s input i) := by
  have hacc : loopAcc input 30 =
      UInt256.lor
        (UInt256.xor (MachineState.readWord input 960) (referenceWord input))
        (loopAcc input 29) := by
    rw [show 30 = 29 + 1 by omega, loopAcc]
  have hfalse : ¬ UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 992) (UInt256.ofNat 992)) := by decide
  have hxor : UInt256.xor (referenceWord input)
      (MachineState.readWord input 960) =
      UInt256.xor (MachineState.readWord input 960)
        (referenceWord input) := BooleanSelect.xor_comm _ _
  simp (config := { maxSteps := 1000000 })
    [loopPath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
    KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopState, loopExitState, referenceWord, hcalldata, hrun, hacc, hfalse,
    hxor, Word.lor_comm, List.exchange, UInt256.isTrue,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tail_target (s : State) (i : Nat)
    (hcalldata : s.executionEnv.calldata = KnownInputData.targetInput)
    (hrun : s.halt = .Running) :
    run tailPath (loopExitState s KnownInputData.targetInput i) =
      some (KnownInputCompactState.bodyEntry s KnownInputData.targetInput i) := by
  have hzero : finalAcc KnownInputData.targetInput = 0 :=
    (KnownInputCompactLogic.finalAcc_zero_iff_target _
      KnownInputData.targetInput_size).2 rfl
  have hzero' : UInt256.lor
      (UInt256.xor
        (UInt256.shiftRight (referenceWord KnownInputData.targetInput)
          (UInt256.ofNat 192))
        (UInt256.shiftRight
          (MachineState.readWord KnownInputData.targetInput 992)
          (UInt256.ofNat 192)))
      (loopAcc KnownInputData.targetInput 30) = 0 := by
    simpa only [finalAcc, BooleanSelect.xor_comm] using hzero
  simp (config := { maxSteps := 1000000 })
    [tailPath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
    KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopExitState, KnownInputCompactState.bodyEntry, finalAcc, hcalldata, hrun,
    hzero', List.exchange,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tail_fallback (s : State) (input : ByteArray) (i : Nat)
    (hsize : input.size = 1000) (hne : input ≠ KnownInputData.targetInput)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run tailPath (loopExitState s input i) = some (legacyEntry s input i) := by
  have hneAcc : finalAcc input ≠ 0 := by
    intro hz
    exact hne ((KnownInputCompactLogic.finalAcc_zero_iff_target input hsize).1 hz)
  have htrue : UInt256.isTrue (finalAcc input) := by
    intro hnat
    apply hneAcc
    apply Challenge.EvmProof.Word.word_ext
    simpa using hnat
  have htrue' : UInt256.isTrue
      (UInt256.lor
        (UInt256.xor
          (UInt256.shiftRight (referenceWord input) (UInt256.ofNat 192))
          (UInt256.shiftRight (MachineState.readWord input 992)
            (UInt256.ofNat 192)))
        (loopAcc input 30)) := by
    simpa only [finalAcc, BooleanSelect.xor_comm] using htrue
  have hdest : Decode.isValidJumpDest submissionBytecode 0x129e = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2792 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [tailPath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
    KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopExitState, legacyEntry, finalAcc, hcalldata, hcode, hrun, htrue', hdest,
    List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

-/
end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactGuardTrace
