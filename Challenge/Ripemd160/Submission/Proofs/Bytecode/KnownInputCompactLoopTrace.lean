import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactGuardTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactLoopTrace

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputState KnownInputCompactPaths KnownInputCompactState

private abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

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
  have hlt : 32 * n + 64 < 992 := by omega
  have hnextMod :
      (32 * n + 64) %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        32 * n + 64 := by
    apply Nat.mod_eq_of_lt
    simpa using hnext
  have hcond0 :
      (UInt256.lt (UInt256.ofNat (32 * n + 64))
        (UInt256.ofNat 992)).toNat ≠ 0 := by
    unfold UInt256.lt
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hnext,
      Nat.mod_eq_of_lt (by norm_num : 992 < 2 ^ 256), if_pos hlt]
    decide
  have hmod' :
      (32 * n + 32) %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        32 * n + 32 := by
    apply Nat.mod_eq_of_lt
    simpa using hstart
  have hnaddr : 32 * (n + 1) = 32 * n + 32 := by omega
  have hxor : UInt256.xor (referenceWord input)
      (MachineState.readWord input (32 * n + 32)) =
      UInt256.xor (MachineState.readWord input (32 * n + 32))
        (referenceWord input) := BooleanSelect.xor_comm _ _
  have hxor' : UInt256.xor (MachineState.readWord input 0)
      (MachineState.readWord input (32 * n + 32)) =
      UInt256.xor (MachineState.readWord input (32 * n + 32))
        (MachineState.readWord input 0) := by
    simpa [referenceWord] using hxor
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
    hstart, hnext, hmod, hmod', hsum, hlt, hnextMod, hcond0, hacc, hxor, hxor', hnaddr,
    Word.lor_comm,
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
  have hzero :
      (UInt256.lt (UInt256.ofNat 992) (UInt256.ofNat 992)).toNat = 0 := by decide
  have hmod :
      960 %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        960 := by norm_num
  have hxor : UInt256.xor (referenceWord input)
      (MachineState.readWord input 960) =
      UInt256.xor (MachineState.readWord input 960)
        (referenceWord input) := BooleanSelect.xor_comm _ _
  have hxor' : UInt256.xor (MachineState.readWord input 0)
      (MachineState.readWord input 960) =
      UInt256.xor (MachineState.readWord input 960)
        (MachineState.readWord input 0) := by
    simpa [referenceWord] using hxor
  simp (config := { maxSteps := 1000000 })
    [loopPath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
    KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopState, loopExitState, referenceWord, hcalldata, hrun, hacc, hfalse, hzero, hmod,
    hxor, hxor', Word.lor_comm, List.exchange, UInt256.isTrue,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactLoopTrace
