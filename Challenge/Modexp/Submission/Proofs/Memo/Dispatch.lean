import Challenge.Modexp.Submission.Proofs.Memo.PCs
import Challenge.Modexp.Submission.Proofs.Memo.Logic
import Challenge.Modexp.Submission.Proofs.Memo.Step

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.Dispatch

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo

def sizeState (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat pc
      stack := [UInt256.ofNat input.size] }

def entryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 977 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.opAt 978 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATASIZE)),
   Main.opAt 979 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.opAt 980 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO)),
   Main.pushAt 981 2 1409,
   Main.opAt 982 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def entryPrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 977 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.opAt 978 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATASIZE)),
   Main.opAt 979 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.opAt 980 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO)),
   Main.pushAt 981 2 1409
  ]

def check0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 983 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 984 1 99,
   Main.opAt 985 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 986 2 1413,
   Main.opAt 987 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def check0PrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 983 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 984 1 99,
   Main.opAt 985 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 986 2 1413
  ]

def check1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 988 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 989 1 98,
   Main.opAt 990 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 991 2 1491,
   Main.opAt 992 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def check1PrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 988 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 989 1 98,
   Main.opAt 990 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 991 2 1491
  ]

def check2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 993 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 994 1 110,
   Main.opAt 995 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 996 2 1638,
   Main.opAt 997 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def check2PrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 993 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 994 1 110,
   Main.opAt 995 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 996 2 1638
  ]

def check3Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 998 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 999 1 161,
   Main.opAt 1000 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1001 2 1712,
   Main.opAt 1002 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def check3PrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 998 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 999 1 161,
   Main.opAt 1000 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1001 2 1712
  ]

def check4Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1003 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 1004 1 160,
   Main.opAt 1005 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1006 2 1865,
   Main.opAt 1007 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def check4PrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1003 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 1004 1 160,
   Main.opAt 1005 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1006 2 1865
  ]

def check5Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1008 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 1009 1 100,
   Main.opAt 1010 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1011 2 1975,
   Main.opAt 1012 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def check5PrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1008 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 1009 1 100,
   Main.opAt 1010 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1011 2 1975
  ]

def check6Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1013 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 1014 1 163,
   Main.opAt 1015 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1016 2 2089,
   Main.opAt 1017 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def check6PrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1013 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 1014 1 163,
   Main.opAt 1015 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1016 2 2089
  ]

def check7Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1018 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 1019 1 192,
   Main.opAt 1020 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1021 2 2273,
   Main.opAt 1022 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def check7PrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1018 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 1019 1 192,
   Main.opAt 1020 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1021 2 2273
  ]

def check8Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1023 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 1024 2 353,
   Main.opAt 1025 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1026 2 2640,
   Main.opAt 1027 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def check8PrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1023 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 1024 2 353,
   Main.opAt 1025 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1026 2 2640
  ]

def check9Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1028 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 1029 2 611,
   Main.opAt 1030 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1031 2 3164,
   Main.opAt 1032 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def check9PrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1028 (EvmSemantics.Operation.Dup { idx := 0 }),
   Main.pushAt 1029 2 611,
   Main.opAt 1030 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1031 2 3164
  ]

def exitPrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1033 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   Main.pushAt 1034 2 1196
  ]

theorem run_entry_nonempty (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (h : input.size ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock entryPath (Main.trampolineState input 1314) =
      some (sizeState input 1322) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hz : UInt256.isZero (UInt256.ofNat input.size) = UInt256.ofNat 0 :=
    Logic.isZero_ofNat_of_ne hsize h
  simp [entryPath, sizeState, hz, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def entryJumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1321
      stack := [UInt256.ofNat 1409, UInt256.ofNat 1, UInt256.ofNat input.size] }

def entry_empty_jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 982 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

theorem run_entry_empty_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated entry_empty_jumpLocated (entryJumpState input) =
      some (sizeState input 1409) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1409 = true :=
    Artifact.isValidJumpDest_index 1036 (by rfl)
  have hpc : (entryJumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 982 := by
    simp [entryJumpState, initialState, PCs.pc0, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken entry_empty_jumpLocated rfl (entryJumpState input) 1409 (UInt256.ofNat 1) [UInt256.ofNat input.size] hpc rfl (by simp) Logic.isTrue_one rfl (by norm_num) hjump).trans rfl


theorem run_entry_empty_prefix (input : ByteArray) (h : input.size = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock entryPrefixPath (Main.trampolineState input 1314) =
      some (entryJumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hz : UInt256.isZero (UInt256.ofNat input.size) = UInt256.ofNat 1 :=
    Logic.isZero_ofNat_of_eq h
  simp [entryPrefixPath, entryJumpState, hz, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def check0JumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1329
      stack := [UInt256.ofNat 1413, UInt256.ofNat 1, UInt256.ofNat input.size] }

def check0_jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 987 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

theorem run_check0_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated check0_jumpLocated (check0JumpState input) =
      some (sizeState input 1413) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1413 = true :=
    Artifact.isValidJumpDest_index 1040 (by rfl)
  have hpc : (check0JumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 987 := by
    simp [check0JumpState, initialState, PCs.pc0, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken check0_jumpLocated rfl (check0JumpState input) 1413 (UInt256.ofNat 1) [UInt256.ofNat input.size] hpc rfl (by simp) Logic.isTrue_one rfl (by norm_num) hjump).trans rfl

theorem run_check0_taken_prefix (input : ByteArray) (h : input.size = 99) :
    Challenge.EvmProof.Stepper.runLocatedBlock check0PrefixPath (sizeState input 1322) =
      some (check0JumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 99) (UInt256.ofNat input.size) = UInt256.ofNat 1 :=
    Logic.eq_ofNat_of_eq h
  simp [check0PrefixPath, sizeState, check0JumpState, heq, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check0_skip (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (h : input.size ≠ 99) :
    Challenge.EvmProof.Stepper.runLocatedBlock check0Path (sizeState input 1322) =
      some (sizeState input 1330) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 99) (UInt256.ofNat input.size) = UInt256.ofNat 0 :=
    Logic.eq_ofNat_of_ne (by norm_num) hsize h
  simp [check0Path, sizeState, heq, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def check1JumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1337
      stack := [UInt256.ofNat 1491, UInt256.ofNat 1, UInt256.ofNat input.size] }

def check1_jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 992 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

theorem run_check1_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated check1_jumpLocated (check1JumpState input) =
      some (sizeState input 1491) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1491 = true :=
    Artifact.isValidJumpDest_index 1073 (by rfl)
  have hpc : (check1JumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 992 := by
    simp [check1JumpState, initialState, PCs.pc0, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken check1_jumpLocated rfl (check1JumpState input) 1491 (UInt256.ofNat 1) [UInt256.ofNat input.size] hpc rfl (by simp) Logic.isTrue_one rfl (by norm_num) hjump).trans rfl

theorem run_check1_taken_prefix (input : ByteArray) (h : input.size = 98) :
    Challenge.EvmProof.Stepper.runLocatedBlock check1PrefixPath (sizeState input 1330) =
      some (check1JumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 98) (UInt256.ofNat input.size) = UInt256.ofNat 1 :=
    Logic.eq_ofNat_of_eq h
  simp [check1PrefixPath, sizeState, check1JumpState, heq, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check1_skip (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (h : input.size ≠ 98) :
    Challenge.EvmProof.Stepper.runLocatedBlock check1Path (sizeState input 1330) =
      some (sizeState input 1338) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 98) (UInt256.ofNat input.size) = UInt256.ofNat 0 :=
    Logic.eq_ofNat_of_ne (by norm_num) hsize h
  simp [check1Path, sizeState, heq, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def check2JumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1345
      stack := [UInt256.ofNat 1638, UInt256.ofNat 1, UInt256.ofNat input.size] }

def check2_jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 997 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

theorem run_check2_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated check2_jumpLocated (check2JumpState input) =
      some (sizeState input 1638) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1638 = true :=
    Artifact.isValidJumpDest_index 1135 (by rfl)
  have hpc : (check2JumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 997 := by
    simp [check2JumpState, initialState, PCs.pc0, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken check2_jumpLocated rfl (check2JumpState input) 1638 (UInt256.ofNat 1) [UInt256.ofNat input.size] hpc rfl (by simp) Logic.isTrue_one rfl (by norm_num) hjump).trans rfl

theorem run_check2_taken_prefix (input : ByteArray) (h : input.size = 110) :
    Challenge.EvmProof.Stepper.runLocatedBlock check2PrefixPath (sizeState input 1338) =
      some (check2JumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 110) (UInt256.ofNat input.size) = UInt256.ofNat 1 :=
    Logic.eq_ofNat_of_eq h
  simp [check2PrefixPath, sizeState, check2JumpState, heq, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check2_skip (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (h : input.size ≠ 110) :
    Challenge.EvmProof.Stepper.runLocatedBlock check2Path (sizeState input 1338) =
      some (sizeState input 1346) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 110) (UInt256.ofNat input.size) = UInt256.ofNat 0 :=
    Logic.eq_ofNat_of_ne (by norm_num) hsize h
  simp [check2Path, sizeState, heq, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def check3JumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1353
      stack := [UInt256.ofNat 1712, UInt256.ofNat 1, UInt256.ofNat input.size] }

def check3_jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1002 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

theorem run_check3_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated check3_jumpLocated (check3JumpState input) =
      some (sizeState input 1712) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1712 = true :=
    Artifact.isValidJumpDest_index 1165 (by rfl)
  have hpc : (check3JumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1002 := by
    simp [check3JumpState, initialState, PCs.pc0, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken check3_jumpLocated rfl (check3JumpState input) 1712 (UInt256.ofNat 1) [UInt256.ofNat input.size] hpc rfl (by simp) Logic.isTrue_one rfl (by norm_num) hjump).trans rfl

theorem run_check3_taken_prefix (input : ByteArray) (h : input.size = 161) :
    Challenge.EvmProof.Stepper.runLocatedBlock check3PrefixPath (sizeState input 1346) =
      some (check3JumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 161) (UInt256.ofNat input.size) = UInt256.ofNat 1 :=
    Logic.eq_ofNat_of_eq h
  simp [check3PrefixPath, sizeState, check3JumpState, heq, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check3_skip (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (h : input.size ≠ 161) :
    Challenge.EvmProof.Stepper.runLocatedBlock check3Path (sizeState input 1346) =
      some (sizeState input 1354) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 161) (UInt256.ofNat input.size) = UInt256.ofNat 0 :=
    Logic.eq_ofNat_of_ne (by norm_num) hsize h
  simp [check3Path, sizeState, heq, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def check4JumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1361
      stack := [UInt256.ofNat 1865, UInt256.ofNat 1, UInt256.ofNat input.size] }

def check4_jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1007 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

theorem run_check4_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated check4_jumpLocated (check4JumpState input) =
      some (sizeState input 1865) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1865 = true :=
    Artifact.isValidJumpDest_index 1208 (by rfl)
  have hpc : (check4JumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1007 := by
    simp [check4JumpState, initialState, PCs.pc0, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken check4_jumpLocated rfl (check4JumpState input) 1865 (UInt256.ofNat 1) [UInt256.ofNat input.size] hpc rfl (by simp) Logic.isTrue_one rfl (by norm_num) hjump).trans rfl

theorem run_check4_taken_prefix (input : ByteArray) (h : input.size = 160) :
    Challenge.EvmProof.Stepper.runLocatedBlock check4PrefixPath (sizeState input 1354) =
      some (check4JumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 160) (UInt256.ofNat input.size) = UInt256.ofNat 1 :=
    Logic.eq_ofNat_of_eq h
  simp [check4PrefixPath, sizeState, check4JumpState, heq, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check4_skip (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (h : input.size ≠ 160) :
    Challenge.EvmProof.Stepper.runLocatedBlock check4Path (sizeState input 1354) =
      some (sizeState input 1362) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 160) (UInt256.ofNat input.size) = UInt256.ofNat 0 :=
    Logic.eq_ofNat_of_ne (by norm_num) hsize h
  simp [check4Path, sizeState, heq, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def check5JumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1369
      stack := [UInt256.ofNat 1975, UInt256.ofNat 1, UInt256.ofNat input.size] }

def check5_jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1012 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

theorem run_check5_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated check5_jumpLocated (check5JumpState input) =
      some (sizeState input 1975) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1975 = true :=
    Artifact.isValidJumpDest_index 1243 (by rfl)
  have hpc : (check5JumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1012 := by
    simp [check5JumpState, initialState, PCs.pc1, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken check5_jumpLocated rfl (check5JumpState input) 1975 (UInt256.ofNat 1) [UInt256.ofNat input.size] hpc rfl (by simp) Logic.isTrue_one rfl (by norm_num) hjump).trans rfl

theorem run_check5_taken_prefix (input : ByteArray) (h : input.size = 100) :
    Challenge.EvmProof.Stepper.runLocatedBlock check5PrefixPath (sizeState input 1362) =
      some (check5JumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 100) (UInt256.ofNat input.size) = UInt256.ofNat 1 :=
    Logic.eq_ofNat_of_eq h
  simp [check5PrefixPath, sizeState, check5JumpState, heq, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check5_skip (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (h : input.size ≠ 100) :
    Challenge.EvmProof.Stepper.runLocatedBlock check5Path (sizeState input 1362) =
      some (sizeState input 1370) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 100) (UInt256.ofNat input.size) = UInt256.ofNat 0 :=
    Logic.eq_ofNat_of_ne (by norm_num) hsize h
  simp [check5Path, sizeState, heq, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def check6JumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1377
      stack := [UInt256.ofNat 2089, UInt256.ofNat 1, UInt256.ofNat input.size] }

def check6_jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1017 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

theorem run_check6_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated check6_jumpLocated (check6JumpState input) =
      some (sizeState input 2089) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 2089 = true :=
    Artifact.isValidJumpDest_index 1281 (by rfl)
  have hpc : (check6JumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1017 := by
    simp [check6JumpState, initialState, PCs.pc1, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken check6_jumpLocated rfl (check6JumpState input) 2089 (UInt256.ofNat 1) [UInt256.ofNat input.size] hpc rfl (by simp) Logic.isTrue_one rfl (by norm_num) hjump).trans rfl

theorem run_check6_taken_prefix (input : ByteArray) (h : input.size = 163) :
    Challenge.EvmProof.Stepper.runLocatedBlock check6PrefixPath (sizeState input 1370) =
      some (check6JumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 163) (UInt256.ofNat input.size) = UInt256.ofNat 1 :=
    Logic.eq_ofNat_of_eq h
  simp [check6PrefixPath, sizeState, check6JumpState, heq, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check6_skip (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (h : input.size ≠ 163) :
    Challenge.EvmProof.Stepper.runLocatedBlock check6Path (sizeState input 1370) =
      some (sizeState input 1378) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 163) (UInt256.ofNat input.size) = UInt256.ofNat 0 :=
    Logic.eq_ofNat_of_ne (by norm_num) hsize h
  simp [check6Path, sizeState, heq, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def check7JumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1385
      stack := [UInt256.ofNat 2273, UInt256.ofNat 1, UInt256.ofNat input.size] }

def check7_jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1022 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

theorem run_check7_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated check7_jumpLocated (check7JumpState input) =
      some (sizeState input 2273) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 2273 = true :=
    Artifact.isValidJumpDest_index 1324 (by rfl)
  have hpc : (check7JumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1022 := by
    simp [check7JumpState, initialState, PCs.pc1, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken check7_jumpLocated rfl (check7JumpState input) 2273 (UInt256.ofNat 1) [UInt256.ofNat input.size] hpc rfl (by simp) Logic.isTrue_one rfl (by norm_num) hjump).trans rfl

theorem run_check7_taken_prefix (input : ByteArray) (h : input.size = 192) :
    Challenge.EvmProof.Stepper.runLocatedBlock check7PrefixPath (sizeState input 1378) =
      some (check7JumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 192) (UInt256.ofNat input.size) = UInt256.ofNat 1 :=
    Logic.eq_ofNat_of_eq h
  simp [check7PrefixPath, sizeState, check7JumpState, heq, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check7_skip (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (h : input.size ≠ 192) :
    Challenge.EvmProof.Stepper.runLocatedBlock check7Path (sizeState input 1378) =
      some (sizeState input 1386) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 192) (UInt256.ofNat input.size) = UInt256.ofNat 0 :=
    Logic.eq_ofNat_of_ne (by norm_num) hsize h
  simp [check7Path, sizeState, heq, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def check8JumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1394
      stack := [UInt256.ofNat 2640, UInt256.ofNat 1, UInt256.ofNat input.size] }

def check8_jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1027 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

theorem run_check8_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated check8_jumpLocated (check8JumpState input) =
      some (sizeState input 2640) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 2640 = true :=
    Artifact.isValidJumpDest_index 1409 (by rfl)
  have hpc : (check8JumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1027 := by
    simp [check8JumpState, initialState, PCs.pc1, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken check8_jumpLocated rfl (check8JumpState input) 2640 (UInt256.ofNat 1) [UInt256.ofNat input.size] hpc rfl (by simp) Logic.isTrue_one rfl (by norm_num) hjump).trans rfl

theorem run_check8_taken_prefix (input : ByteArray) (h : input.size = 353) :
    Challenge.EvmProof.Stepper.runLocatedBlock check8PrefixPath (sizeState input 1386) =
      some (check8JumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 353) (UInt256.ofNat input.size) = UInt256.ofNat 1 :=
    Logic.eq_ofNat_of_eq h
  simp [check8PrefixPath, sizeState, check8JumpState, heq, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check8_skip (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (h : input.size ≠ 353) :
    Challenge.EvmProof.Stepper.runLocatedBlock check8Path (sizeState input 1386) =
      some (sizeState input 1395) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 353) (UInt256.ofNat input.size) = UInt256.ofNat 0 :=
    Logic.eq_ofNat_of_ne (by norm_num) hsize h
  simp [check8Path, sizeState, heq, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def check9JumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1403
      stack := [UInt256.ofNat 3164, UInt256.ofNat 1, UInt256.ofNat input.size] }

def check9_jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1032 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

theorem run_check9_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated check9_jumpLocated (check9JumpState input) =
      some (sizeState input 3164) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 3164 = true :=
    Artifact.isValidJumpDest_index 1491 (by rfl)
  have hpc : (check9JumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1032 := by
    simp [check9JumpState, initialState, PCs.pc1, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken check9_jumpLocated rfl (check9JumpState input) 3164 (UInt256.ofNat 1) [UInt256.ofNat input.size] hpc rfl (by simp) Logic.isTrue_one rfl (by norm_num) hjump).trans rfl

theorem run_check9_taken_prefix (input : ByteArray) (h : input.size = 611) :
    Challenge.EvmProof.Stepper.runLocatedBlock check9PrefixPath (sizeState input 1395) =
      some (check9JumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 611) (UInt256.ofNat input.size) = UInt256.ofNat 1 :=
    Logic.eq_ofNat_of_eq h
  simp [check9PrefixPath, sizeState, check9JumpState, heq, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check9_skip (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (h : input.size ≠ 611) :
    Challenge.EvmProof.Stepper.runLocatedBlock check9Path (sizeState input 1395) =
      some (sizeState input 1404) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 611) (UInt256.ofNat input.size) = UInt256.ofNat 0 :=
    Logic.eq_ofNat_of_ne (by norm_num) hsize h
  simp [check9Path, sizeState, heq, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def exitJumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1408
      stack := [UInt256.ofNat 1196] }

def exitJumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1035 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))

theorem run_exit_prefix (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock exitPrefixPath (sizeState input 1404) =
      some (exitJumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [exitPrefixPath, sizeState, exitJumpState, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_exit_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated exitJumpLocated (exitJumpState input) =
      some (Main.trampolineState input 1196) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1196 = true :=
    Artifact.isValidJumpDest_index 899 (by rfl)
  have hpc : (exitJumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1035 := by
    simp [exitJumpState, initialState, PCs.pc1, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jump exitJumpLocated rfl (exitJumpState input) 1196 [] hpc rfl (by simp) rfl (by norm_num) hjump).trans rfl

end Challenge.Modexp.Submission.Proofs.Memo.Dispatch
