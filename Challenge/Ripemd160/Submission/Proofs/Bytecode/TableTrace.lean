import Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Schedule
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.InitializationCorrect
import YulEvmCompiler.BytesLemmas
import Challenge.EvmProof.Bytes

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Direct traces for RIPEMD-160 memory helpers

This module certifies the five small word/table accessors at artifact indices
23 through 104.  The state transformers are caller-parametric, so the facts
compose both with initialization and with the schedule/round traces.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.TableTrace

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def hAtPath : List Located :=
  [⟨23, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨24, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨25, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨26, .push ⟨1, by decide⟩ (UInt256.ofNat 0x20), by rfl, by decide⟩,
   ⟨27, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨28, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨29, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨30, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨31, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def hSetPath : List Located :=
  [⟨38, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨39, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨40, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨41, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨42, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨43, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨44, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨45, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨46, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨47, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨48, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def xAtPath : List Located :=
  [⟨55, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨56, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨57, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨58, .push ⟨2, by decide⟩ (UInt256.ofNat 672), by rfl, by decide⟩,
   ⟨59, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨60, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨61, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨62, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨63, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def xSetPath : List Located := Schedule.xSetPath

def tableAtPath : List Located :=
  [⟨86, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨87, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨88, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨89, .push ⟨1, by decide⟩ (UInt256.ofNat 31), by rfl, by decide⟩,
   ⟨90, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨91, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨92, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨93, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem hAtPC (j : Nat) (hlo : 23 ≤ j) (hhi : j ≤ 34) :
    Artifact.submissionArtifact.instructionPC j =
      [0x20, 0x21, 0x23, 0x24, 0x26, 0x27, 0x28, 0x29,
        0x2a, 0x2b, 0x2c, 0x2d][j - 23]! := by
  interval_cases j <;> rfl

@[simp] private theorem hSetPC (j : Nat) (hlo : 38 ≤ j) (hhi : j ≤ 51) :
    Artifact.submissionArtifact.instructionPC j =
      [51, 52, 53, 55, 56, 57, 58, 63, 64, 65, 66, 67, 68, 69][j - 38]! := by
  interval_cases j <;> rfl

@[simp] private theorem xAtPC (j : Nat) (hlo : 55 ≤ j) (hhi : j ≤ 66) :
    Artifact.submissionArtifact.instructionPC j =
      [75, 76, 78, 79, 82, 83, 84, 85, 86, 87, 88, 89][j - 55]! := by
  interval_cases j <;> rfl

@[simp] private theorem xSetPC (j : Nat) (hlo : 70 ≤ j) (hhi : j ≤ 82) :
    Artifact.submissionArtifact.instructionPC j =
      [95, 96, 98, 99, 102, 103, 104, 109, 110, 111, 112, 113, 114][j - 70]! := by
  interval_cases j <;> rfl

@[simp] private theorem tableAtPC (j : Nat) (hlo : 86 ≤ j) (hhi : j ≤ 104) :
    Artifact.submissionArtifact.instructionPC j =
      [120, 121, 122, 123, 125, 126, 127, 128, 129, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141][j - 86]! := by
  interval_cases j <;> rfl

def slotAddress (base i : UInt256) : UInt256 :=
  UInt256.shiftLeft i (UInt256.ofNat 5) + base

def loadedWord (s : State) (base i : UInt256) : UInt256 :=
  MachineState.readWord s.memory (slotAddress base i).toNat

def storedWord (s : State) (base i value : UInt256) : State :=
  let address := slotAddress base i
  let masked := UInt256.land value (UInt256.ofNat 0xffffffff)
  { s with
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded masked.toNat 32) address.toNat
    activeWords := s.activeWordsAfterUInt256 address.toNat 32 }

def tableAddress (base i : UInt256) : UInt256 :=
  (base - UInt256.ofNat 31) + i

def tableValue (s : State) (base i : UInt256) : UInt256 :=
  UInt256.byteAt (UInt256.ofNat 31)
    (MachineState.readWord s.memory (tableAddress base i).toNat)

def atEntry (s : State) (pc i returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := pc
           stack := [i, 0, returnDest] ++ rest }

def atReturned (s : State) (base i returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := returnDest
           stack := loadedWord s base i :: rest
           activeWords := s.activeWordsAfterUInt256 (slotAddress base i).toNat 32 }

def setEntry (s : State) (base i value returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x33
           stack := [base, i, value, returnDest] ++ rest }

def setReturned (s : State) (base i value returnDest : UInt256)
    (rest : List UInt256) : State :=
  { storedWord s base i value with
    pc := returnDest
    stack := rest }

def hSetEntry (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) : State :=
  setEntry s (UInt256.ofNat 0x20) i value returnDest rest

def hSetReturned (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) : State :=
  setReturned s (UInt256.ofNat 0x20) i value returnDest rest

def xSetEntry (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x5f
           stack := [i, value, returnDest] ++ rest }

def xSetReturned (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) : State :=
  { storedWord s (UInt256.ofNat 0x2a0) i value with
      pc := returnDest
      stack := rest }

def tableAtEntry (s : State) (base i returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x78
           stack := [base - UInt256.ofNat 31, i, 0, returnDest] ++ rest }

def tableAtReturned (s : State) (base i returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := returnDest
           stack := tableValue s base i :: rest
           activeWords := s.activeWordsAfterUInt256 (tableAddress base i).toNat 32 }

set_option linter.unusedSimpArgs false in
theorem run_hAt (s : State) (i returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1018)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock hAtPath
      (atEntry s (UInt256.ofNat 0x20) i returnDest rest) =
        some (atReturned s (UInt256.ofNat 0x20) i returnDest rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have haddr : UInt256.ofNat 0x20 +
      UInt256.shiftLeft i (UInt256.ofNat 5) =
        slotAddress (UInt256.ofNat 0x20) i := by
    rw [slotAddress, Challenge.EvmProof.Word.word_add_comm]
  simp [hAtPath, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    atEntry, atReturned, loadedWord, hc2, hc3, hc4, hc5, hrun, hcode, hvalid,
    haddr, List.exchange, State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_xAt (s : State) (i returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1018)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock xAtPath
      (atEntry s (UInt256.ofNat 0x4b) i returnDest rest) =
        some (atReturned s (UInt256.ofNat 0x2a0) i returnDest rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have haddr : UInt256.ofNat 0x2a0 +
      UInt256.shiftLeft i (UInt256.ofNat 5) =
        slotAddress (UInt256.ofNat 0x2a0) i := by
    rw [slotAddress, Challenge.EvmProof.Word.word_add_comm]
  simp [xAtPath, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    atEntry, atReturned, loadedWord, hc2, hc3, hc4, hc5, hrun, hcode, hvalid,
    haddr, List.exchange, State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_wordSet (s : State) (base i value returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock hSetPath
      (setEntry s base i value returnDest rest) =
        some (setReturned s base i value returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have haddr : base + UInt256.shiftLeft i (UInt256.ofNat 5) =
      slotAddress base i := by
    rw [slotAddress, Challenge.EvmProof.Word.word_add_comm]
  simp [hSetPath, Word.land_comm, List.exchange,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    setEntry, setReturned, storedWord, slotAddress, Challenge.EvmProof.Word.mask32,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hrun, hcode, hvalid, haddr,
    State.activeWordsAfterUInt256]

theorem run_hSet (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock hSetPath
      (hSetEntry s i value returnDest rest) =
        some (hSetReturned s i value returnDest rest) := by
  exact run_wordSet s (UInt256.ofNat 0x20) i value returnDest rest
    hstack hcode hrun hvalid

set_option linter.unusedSimpArgs false in
theorem run_xSet (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1017)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock xSetPath
      (xSetEntry s i value returnDest rest) =
        some (xSetReturned s i value returnDest rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have haddr : UInt256.ofNat 0x2a0 +
      UInt256.shiftLeft i (UInt256.ofNat 5) =
        slotAddress (UInt256.ofNat 0x2a0) i := by
    rw [slotAddress, Challenge.EvmProof.Word.word_add_comm]
  simp [xSetPath, Schedule.xSetPath, Word.land_comm, List.exchange,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    xSetEntry, xSetReturned, storedWord, Challenge.EvmProof.Word.mask32,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hrun, hcode, hvalid, haddr,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_tableAt (s : State) (base i returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock tableAtPath
      (tableAtEntry s base i returnDest rest) =
        some (tableAtReturned s base i returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  simp [tableAtPath, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    tableAtEntry, tableAtReturned, tableValue, tableAddress,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hrun, hcode, hvalid,
    List.exchange, State.activeWordsAfterUInt256]

def gasSteps_hAt (s : State) (i returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1018)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (atEntry s (UInt256.ofNat 0x20) i returnDest rest)
      (atReturned s (UInt256.ofNat 0x20) i returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka hAtPath
      (s := atEntry s (UInt256.ofNat 0x20) i returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_hAt s i returnDest rest hstack hcode hrun hvalid
  · exact hrun
  · exact hnp

def gasSteps_wordSet (s : State) (base i value returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (setEntry s base i value returnDest rest)
      (setReturned s base i value returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka hSetPath
      (s := setEntry s base i value returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_wordSet s base i value returnDest rest hstack hcode hrun hvalid
  · exact hrun
  · exact hnp

def gasSteps_hSet (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (hSetEntry s i value returnDest rest)
      (hSetReturned s i value returnDest rest) :=
  gasSteps_wordSet s (UInt256.ofNat 0x20) i value returnDest rest
    hstack hcode hfork hrun hnp hvalid

def gasSteps_xAt (s : State) (i returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1018)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (atEntry s (UInt256.ofNat 0x4b) i returnDest rest)
      (atReturned s (UInt256.ofNat 0x2a0) i returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka xAtPath
      (s := atEntry s (UInt256.ofNat 0x4b) i returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_xAt s i returnDest rest hstack hcode hrun hvalid
  · exact hrun
  · exact hnp

def gasSteps_xSet (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1017)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (xSetEntry s i value returnDest rest)
      (xSetReturned s i value returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka xSetPath
      (s := xSetEntry s i value returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_xSet s i value returnDest rest hstack hcode hrun hvalid
  · exact hrun
  · exact hnp

def gasSteps_tableAt (s : State) (base i returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (tableAtEntry s base i returnDest rest)
      (tableAtReturned s base i returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tableAtPath
      (s := tableAtEntry s base i returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_tableAt s base i returnDest rest hstack hcode hrun hvalid
  · exact hrun
  · exact hnp

@[simp] theorem storedWord_memory (s : State) (base i value : UInt256) :
    (storedWord s base i value).memory =
      MachineState.writeBytes s.memory
        (Data.Bytes.natToBytesPadded
          (UInt256.land value (UInt256.ofNat 0xffffffff)).toNat 32)
        (slotAddress base i).toNat := by
  rfl

@[simp] theorem loadedWord_storedWord (s : State) (base i value : UInt256) :
    loadedWord (storedWord s base i value) base i =
      UInt256.land value (UInt256.ofNat 0xffffffff) := by
  unfold loadedWord
  rw [storedWord_memory, Challenge.EvmProof.Memory.readWord_writeWord]

theorem loadedWord_storedWord_disjoint (s : State)
    (writeBase writeI value readBase readI : UInt256)
    (hdisjoint :
      (slotAddress readBase readI).toNat + 32 ≤
          (slotAddress writeBase writeI).toNat ∨
        (slotAddress writeBase writeI).toNat + 32 ≤
          (slotAddress readBase readI).toNat) :
    loadedWord (storedWord s writeBase writeI value) readBase readI =
      loadedWord s readBase readI := by
  unfold loadedWord
  rw [storedWord_memory,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using
      hdisjoint

theorem slotAddress_ofNat (base i : Nat)
    (hi : i < 2 ^ 256) (haddr : i * 32 + base < 2 ^ 256) :
    slotAddress (UInt256.ofNat base) (UInt256.ofNat i) =
      UInt256.ofNat (base + i * 32) := by
  unfold slotAddress
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat hi (by omega) (by
    norm_num at haddr ⊢
    omega)]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by
    norm_num at haddr ⊢
    exact haddr)]
  congr 1
  omega

/-- The generic `xAt` value specializes to the schedule's X-slot accessor. -/
theorem loadedWord_xValue (s : State) (i : Nat) (hi : i < 16) :
    loadedWord s (UInt256.ofNat 0x2a0) (UInt256.ofNat i) =
      ScheduleCorrect.xValue s i := by
  unfold loadedWord ScheduleCorrect.xValue
  rw [slotAddress_ofNat 0x2a0 i (by omega) (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), ScheduleCorrect.xSlotWord_toNat i hi]

@[simp] theorem tableBase1184 :
    UInt256.ofNat 1184 - UInt256.ofNat 31 = UInt256.ofNat 1153 := by decide

@[simp] theorem tableBase1280 :
    UInt256.ofNat 1280 - UInt256.ofNat 31 = UInt256.ofNat 1249 := by decide

@[simp] theorem tableBase1376 :
    UInt256.ofNat 1376 - UInt256.ofNat 31 = UInt256.ofNat 1345 := by decide

@[simp] theorem tableBase1472 :
    UInt256.ofNat 1472 - UInt256.ofNat 31 = UInt256.ofNat 1441 := by decide

private theorem tableAddress_ofNat (base i : Nat)
    (hlo : 31 ≤ base) (hbase : base < 2 ^ 64) (hi : i < 80) :
    tableAddress (UInt256.ofNat base) (UInt256.ofNat i) =
      UInt256.ofNat (base - 31 + i) := by
  unfold tableAddress
  rw [Challenge.EvmProof.Word.ofNat_sub_ofNat hlo (by omega),
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]

/-- The executed packed-table helper is exactly the initialization proof's
`tableByte` accessor on every RIPEMD table index. -/
theorem tableValue_tableByte (s : State) (base i : Nat)
    (hlo : 31 ≤ base) (hbase : base < 2 ^ 64) (hi : i < 80) :
    tableValue s (UInt256.ofNat base) (UInt256.ofNat i) =
      InitializationCorrect.tableByte s.memory base i := by
  unfold tableValue InitializationCorrect.tableByte
  rw [tableAddress_ofNat base i hlo hbase hi,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  rw [Challenge.EvmProof.Bytes.byteAt_readWord s.memory (base - 31 + i) 31 (by omega),
    Challenge.EvmProof.Bytes.byteAt_readWord s.memory (base + 32 * (i / 32))
      (i % 32) (Nat.mod_lt _ (by omega))]
  congr 3
  omega

end Challenge.Ripemd160.Submission.Proofs.Bytecode.TableTrace
