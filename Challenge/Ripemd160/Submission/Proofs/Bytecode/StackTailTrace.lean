import Batteries.Tactic.OpenPrivate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackPC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactSegment

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-!
# Located H31b final-combination trace

The raw tail theorem is lifted through the exact H31b artifact.  The path starts
at instruction 1646 and ends at instruction 1706.  The 713 helper instructions
after the tail remain in the artifact suffix.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTailTrace

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackTail

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) :=
  Challenge.EvmProof.Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

open private submissionInstructionsChunk0 submissionInstructionsChunk1
  submissionInstructionsChunk2 submissionInstructionsChunk3
  submissionInstructionsChunk4 submissionInstructionsChunk5
  submissionInstructionsChunk6 submissionInstructionsChunk7
  submissionInstructionsChunk8 submissionInstructionsChunk9
  submissionInstructionsChunk10 submissionInstructionsChunk11
  submissionInstructionsChunk12 submissionInstructionsChunk13
  submissionInstructionsChunk0_length submissionInstructionsChunk1_length
  submissionInstructionsChunk2_length submissionInstructionsChunk3_length
  submissionInstructionsChunk4_length submissionInstructionsChunk5_length
  submissionInstructionsChunk6_length submissionInstructionsChunk7_length
  submissionInstructionsChunk8_length submissionInstructionsChunk9_length
  submissionInstructionsChunk10_length submissionInstructionsChunk11_length
  submissionInstructionsChunk12_length submissionInstructionsChunk13_length
  wfOp
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

def artifactPrefix : List Instr :=
  submissionInstructionsChunk0 ++ submissionInstructionsChunk1 ++
  submissionInstructionsChunk2 ++ submissionInstructionsChunk3 ++
  submissionInstructionsChunk4 ++ submissionInstructionsChunk5 ++
  submissionInstructionsChunk6 ++ submissionInstructionsChunk7

def tailBefore : List Instr :=
  artifactPrefix ++ submissionInstructionsChunk8.take 46

def tailAfter : List Instr :=
  submissionInstructionsChunk8.drop 107 ++ submissionInstructionsChunk9 ++
    submissionInstructionsChunk10 ++ submissionInstructionsChunk11 ++
    submissionInstructionsChunk12 ++ submissionInstructionsChunk13

private theorem artifactPrefix_length : artifactPrefix.length = 1600 := by
  simp [artifactPrefix]

private theorem tailBefore_length : tailBefore.length = 1646 := by
  simp [tailBefore, artifactPrefix_length]

private theorem tailAfter_length : tailAfter.length = 713 := by
  simp [tailAfter]

private theorem tailAfter_nonempty : tailAfter ≠ [] := by
  intro h
  have : tailAfter.length = 0 := by simp [h]
  have hlen := tailAfter_length
  omega

private theorem artifactChunk8_tail :
    submissionInstructionsChunk8 =
      submissionInstructionsChunk8.take 46 ++
        StackTail.tailInstructions ++ submissionInstructionsChunk8.drop 107 := by
  rfl

private theorem artifact_tail_split :
    Artifact.submissionArtifact.instructions =
      tailBefore ++ StackTail.tailInstructions ++ tailAfter := by
  change Artifact.submissionInstructions =
    (artifactPrefix ++ submissionInstructionsChunk8.take 46) ++
      StackTail.tailInstructions ++
      (submissionInstructionsChunk8.drop 107 ++ submissionInstructionsChunk9 ++
        submissionInstructionsChunk10 ++ submissionInstructionsChunk11 ++
        submissionInstructionsChunk12 ++ submissionInstructionsChunk13)
  have hprefix : Artifact.submissionInstructions =
      artifactPrefix ++ submissionInstructionsChunk8 ++
        submissionInstructionsChunk9 ++ submissionInstructionsChunk10 ++
        submissionInstructionsChunk11 ++ submissionInstructionsChunk12 ++
        submissionInstructionsChunk13 := by
    simp only [Artifact.submissionInstructions, artifactPrefix, List.append_assoc]
  rw [hprefix]
  conv_lhs => rw [artifactChunk8_tail]
  simp only [List.append_assoc]

private theorem tailInstructions_length : StackTail.tailInstructions.length = 61 := by
  decide

private theorem tailByteLength :
    StackPC.byteLength StackTail.tailInstructions = 91 := by
  decide

private theorem instructionPC_segment_of_byteLength
    (p : Challenge.EvmProof.ProgramArtifact)
    (before segment after : List Instr) (startIndex startPC : Nat)
    (hsplit : p.instructions = before ++ segment ++ after)
    (hindex : before.length = startIndex)
    (hpc : p.instructionPC startIndex = startPC)
    (i : Nat) (hi : i ≤ segment.length) :
    p.instructionPC (startIndex + i) =
      startPC + StackPC.byteLength (segment.take i) := by
  have hzero := ArtifactSegment.instructionPC_segment p before segment after
    hsplit 0 (by omega)
  have hzero' : p.instructionPC startIndex = (assembleBytes before).length := by
    simpa [hindex] using hzero
  have hbefore : (assembleBytes before).length = startPC :=
    hzero'.symm.trans hpc
  have h := ArtifactSegment.instructionPC_segment_of_bounds p before segment after
    startIndex startPC hsplit hindex hbefore i hi
  simpa only [StackPC.byteLength_eq_assemble] using h

private theorem tail_instruction_at (i : Nat)
    (hi : i < StackTail.tailInstructions.length) :
    Artifact.submissionArtifact.instructions[1646 + i]? =
      StackTail.tailInstructions[i]? := by
  have h := ArtifactSegment.getElem?_segment
    Artifact.submissionArtifact tailBefore StackTail.tailInstructions tailAfter
    artifact_tail_split i hi
  simpa [tailBefore_length] using h

private theorem tail_instruction_pc (i : Nat)
    (hi : i ≤ StackTail.tailInstructions.length) :
    Artifact.submissionArtifact.instructionPC (1646 + i) =
      0xcef + StackPC.byteLength (StackTail.tailInstructions.take i) := by
  exact instructionPC_segment_of_byteLength Artifact.submissionArtifact
    tailBefore StackTail.tailInstructions tailAfter 1646 0xcef
    artifact_tail_split tailBefore_length StackPC.tailPC i hi

private theorem tail_instruction_pc_global (index : Nat)
    (hlo : 1646 ≤ index) (hhi : index ≤ 1707) :
    Artifact.submissionArtifact.instructionPC index =
      0xcef +
        StackPC.byteLength (StackTail.tailInstructions.take (index - 1646)) := by
  have hi : index - 1646 ≤ StackTail.tailInstructions.length := by
    rw [tailInstructions_length]
    omega
  have h := tail_instruction_pc (index - 1646) hi
  simpa only [Nat.add_sub_of_le hlo] using h

private theorem finalJumpPC :
    Artifact.submissionArtifact.instructionPC 1640 = 0xada := by
  have h := tail_instruction_pc 60 (by decide)
  simpa [StackTail.tailInstructions, StackTail.tail60Instructions,
    StackTail.c0Instructions, StackTail.c1Instructions,
    StackTail.c2Instructions, StackTail.c3Instructions,
    StackTail.c4Instructions, StackTail.storeH0Instructions,
    StackTail.cleanupInstructions, StackTail.finalJumpInstructions,
    StackPC.byteLength] using h

private theorem tail_instruction_wellFormed (i : Nat)
    (hi : i < StackTail.tailInstructions.length) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka
      ((StackTail.tailInstructions)[i]'(by exact hi)) := by
  have hlt : i < 61 := by simpa [tailInstructions_length] using hi
  have hle : i ≤ 60 := by omega
  interval_cases i <;>
    simp [StackTail.tailInstructions, StackTail.tail60Instructions,
      StackTail.c0Instructions, StackTail.c1Instructions, StackTail.c2Instructions,
      StackTail.c3Instructions, StackTail.c4Instructions, StackTail.storeH0Instructions,
      StackTail.cleanupInstructions, StackTail.finalJumpInstructions,
      Challenge.EvmProof.Stepper.WellFormed, YulEvmCompiler.plainOp] <;>
    decide

def tailLocated (i : Nat) (hi : i < StackTail.tailInstructions.length) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka where
  index := 1646 + i
  instruction := ((StackTail.tailInstructions)[i]'(by exact hi))
  atIndex := by
    have h := tail_instruction_at i hi
    simpa [List.getElem?_eq_getElem hi] using h
  wellFormed := tail_instruction_wellFormed i hi

def tailPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  (List.finRange StackTail.tailInstructions.length).map
    (fun i => tailLocated i.val i.isLt)

private def tailPath8 : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [tailLocated 0 (by decide), tailLocated 1 (by decide),
   tailLocated 2 (by decide), tailLocated 3 (by decide),
   tailLocated 4 (by decide), tailLocated 5 (by decide),
   tailLocated 6 (by decide), tailLocated 7 (by decide)]

private theorem runLocatedBlock_tail8 (s : State)
    (left right : Compression.EvmWorking) (ret : UInt256) (rest : List UInt256)
    (hrun : s.halt = .Running)
    (hstack : rest.length < 1009) :
    Challenge.EvmProof.Stepper.runLocatedBlock tailPath8
        (StackTail.tailEntry s left right ret rest) =
      StackTail.runTailInstrs StackTail.c0Instructions
        (StackTail.tailEntry s left right ret rest) := by
  have hcap11 : rest.length + 11 < 1024 := by omega
  have hcap12 : rest.length + 12 < 1024 := by omega
  have hcap13 : rest.length + 13 < 1024 := by omega
  have hcap14 : rest.length + 14 < 1024 := by omega
  have hpc0 := tail_instruction_pc 0 (by decide)
  have hpc1 := tail_instruction_pc 1 (by decide)
  have hpc2 := tail_instruction_pc 2 (by decide)
  have hpc3 := tail_instruction_pc 3 (by decide)
  have hpc4 := tail_instruction_pc 4 (by decide)
  have hpc5 := tail_instruction_pc 5 (by decide)
  have hpc6 := tail_instruction_pc 6 (by decide)
  have hpc7 := tail_instruction_pc 7 (by decide)
  simp (discharger := omega) [tailPath8, tailLocated,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, hpc0, hpc1, hpc2, hpc3, hpc4,
    hpc5, hpc6, hpc7,
    StackTail.tailInstructions, StackTail.tail60Instructions,
    StackTail.c0Instructions, StackTail.tailEntry, StackTail.workingStack,
    StackTail.runTailInstrs, Challenge.EvmProof.Stepper.runInstr, hrun,
    hcap11, hcap12, hcap13, hcap14, Nat.add_assoc,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    StackPC.byteLength]

set_option linter.unusedSimpArgs false in
private theorem runLocatedBlock_tail_raw (s : State)
    (left right : Compression.EvmWorking) (ret : UInt256) (rest : List UInt256)
    (hrun : s.halt = .Running)
    (hstack : rest.length < 1009)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock tailPath
        (StackTail.tailEntry s left right ret rest) =
      StackTail.runTailInstrs StackTail.tailInstructions
        (StackTail.tailEntry s left right ret rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hcap7 : rest.length + 7 < 1024 := by omega
  have hcap8 : rest.length + 8 < 1024 := by omega
  have hcap9 : rest.length + 9 < 1024 := by omega
  have hcap10 : rest.length + 10 < 1024 := by omega
  have hcap11 : rest.length + 11 < 1024 := by omega
  have hcap12 : rest.length + 12 < 1024 := by omega
  have hcap13 : rest.length + 13 < 1024 := by omega
  have hcap14 : rest.length + 14 < 1024 := by omega
  have hcap15 : rest.length + 15 < 1024 := by omega
  simp (config := { maxSteps := 1000000 }) (discharger := omega)
    [tailPath, List.finRange_succ, tailLocated,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, tail_instruction_pc_global,
      StackTail.tailInstructions, StackTail.tail60Instructions,
      StackTail.c0Instructions, StackTail.c1Instructions,
      StackTail.c2Instructions, StackTail.c3Instructions,
      StackTail.c4Instructions, StackTail.storeH0Instructions,
      StackTail.cleanupInstructions, StackTail.finalJumpInstructions,
      StackTail.tailEntry, StackTail.workingStack,
      StackTail.runTailInstrs, Challenge.EvmProof.Stepper.runInstr, hrun,
      hvalid,
      hcap0, hcap1, hcap2, hcap3, hcap4, hcap5, hcap6, hcap7, hcap8, hcap9,
      hcap10, hcap11, hcap12, hcap13, hcap14, hcap15, Nat.add_assoc,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      StackPC.byteLength]

theorem tailPath_length : tailPath.length = 61 := by
  simp [tailPath, tailInstructions_length]

def actualTailResult (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) : State :=
  StackTail.tailResult s left right ret rest

private theorem runTailInstrs_append {xs ys : List Instr} {s t u : State}
    (hxs : StackTail.runTailInstrs xs s = some t)
    (hys : StackTail.runTailInstrs ys t = some u) :
    StackTail.runTailInstrs (xs ++ ys) s = some u := by
  induction xs generalizing s t with
  | nil =>
      simp [StackTail.runTailInstrs] at hxs
      subst t
      simpa [StackTail.runTailInstrs] using hys
  | cons instruction instructions ih =>
      cases hstep : Challenge.EvmProof.Stepper.runInstr instruction s with
      | none =>
          simp [StackTail.runTailInstrs, hstep] at hxs
      | some next =>
          have hrest : StackTail.runTailInstrs instructions next = some t := by
            simpa [StackTail.runTailInstrs, hstep] using hxs
          have h := ih hrest hys
          simpa [StackTail.runTailInstrs, hstep] using h

set_option linter.unusedSimpArgs false in
private theorem runLocatedBlock_tail (s : State)
    (left right : Compression.EvmWorking) (ret : UInt256) (rest : List UInt256)
    (hactive : 67 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1009)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock tailPath
        (StackTail.tailEntry s left right ret rest) =
      some (actualTailResult s left right ret rest) := by
  rw [runLocatedBlock_tail_raw s left right ret rest hrun hstack hvalid]
  have h60 := StackTail.run_tail60 s left right ret rest hactive hstack
  have hj := StackTail.run_tail_jump s left right ret rest hactive hstack hvalid
  have hall := runTailInstrs_append h60 hj
  simpa [StackTail.tailInstructions, actualTailResult] using hall

def actualTailGasSteps (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256)
    (hactive : 67 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1009)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    Challenge.EvmProof.GasSteps
      (StackTail.tailEntry s left right ret rest)
      (actualTailResult s left right ret rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tailPath
  · simpa [StackTail.tailEntry] using hcode
  · simpa [StackTail.tailEntry] using hfork
  · exact runLocatedBlock_tail s left right ret rest hactive hstack hrun hvalid
  · simpa [StackTail.tailEntry] using hrun
  · simpa [StackTail.tailEntry] using hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTailTrace
