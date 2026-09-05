import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairSitesBase
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairCallTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairHelperTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairSites

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

private theorem leftWrapper_slice (k : Fin 40) :
    (Artifact.instructions.drop (leftWrapperIndex k.val)).take
        (leftWrapperTemplate k).length = leftWrapperTemplate k := by
  fin_cases k <;> rfl

private theorem leftWrapper_fits (k : Fin 40) :
    leftWrapperIndex k.val + (leftWrapperTemplate k).length ≤
      Artifact.instructions.length := by
  change 930 + 8 * k.val + 8 ≤ Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  omega

private theorem leftWrapper_wellFormed (k : Fin 40) :
    StackRoundData.TemplateWellFormed (leftWrapperTemplate k) := by
  fin_cases k <;> decide

def leftWrapperSite (k : Fin 40) :
    GenericRoundSite Artifact .Osaka (leftWrapperTemplate k) :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact) (fork := .Osaka) (leftWrapperTemplate k)
    (leftWrapperIndex k.val) (leftWrapper_slice k) (leftWrapper_fits k)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (leftWrapper_wellFormed k))
    (by simp [leftWrapperTemplate, pairWrapperTemplate])

private theorem leftWrapperAt (k : Fin 40) (offset : Nat)
    (hoffset : offset < (leftWrapperTemplate k).length) :
    Artifact.instructions[leftWrapperIndex k.val + offset]? =
      some (leftWrapperTemplate k)[offset] :=
  getElem_of_slice _ _ (leftWrapper_slice k) _ hoffset

private theorem leftCall_slice (k : Fin 40) :
    (Artifact.instructions.drop (leftWrapperIndex k.val)).take
        (PairCallTrace.pairCallPushes (leftReturnPC k.val) (leftAddress0 k)
          (leftAddress1 k) (leftHelperPC k.val) (leftRotation0 k)
          (leftRotation1 k)).length =
      PairCallTrace.pairCallPushes (leftReturnPC k.val) (leftAddress0 k)
        (leftAddress1 k) (leftHelperPC k.val) (leftRotation0 k)
        (leftRotation1 k) := by
  have h := congrArg (fun xs : List Instr => xs.take 6) (leftWrapper_slice k)
  simpa [leftWrapperTemplate, pairWrapperTemplate, PairCallTrace.pairCallPushes,
    PairRoundState.pairCallPushes, List.take_take] using h

private theorem leftCall_fits (k : Fin 40) :
    leftWrapperIndex k.val +
        (PairCallTrace.pairCallPushes (leftReturnPC k.val) (leftAddress0 k)
          (leftAddress1 k) (leftHelperPC k.val) (leftRotation0 k)
          (leftRotation1 k)).length ≤ Artifact.instructions.length := by
  change 930 + 8 * k.val + 6 ≤ Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  omega

private theorem leftCall_wellFormed (k : Fin 40) :
    ∀ instruction ∈
        PairCallTrace.pairCallPushes (leftReturnPC k.val) (leftAddress0 k)
          (leftAddress1 k) (leftHelperPC k.val) (leftRotation0 k)
          (leftRotation1 k),
      Stepper.WellFormed .Osaka instruction := by
  intro instruction hmem
  apply StackRoundData.templateWellFormed_mem (leftWrapper_wellFormed k)
  change instruction ∈
    PairCallTrace.pairCallPushes (leftReturnPC k.val) (leftAddress0 k)
      (leftAddress1 k) (leftHelperPC k.val) (leftRotation0 k)
      (leftRotation1 k) ++ [op .JUMP, op .JUMPDEST]
  exact List.mem_append_left _ hmem

def leftCallPushes (k : Fin 40) :
    GenericRoundSite Artifact .Osaka
      (PairCallTrace.pairCallPushes (leftReturnPC k.val) (leftAddress0 k)
        (leftAddress1 k) (leftHelperPC k.val) (leftRotation0 k)
        (leftRotation1 k)) :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact) (fork := .Osaka)
    (PairCallTrace.pairCallPushes (leftReturnPC k.val) (leftAddress0 k)
      (leftAddress1 k) (leftHelperPC k.val) (leftRotation0 k)
      (leftRotation1 k))
    (leftWrapperIndex k.val) (leftCall_slice k) (leftCall_fits k)
    StackRoundData.artifact_code_bound (leftCall_wellFormed k)
    (by simp [PairCallTrace.pairCallPushes, PairRoundState.pairCallPushes])

def leftCallJump (k : Fin 40) : LocatedSite Artifact .Osaka where
  located :=
    { index := leftWrapperIndex k.val + 6
      instruction := .op .JUMP
      atIndex := by
        simpa [leftWrapperTemplate, pairWrapperTemplate,
          PairRoundState.pairCallPushes, PairCallTrace.pairCallPushes, op] using
          leftWrapperAt k 6 (by
            simp [leftWrapperTemplate, pairWrapperTemplate,
              PairRoundState.pairCallPushes])
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := leftJumpPC k.val
  pc_eq := pc_toNat_instructionPC _

private theorem leftCallPushes_end_eq (k : Fin 40) :
    (leftCallJump k).pc = (leftCallPushes k).endPC := by
  have hend := StackRoundTrace.endPC_eq_pcAfter_sites
    (leftCallPushes k).sites (leftCallPushes k).startPC
    (leftCallPushes k).endPC (leftCallPushes k).head_eq
    (leftCallPushes k).end_eq (leftCallPushes k).contiguous
  rw [(leftCallPushes k).instruction_eq] at hend
  have hstart : (leftCallPushes k).startPC = leftPC k.val := by
    rfl
  rw [hstart] at hend
  calc
    (leftCallJump k).pc = leftJumpPC k.val := by simp [leftCallJump]
    _ = StackRoundTrace.pcAfter (leftPC k.val)
        (PairCallTrace.pairCallPushes (leftReturnPC k.val) (leftAddress0 k)
          (leftAddress1 k) (leftHelperPC k.val) (leftRotation0 k)
          (leftRotation1 k)) := by
      fin_cases k <;> rfl
    _ = (leftCallPushes k).endPC := hend.symm

def leftReturnSite (k : Fin 40) : LocatedSite Artifact .Osaka where
  located :=
    { index := leftWrapperIndex k.val + 7
      instruction := .op .JUMPDEST
      atIndex := by
        simpa [leftWrapperTemplate, pairWrapperTemplate,
          PairRoundState.pairCallPushes, PairCallTrace.pairCallPushes, op] using
          leftWrapperAt k 7 (by
            simp [leftWrapperTemplate, pairWrapperTemplate,
              PairRoundState.pairCallPushes])
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := leftReturnPC k.val
  pc_eq := pc_toNat_instructionPC _

def leftCallSite (k : Fin 40) :
    PairCallTrace.CallSite Artifact .Osaka
      (leftReturnPC k.val) (leftAddress0 k) (leftAddress1 k)
      (leftHelperPC k.val) (leftRotation0 k) (leftRotation1 k) where
  pushes := leftCallPushes k
  jump := leftCallJump k
  jump_instr := by simp [leftCallJump]
  jump_pc := leftCallPushes_end_eq k

theorem leftCallSite_start (k : Fin 40) :
    (leftCallSite k).pushes.startPC = leftPC k.val := by
  rfl

theorem leftReturnSite_at (k : Fin 40) :
    (leftReturnSite k).pc = leftReturnPC k.val := by
  simp [leftReturnSite]

theorem leftReturnSite_succ_next (k : Fin 40) :
    (leftReturnSite k).pc.succ = leftPC (k.val + 1) := by
  fin_cases k <;> decide

private theorem leftHelper_slice (group : Fin 5) :
    (Artifact.instructions.drop (leftHelperStartIndex group.val)).take
        (leftHelperTemplate group).length = leftHelperTemplate group := by
  fin_cases group <;> rfl

private theorem leftHelper_fits (group : Fin 5) :
    leftHelperStartIndex group.val + (leftHelperTemplate group).length ≤
      Artifact.instructions.length := by
  change leftHelperStartIndex group.val +
      (pairBeforeJumpTemplate group.val
        (StackRoundData.leftConstant (16 * group.val))).length ≤
      Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  fin_cases group <;> decide

private theorem leftHelper_wellFormed (group : Fin 5) :
    StackRoundData.TemplateWellFormed (leftHelperTemplate group) := by
  fin_cases group <;> decide

def leftHelperSite (group : Fin 5) :
    GenericRoundSite Artifact .Osaka (leftHelperTemplate group) :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact) (fork := .Osaka) (leftHelperTemplate group)
    (leftHelperStartIndex group.val) (leftHelper_slice group) (leftHelper_fits group)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (leftHelper_wellFormed group))
    (by
      change pairBeforeJumpTemplate group.val
        (StackRoundData.leftConstant (16 * group.val)) ≠ []
      fin_cases group <;> decide)

theorem leftHelperSite_start_eq (group : Fin 5) :
    (leftHelperSite group).startPC = leftHelperPCOfGroup group.val := by
  fin_cases group <;> rfl

theorem leftHelperEndIndex (group : Fin 5) :
    leftHelperStartIndex group.val + (leftHelperTemplate group).length =
      leftHelperJumpIndex group.val := by
  fin_cases group <;> rfl

def leftHelperJump (group : Fin 5) : LocatedSite Artifact .Osaka where
  located :=
    { index := leftHelperJumpIndex group.val
      instruction := .op .JUMP
      atIndex := by fin_cases group <;> rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat (Artifact.instructionPC (leftHelperJumpIndex group.val))
  pc_eq := pc_toNat_instructionPC _

theorem leftHelperSite_end_eq (group : Fin 5) :
    (leftHelperJump group).pc = (leftHelperSite group).endPC := by
  have hend := StackRoundTrace.endPC_eq_pcAfter_sites
    (leftHelperSite group).sites (leftHelperSite group).startPC
    (leftHelperSite group).endPC (leftHelperSite group).head_eq
    (leftHelperSite group).end_eq (leftHelperSite group).contiguous
  rw [(leftHelperSite group).instruction_eq] at hend
  rw [leftHelperSite_start_eq group] at hend
  calc
    (leftHelperJump group).pc =
        UInt256.ofNat (Artifact.instructionPC (leftHelperJumpIndex group.val)) := by
          simp [leftHelperJump]
    _ = StackRoundTrace.pcAfter (leftHelperPCOfGroup group.val)
        (leftHelperTemplate group) := by
          fin_cases group <;> rfl
    _ = (leftHelperSite group).endPC := hend.symm

theorem leftHelper_valid (group : Fin 5) :
    Decode.isValidJumpDest Artifact.code
      (leftHelperPCOfGroup group.val).toNat = true := by
  have hpc : (leftHelperPCOfGroup group.val).toNat =
      Artifact.instructionPC (leftHelperStartIndex group.val) := by
    fin_cases group <;> rfl
  rw [hpc]
  exact Artifact.isValidJumpDest_index (leftHelperStartIndex group.val)
    (by fin_cases group <;> rfl)

theorem leftReturn_valid (k : Fin 40) :
    Decode.isValidJumpDest Artifact.code (leftReturnPC k.val).toNat = true := by
  have hpc : (leftReturnPC k.val).toNat =
      Artifact.instructionPC (leftWrapperIndex k.val + 7) := by
    exact (leftReturnSite k).pc_eq
  rw [hpc]
  exact Artifact.isValidJumpDest_index (leftWrapperIndex k.val + 7)
    (leftReturnSite k).located.atIndex

def leftRoundSite (k : Fin 40) :
    PairHelperTrace.RoundSite Artifact .Osaka
      (k.val / 8) (leftAddress0 k) (leftAddress1 k)
      (leftRotation0 k) (leftRotation1 k) (leftConstant k) where
  returnPC := leftReturnPC k.val
  helperPC := leftHelperPC k.val
  call := leftCallSite k
  helper := castTemplate (leftHelperSite ⟨k.val / 8, by omega⟩) (by rfl)
  helper_start := by
    rw [castTemplate_start]
    exact leftHelperSite_start_eq ⟨k.val / 8, by omega⟩
  helperJump := leftHelperJump ⟨k.val / 8, by omega⟩
  helper_jump_instr := by rfl
  helper_end := by
    rw [castTemplate_end]
    exact leftHelperSite_end_eq ⟨k.val / 8, by omega⟩
  returnSite := leftReturnSite k
  return_instr := by rfl
  return_at := by rfl
  helper_valid := leftHelper_valid ⟨k.val / 8, by omega⟩
  return_valid := leftReturn_valid k

theorem leftRoundSite_start (k : Fin 40) :
    (leftRoundSite k).call.pushes.startPC = leftPC k.val := by
  exact leftCallSite_start k

theorem leftRoundSite_end (k : Fin 40) :
    (leftRoundSite k).returnSite.pc.succ = leftPC (k.val + 1) := by
  exact leftReturnSite_succ_next k

theorem leftRotation0_le32 (k : Fin 40) : leftRotation0 k ≤ 32 := by
  fin_cases k <;> decide

theorem leftRotation1_le32 (k : Fin 40) : leftRotation1 k ≤ 32 := by
  fin_cases k <;> decide

@[simp] theorem leftPC_zero : leftPC 0 = UInt256.ofNat 0x533 := by rfl

@[simp] theorem leftPC_end : leftPC 40 = UInt256.ofNat 0x803 := by rfl

@[simp] theorem leftStartPC_eq : leftStartPC = UInt256.ofNat 0x533 := by rfl

@[simp] theorem leftEndPC_eq : leftEndPC = UInt256.ofNat 0x803 := by rfl

theorem leftPC_succ (k : Fin 40) :
    leftPC (k.val + 1) = leftPC k.val + UInt256.ofNat 18 := by
  fin_cases k <;> rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairSites
