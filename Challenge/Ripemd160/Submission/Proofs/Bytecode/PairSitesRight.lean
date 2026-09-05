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

private theorem rightWrapper_slice (k : Fin 40) :
    (Artifact.instructions.drop (rightWrapperIndex k.val)).take
        (rightWrapperTemplate k).length = rightWrapperTemplate k := by
  fin_cases k <;> rfl

private theorem rightWrapper_fits (k : Fin 40) :
    rightWrapperIndex k.val + (rightWrapperTemplate k).length ≤
      Artifact.instructions.length := by
  change 1260 + 8 * k.val + 8 ≤ Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  omega

private theorem rightWrapper_wellFormed (k : Fin 40) :
    StackRoundData.TemplateWellFormed (rightWrapperTemplate k) := by
  fin_cases k <;> decide

def rightWrapperSite (k : Fin 40) :
    GenericRoundSite Artifact .Osaka (rightWrapperTemplate k) :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact) (fork := .Osaka) (rightWrapperTemplate k)
    (rightWrapperIndex k.val) (rightWrapper_slice k) (rightWrapper_fits k)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (rightWrapper_wellFormed k))
    (by simp [rightWrapperTemplate, pairWrapperTemplate])

private theorem rightWrapperAt (k : Fin 40) (offset : Nat)
    (hoffset : offset < (rightWrapperTemplate k).length) :
    Artifact.instructions[rightWrapperIndex k.val + offset]? =
      some (rightWrapperTemplate k)[offset] :=
  getElem_of_slice _ _ (rightWrapper_slice k) _ hoffset

private theorem rightCall_slice (k : Fin 40) :
    (Artifact.instructions.drop (rightWrapperIndex k.val)).take
        (PairCallTrace.pairCallPushes (rightReturnPC k.val) (rightAddress0 k)
          (rightAddress1 k) (rightHelperPC k.val) (rightRotation0 k)
          (rightRotation1 k)).length =
      PairCallTrace.pairCallPushes (rightReturnPC k.val) (rightAddress0 k)
        (rightAddress1 k) (rightHelperPC k.val) (rightRotation0 k)
        (rightRotation1 k) := by
  have h := congrArg (fun xs : List Instr => xs.take 6) (rightWrapper_slice k)
  simpa [rightWrapperTemplate, pairWrapperTemplate, PairCallTrace.pairCallPushes,
    PairRoundState.pairCallPushes, List.take_take] using h

private theorem rightCall_fits (k : Fin 40) :
    rightWrapperIndex k.val +
        (PairCallTrace.pairCallPushes (rightReturnPC k.val) (rightAddress0 k)
          (rightAddress1 k) (rightHelperPC k.val) (rightRotation0 k)
          (rightRotation1 k)).length ≤ Artifact.instructions.length := by
  change 1260 + 8 * k.val + 6 ≤ Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  omega

private theorem rightCall_wellFormed (k : Fin 40) :
    ∀ instruction ∈
        PairCallTrace.pairCallPushes (rightReturnPC k.val) (rightAddress0 k)
          (rightAddress1 k) (rightHelperPC k.val) (rightRotation0 k)
          (rightRotation1 k),
      Stepper.WellFormed .Osaka instruction := by
  intro instruction hmem
  apply StackRoundData.templateWellFormed_mem (rightWrapper_wellFormed k)
  change instruction ∈
    PairCallTrace.pairCallPushes (rightReturnPC k.val) (rightAddress0 k)
      (rightAddress1 k) (rightHelperPC k.val) (rightRotation0 k)
      (rightRotation1 k) ++ [op .JUMP, op .JUMPDEST]
  exact List.mem_append_left _ hmem

def rightCallPushes (k : Fin 40) :
    GenericRoundSite Artifact .Osaka
      (PairCallTrace.pairCallPushes (rightReturnPC k.val) (rightAddress0 k)
        (rightAddress1 k) (rightHelperPC k.val) (rightRotation0 k)
        (rightRotation1 k)) :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact) (fork := .Osaka)
    (PairCallTrace.pairCallPushes (rightReturnPC k.val) (rightAddress0 k)
      (rightAddress1 k) (rightHelperPC k.val) (rightRotation0 k)
      (rightRotation1 k))
    (rightWrapperIndex k.val) (rightCall_slice k) (rightCall_fits k)
    StackRoundData.artifact_code_bound (rightCall_wellFormed k)
    (by simp [PairCallTrace.pairCallPushes, PairRoundState.pairCallPushes])

def rightCallJump (k : Fin 40) : LocatedSite Artifact .Osaka where
  located :=
    { index := rightWrapperIndex k.val + 6
      instruction := .op .JUMP
      atIndex := by
        simpa [rightWrapperTemplate, pairWrapperTemplate,
          PairRoundState.pairCallPushes, PairCallTrace.pairCallPushes, op] using
          rightWrapperAt k 6 (by
            simp [rightWrapperTemplate, pairWrapperTemplate,
              PairRoundState.pairCallPushes])
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := rightJumpPC k.val
  pc_eq := pc_toNat_instructionPC _

private theorem rightCallPushes_end_eq (k : Fin 40) :
    (rightCallJump k).pc = (rightCallPushes k).endPC := by
  have hend := StackRoundTrace.endPC_eq_pcAfter_sites
    (rightCallPushes k).sites (rightCallPushes k).startPC
    (rightCallPushes k).endPC (rightCallPushes k).head_eq
    (rightCallPushes k).end_eq (rightCallPushes k).contiguous
  rw [(rightCallPushes k).instruction_eq] at hend
  have hstart : (rightCallPushes k).startPC = rightPC k.val := by
    rfl
  rw [hstart] at hend
  calc
    (rightCallJump k).pc = rightJumpPC k.val := by simp [rightCallJump]
    _ = StackRoundTrace.pcAfter (rightPC k.val)
        (PairCallTrace.pairCallPushes (rightReturnPC k.val) (rightAddress0 k)
          (rightAddress1 k) (rightHelperPC k.val) (rightRotation0 k)
          (rightRotation1 k)) := by
      fin_cases k <;> rfl
    _ = (rightCallPushes k).endPC := hend.symm

def rightReturnSite (k : Fin 40) : LocatedSite Artifact .Osaka where
  located :=
    { index := rightWrapperIndex k.val + 7
      instruction := .op .JUMPDEST
      atIndex := by
        simpa [rightWrapperTemplate, pairWrapperTemplate,
          PairRoundState.pairCallPushes, PairCallTrace.pairCallPushes, op] using
          rightWrapperAt k 7 (by
            simp [rightWrapperTemplate, pairWrapperTemplate,
              PairRoundState.pairCallPushes])
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := rightReturnPC k.val
  pc_eq := pc_toNat_instructionPC _

def rightCallSite (k : Fin 40) :
    PairCallTrace.CallSite Artifact .Osaka
      (rightReturnPC k.val) (rightAddress0 k) (rightAddress1 k)
      (rightHelperPC k.val) (rightRotation0 k) (rightRotation1 k) where
  pushes := rightCallPushes k
  jump := rightCallJump k
  jump_instr := by simp [rightCallJump]
  jump_pc := rightCallPushes_end_eq k

theorem rightCallSite_start (k : Fin 40) :
    (rightCallSite k).pushes.startPC = rightPC k.val := by
  rfl

theorem rightReturnSite_at (k : Fin 40) :
    (rightReturnSite k).pc = rightReturnPC k.val := by
  simp [rightReturnSite]

theorem rightReturnSite_succ_next (k : Fin 40) :
    (rightReturnSite k).pc.succ = rightPC (k.val + 1) := by
  fin_cases k <;> decide

private theorem rightHelper_slice (group : Fin 5) :
    (Artifact.instructions.drop (rightHelperStartIndex group.val)).take
        (rightHelperTemplate group).length = rightHelperTemplate group := by
  fin_cases group <;> rfl

private theorem rightHelper_fits (group : Fin 5) :
    rightHelperStartIndex group.val + (rightHelperTemplate group).length ≤
      Artifact.instructions.length := by
  change rightHelperStartIndex group.val +
      (pairBeforeJumpTemplate (4 - group.val)
        (StackRoundData.rightConstant (16 * group.val))).length ≤
      Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  fin_cases group <;> decide

private theorem rightHelper_wellFormed (group : Fin 5) :
    StackRoundData.TemplateWellFormed (rightHelperTemplate group) := by
  fin_cases group <;> decide

def rightHelperSite (group : Fin 5) :
    GenericRoundSite Artifact .Osaka (rightHelperTemplate group) :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact) (fork := .Osaka) (rightHelperTemplate group)
    (rightHelperStartIndex group.val) (rightHelper_slice group) (rightHelper_fits group)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (rightHelper_wellFormed group))
    (by
      change pairBeforeJumpTemplate (4 - group.val)
        (StackRoundData.rightConstant (16 * group.val)) ≠ []
      fin_cases group <;> decide)

theorem rightHelperSite_start_eq (group : Fin 5) :
    (rightHelperSite group).startPC = rightHelperPCOfGroup group.val := by
  fin_cases group <;> rfl

theorem rightHelperEndIndex (group : Fin 5) :
    rightHelperStartIndex group.val + (rightHelperTemplate group).length =
      rightHelperJumpIndex group.val := by
  fin_cases group <;> rfl

def rightHelperJump (group : Fin 5) : LocatedSite Artifact .Osaka where
  located :=
    { index := rightHelperJumpIndex group.val
      instruction := .op .JUMP
      atIndex := by fin_cases group <;> rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat (Artifact.instructionPC (rightHelperJumpIndex group.val))
  pc_eq := pc_toNat_instructionPC _

theorem rightHelperSite_end_eq (group : Fin 5) :
    (rightHelperJump group).pc = (rightHelperSite group).endPC := by
  have hend := StackRoundTrace.endPC_eq_pcAfter_sites
    (rightHelperSite group).sites (rightHelperSite group).startPC
    (rightHelperSite group).endPC (rightHelperSite group).head_eq
    (rightHelperSite group).end_eq (rightHelperSite group).contiguous
  rw [(rightHelperSite group).instruction_eq] at hend
  rw [rightHelperSite_start_eq group] at hend
  calc
    (rightHelperJump group).pc =
        UInt256.ofNat (Artifact.instructionPC (rightHelperJumpIndex group.val)) := by
          simp [rightHelperJump]
    _ = StackRoundTrace.pcAfter (rightHelperPCOfGroup group.val)
        (rightHelperTemplate group) := by
          fin_cases group <;> rfl
    _ = (rightHelperSite group).endPC := hend.symm

theorem rightHelper_valid (group : Fin 5) :
    Decode.isValidJumpDest Artifact.code
      (rightHelperPCOfGroup group.val).toNat = true := by
  have hpc : (rightHelperPCOfGroup group.val).toNat =
      Artifact.instructionPC (rightHelperStartIndex group.val) := by
    fin_cases group <;> rfl
  rw [hpc]
  exact Artifact.isValidJumpDest_index (rightHelperStartIndex group.val)
    (by fin_cases group <;> rfl)

theorem rightReturn_valid (k : Fin 40) :
    Decode.isValidJumpDest Artifact.code (rightReturnPC k.val).toNat = true := by
  have hpc : (rightReturnPC k.val).toNat =
      Artifact.instructionPC (rightWrapperIndex k.val + 7) := by
    exact (rightReturnSite k).pc_eq
  rw [hpc]
  exact Artifact.isValidJumpDest_index (rightWrapperIndex k.val + 7)
    (rightReturnSite k).located.atIndex

def rightRoundSite (k : Fin 40) :
    PairHelperTrace.RoundSite Artifact .Osaka
      (4 - k.val / 8) (rightAddress0 k) (rightAddress1 k)
      (rightRotation0 k) (rightRotation1 k) (rightConstant k) where
  returnPC := rightReturnPC k.val
  helperPC := rightHelperPC k.val
  call := rightCallSite k
  helper := castTemplate (rightHelperSite ⟨k.val / 8, by omega⟩) (by rfl)
  helper_start := by
    rw [castTemplate_start]
    exact rightHelperSite_start_eq ⟨k.val / 8, by omega⟩
  helperJump := rightHelperJump ⟨k.val / 8, by omega⟩
  helper_jump_instr := by rfl
  helper_end := by
    rw [castTemplate_end]
    exact rightHelperSite_end_eq ⟨k.val / 8, by omega⟩
  returnSite := rightReturnSite k
  return_instr := by rfl
  return_at := by rfl
  helper_valid := rightHelper_valid ⟨k.val / 8, by omega⟩
  return_valid := rightReturn_valid k

theorem rightRoundSite_start (k : Fin 40) :
    (rightRoundSite k).call.pushes.startPC = rightPC k.val := by
  exact rightCallSite_start k

theorem rightRoundSite_end (k : Fin 40) :
    (rightRoundSite k).returnSite.pc.succ = rightPC (k.val + 1) := by
  exact rightReturnSite_succ_next k

theorem rightRotation0_le32 (k : Fin 40) : rightRotation0 k ≤ 32 := by
  fin_cases k <;> decide

theorem rightRotation1_le32 (k : Fin 40) : rightRotation1 k ≤ 32 := by
  fin_cases k <;> decide

@[simp] theorem rightPC_zero : rightPC 0 = UInt256.ofNat 0x812 := by rfl

@[simp] theorem rightPC_end : rightPC 40 = UInt256.ofNat 0xae2 := by rfl

@[simp] theorem rightStartPC_eq : rightStartPC = UInt256.ofNat 0x812 := by rfl

@[simp] theorem rightEndPC_eq : rightEndPC = UInt256.ofNat 0xae2 := by rfl

theorem rightPC_succ (k : Fin 40) :
    rightPC (k.val + 1) = rightPC k.val + UInt256.ofNat 18 := by
  fin_cases k <;> rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairSites
