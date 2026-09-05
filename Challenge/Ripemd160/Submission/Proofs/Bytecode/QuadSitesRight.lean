import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSitesBase
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCallTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

private theorem rightWrapper_slice (k : Fin 20) :
    (Artifact.instructions.drop (rightWrapperIndex k.val)).take
        (rightWrapperTemplate k).length = rightWrapperTemplate k := by
  fin_cases k <;> rfl

private theorem rightWrapper_fits (k : Fin 20) :
    rightWrapperIndex k.val + (rightWrapperTemplate k).length ≤
      Artifact.instructions.length := by
  change 1182 + 12 * k.val + 12 ≤ Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  omega

private theorem rightWrapper_wellFormed (k : Fin 20) :
    StackRoundData.TemplateWellFormed (rightWrapperTemplate k) := by
  fin_cases k <;> decide

def rightWrapperSite (k : Fin 20) :
    GenericRoundSite Artifact .Osaka (rightWrapperTemplate k) :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact) (fork := .Osaka) (rightWrapperTemplate k)
    (rightWrapperIndex k.val) (rightWrapper_slice k) (rightWrapper_fits k)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (rightWrapper_wellFormed k))
    (by simp [rightWrapperTemplate, quadWrapperTemplate,
      QuadCallTrace.quadCallPushes])

private theorem rightWrapperAt (k : Fin 20) (offset : Nat)
    (hoffset : offset < (rightWrapperTemplate k).length) :
    Artifact.instructions[rightWrapperIndex k.val + offset]? =
      some (rightWrapperTemplate k)[offset] :=
  getElem_of_slice _ _ (rightWrapper_slice k) _ hoffset

private theorem rightCall_slice (k : Fin 20) :
    (Artifact.instructions.drop (rightWrapperIndex k.val)).take
        (QuadCallTrace.quadCallPushes (rightReturnPC k.val)
          (rightAddress0 k) (rightAddress1 k) (rightAddress2 k)
          (rightAddress3 k) (rightHelperPC k.val) (rightRotation0 k)
          (rightRotation1 k) (rightRotation2 k) (rightRotation3 k)).length =
      QuadCallTrace.quadCallPushes (rightReturnPC k.val)
        (rightAddress0 k) (rightAddress1 k) (rightAddress2 k) (rightAddress3 k)
        (rightHelperPC k.val) (rightRotation0 k) (rightRotation1 k)
        (rightRotation2 k) (rightRotation3 k) := by
  have h := congrArg (fun xs : List Instr => xs.take 10)
    (rightWrapper_slice k)
  simpa [rightWrapperTemplate, quadWrapperTemplate,
    QuadCallTrace.quadCallPushes, List.take_take] using h

private theorem rightCall_fits (k : Fin 20) :
    rightWrapperIndex k.val +
        (QuadCallTrace.quadCallPushes (rightReturnPC k.val)
          (rightAddress0 k) (rightAddress1 k) (rightAddress2 k)
          (rightAddress3 k) (rightHelperPC k.val) (rightRotation0 k)
          (rightRotation1 k) (rightRotation2 k) (rightRotation3 k)).length ≤
      Artifact.instructions.length := by
  change 1182 + 12 * k.val + 10 ≤ Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  omega

private theorem rightCall_wellFormed (k : Fin 20) :
    ∀ instruction ∈
        QuadCallTrace.quadCallPushes (rightReturnPC k.val)
          (rightAddress0 k) (rightAddress1 k) (rightAddress2 k)
          (rightAddress3 k) (rightHelperPC k.val) (rightRotation0 k)
          (rightRotation1 k) (rightRotation2 k) (rightRotation3 k),
      Stepper.WellFormed .Osaka instruction := by
  intro instruction hmem
  apply StackRoundData.templateWellFormed_mem (rightWrapper_wellFormed k)
  change instruction ∈
    QuadCallTrace.quadCallPushes (rightReturnPC k.val)
      (rightAddress0 k) (rightAddress1 k) (rightAddress2 k) (rightAddress3 k)
      (rightHelperPC k.val) (rightRotation0 k) (rightRotation1 k)
      (rightRotation2 k) (rightRotation3 k) ++ [op .JUMP, op .JUMPDEST]
  exact List.mem_append_left _ hmem

def rightCallPushes (k : Fin 20) :
    GenericRoundSite Artifact .Osaka
      (QuadCallTrace.quadCallPushes (rightReturnPC k.val)
        (rightAddress0 k) (rightAddress1 k) (rightAddress2 k) (rightAddress3 k)
        (rightHelperPC k.val) (rightRotation0 k) (rightRotation1 k)
        (rightRotation2 k) (rightRotation3 k)) :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact) (fork := .Osaka)
    (QuadCallTrace.quadCallPushes (rightReturnPC k.val)
      (rightAddress0 k) (rightAddress1 k) (rightAddress2 k) (rightAddress3 k)
      (rightHelperPC k.val) (rightRotation0 k) (rightRotation1 k)
      (rightRotation2 k) (rightRotation3 k))
    (rightWrapperIndex k.val) (rightCall_slice k) (rightCall_fits k)
    QuadLayout.code_bound (rightCall_wellFormed k)
    (by simp [QuadCallTrace.quadCallPushes])

def rightCallJump (k : Fin 20) : LocatedSite Artifact .Osaka where
  located :=
    { index := rightWrapperIndex k.val + 10
      instruction := .op .JUMP
      atIndex := by
        simpa [rightWrapperTemplate, quadWrapperTemplate,
          QuadCallTrace.quadCallPushes, op] using
          rightWrapperAt k 10 (by
            simp [rightWrapperTemplate, quadWrapperTemplate,
              QuadCallTrace.quadCallPushes])
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := rightJumpPC k.val
  pc_eq := pc_toNat_instructionPC _

private theorem rightCallPushes_end_eq (k : Fin 20) :
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
        (QuadCallTrace.quadCallPushes (rightReturnPC k.val)
          (rightAddress0 k) (rightAddress1 k) (rightAddress2 k)
          (rightAddress3 k) (rightHelperPC k.val) (rightRotation0 k)
          (rightRotation1 k) (rightRotation2 k) (rightRotation3 k)) := by
      fin_cases k <;> rfl
    _ = (rightCallPushes k).endPC := hend.symm

def rightReturnSite (k : Fin 20) : LocatedSite Artifact .Osaka where
  located :=
    { index := rightWrapperIndex k.val + 11
      instruction := .op .JUMPDEST
      atIndex := by
        simpa [rightWrapperTemplate, quadWrapperTemplate,
          QuadCallTrace.quadCallPushes, op] using
          rightWrapperAt k 11 (by
            simp [rightWrapperTemplate, quadWrapperTemplate,
              QuadCallTrace.quadCallPushes])
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := rightReturnPC k.val
  pc_eq := pc_toNat_instructionPC _

def rightCallSite (k : Fin 20) :
    QuadCallTrace.CallSite Artifact .Osaka
      (rightReturnPC k.val) (rightAddress0 k) (rightAddress1 k)
      (rightAddress2 k) (rightAddress3 k) (rightHelperPC k.val)
      (rightRotation0 k) (rightRotation1 k) (rightRotation2 k)
      (rightRotation3 k) where
  pushes := rightCallPushes k
  jump := rightCallJump k
  jump_instr := by simp [rightCallJump]
  jump_pc := rightCallPushes_end_eq k

theorem rightCallSite_start (k : Fin 20) :
    (rightCallSite k).pushes.startPC = rightPC k.val := by
  rfl

theorem rightReturnSite_at (k : Fin 20) :
    (rightReturnSite k).pc = rightReturnPC k.val := by
  simp [rightReturnSite]

theorem rightReturnSite_succ_next (k : Fin 20) :
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
      (QuadRoundState.quadBeforeJumpTemplate (4 - group.val)
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
    (rightHelperStartIndex group.val) (rightHelper_slice group)
    (rightHelper_fits group) QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (rightHelper_wellFormed group))
    (by
      change QuadRoundState.quadBeforeJumpTemplate (4 - group.val)
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

theorem rightReturn_valid (k : Fin 20) :
    Decode.isValidJumpDest Artifact.code (rightReturnPC k.val).toNat = true := by
  have hpc : (rightReturnPC k.val).toNat =
      Artifact.instructionPC (rightWrapperIndex k.val + 11) := by
    exact (rightReturnSite k).pc_eq
  rw [hpc]
  exact Artifact.isValidJumpDest_index (rightWrapperIndex k.val + 11)
    (rightReturnSite k).located.atIndex

def rightRoundSite (k : Fin 20) :
    QuadHelperTrace.RoundSite Artifact .Osaka
      (4 - k.val / 4) (rightAddress0 k) (rightAddress1 k)
      (rightAddress2 k) (rightAddress3 k)
      (rightRotation0 k) (rightRotation1 k) (rightRotation2 k)
      (rightRotation3 k) (rightConstant k) where
  returnPC := rightReturnPC k.val
  helperPC := rightHelperPC k.val
  call := rightCallSite k
  helper := castTemplate (rightHelperSite ⟨k.val / 4, by omega⟩) (by rfl)
  helper_start := by
    rw [castTemplate_start]
    exact rightHelperSite_start_eq ⟨k.val / 4, by omega⟩
  helperJump := rightHelperJump ⟨k.val / 4, by omega⟩
  helper_jump_instr := by rfl
  helper_end := by
    rw [castTemplate_end]
    exact rightHelperSite_end_eq ⟨k.val / 4, by omega⟩
  returnSite := rightReturnSite k
  return_instr := by rfl
  return_at := by rfl
  helper_valid := rightHelper_valid ⟨k.val / 4, by omega⟩
  return_valid := rightReturn_valid k

theorem rightRoundSite_start (k : Fin 20) :
    (rightRoundSite k).call.pushes.startPC = rightPC k.val := by
  exact rightCallSite_start k

theorem rightRoundSite_end (k : Fin 20) :
    (rightRoundSite k).returnSite.pc.succ = rightPC (k.val + 1) := by
  exact rightReturnSite_succ_next k

theorem rightRotation0_le32 (k : Fin 20) :
    rightRotation0 k ≤ 32 := by
  fin_cases k <;> decide

theorem rightRotation1_le32 (k : Fin 20) :
    rightRotation1 k ≤ 32 := by
  fin_cases k <;> decide

theorem rightRotation2_le32 (k : Fin 20) :
    rightRotation2 k ≤ 32 := by
  fin_cases k <;> decide

theorem rightRotation3_le32 (k : Fin 20) :
    rightRotation3 k ≤ 32 := by
  fin_cases k <;> decide

@[simp] theorem rightPC_zero : rightPC 0 = UInt256.ofNat 0x779 := by
  rfl

@[simp] theorem rightPC_end : rightPC 20 = UInt256.ofNat 0x9a9 := by
  rfl

@[simp] theorem rightStartPC_eq : rightStartPC = UInt256.ofNat 0x779 := by
  rfl

@[simp] theorem rightEndPC_eq : rightEndPC = UInt256.ofNat 0x9a9 := by
  rfl

theorem rightPC_succ (k : Fin 20) :
    rightPC (k.val + 1) = rightPC k.val + UInt256.ofNat 28 := by
  fin_cases k <;> rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites
