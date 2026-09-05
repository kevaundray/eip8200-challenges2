import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedHelperTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackPC

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedSites

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundData StackRoundTemplate SharedRoundTemplate

private theorem pc_toNat_instructionPC (index : Nat) :
    (UInt256.ofNat (Artifact.submissionArtifact.instructionPC index)).toNat =
      Artifact.submissionArtifact.instructionPC index := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hle := Artifact.submissionArtifact.instructionPC_le_code_size index
  have hcode := artifact_code_bound
  omega

private theorem getElem_of_slice {artifact : Challenge.EvmProof.ProgramArtifact}
    (startIndex : Nat) (template : List Instr)
    (hslice : (artifact.instructions.drop startIndex).take template.length = template)
    (offset : Nat) (hoffset : offset < template.length) :
    artifact.instructions[startIndex + offset]? = some template[offset] := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) hslice
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs.trans (List.getElem?_eq_getElem hoffset)

def leftHelperStartIndex (group : Nat) : Nat :=
  match group with
  | 0 => 2027
  | 1 => 2064
  | 2 => 2105
  | 3 => 2145
  | _ => 2186

def rightHelperStartIndex (group : Nat) : Nat :=
  match group with
  | 0 => 2226
  | 1 => 2266
  | 2 => 2307
  | 3 => 2347
  | _ => 2388

def leftHelperJumpIndex (group : Nat) : Nat :=
  match group with
  | 0 => 2063
  | 1 => 2104
  | 2 => 2144
  | 3 => 2185
  | _ => 2225

def rightHelperJumpIndex (group : Nat) : Nat :=
  match group with
  | 0 => 2265
  | 1 => 2306
  | 2 => 2346
  | 3 => 2387
  | _ => 2424

def leftHelperWholeLength (group : Nat) : Nat :=
  match group with
  | 0 => 37
  | 1 => 41
  | 2 => 40
  | 3 => 41
  | _ => 40

def rightHelperWholeLength (group : Nat) : Nat :=
  match group with
  | 0 => 40
  | 1 => 41
  | 2 => 40
  | 3 => 41
  | _ => 37

theorem leftHelperEndIndex (group : Fin 5) :
    leftHelperStartIndex group.val +
        (helperBeforeJumpTemplate group.val 0 0
          (leftConstant (16 * group.val))).length =
      leftHelperJumpIndex group.val := by
  fin_cases group <;> rfl

theorem rightHelperEndIndex (group : Fin 5) :
    rightHelperStartIndex group.val +
        (helperBeforeJumpTemplate (4 - group.val) 0 0
          (rightConstant (16 * group.val))).length =
      rightHelperJumpIndex group.val := by
  fin_cases group <;> rfl

theorem leftConstant_group (i : Fin 80) :
    leftConstant (16 * (i.val / 16)) = leftConstant i.val := by
  unfold leftConstant
  have h : 16 * (i.val / 16) / 16 = i.val / 16 := by omega
  rw [h]

theorem rightConstant_group (i : Fin 80) :
    rightConstant (16 * (i.val / 16)) = rightConstant i.val := by
  unfold rightConstant
  have h : 16 * (i.val / 16) / 16 = i.val / 16 := by omega
  rw [h]

private theorem leftCallSlice (i : Fin 80) :
    (Artifact.submissionArtifact.instructions.drop (leftStartIndex i.val)).take
        (SharedCallTrace.callPushes (leftReturnPC i.val) (leftAddress i.val)
          (leftHelperPC i.val) (leftRotation i.val)).length =
      SharedCallTrace.callPushes (leftReturnPC i.val) (leftAddress i.val)
        (leftHelperPC i.val) (leftRotation i.val) := by
  have h := congrArg (fun xs : List Instr => xs.take 4)
    (StackSliceCertificates.leftFacts i).slice
  simpa [SharedCallTrace.callPushes, leftTemplate, wrapperTemplate,
    List.take_take] using h

private theorem rightCallSlice (i : Fin 80) :
    (Artifact.submissionArtifact.instructions.drop (rightStartIndex i.val)).take
        (SharedCallTrace.callPushes (rightReturnPC i.val) (rightAddress i.val)
          (rightHelperPC i.val) (rightRotation i.val)).length =
      SharedCallTrace.callPushes (rightReturnPC i.val) (rightAddress i.val)
        (rightHelperPC i.val) (rightRotation i.val) := by
  have h := congrArg (fun xs : List Instr => xs.take 4)
    (StackSliceCertificates.rightFacts i).slice
  simpa [SharedCallTrace.callPushes, rightTemplate, wrapperTemplate,
    List.take_take] using h

private theorem leftCallFits (i : Fin 80) :
    leftStartIndex i.val +
        (SharedCallTrace.callPushes (leftReturnPC i.val) (leftAddress i.val)
          (leftHelperPC i.val) (leftRotation i.val)).length ≤
      Artifact.submissionArtifact.instructions.length := by
  have h := (StackSliceCertificates.leftFacts i).fits
  simp [SharedCallTrace.callPushes] at h ⊢
  omega

private theorem rightCallFits (i : Fin 80) :
    rightStartIndex i.val +
        (SharedCallTrace.callPushes (rightReturnPC i.val) (rightAddress i.val)
          (rightHelperPC i.val) (rightRotation i.val)).length ≤
      Artifact.submissionArtifact.instructions.length := by
  have h := (StackSliceCertificates.rightFacts i).fits
  simp [SharedCallTrace.callPushes] at h ⊢
  omega

private theorem leftCallWellFormed (i : Fin 80) :
    ∀ instruction ∈
        SharedCallTrace.callPushes (leftReturnPC i.val) (leftAddress i.val)
          (leftHelperPC i.val) (leftRotation i.val),
      Challenge.EvmProof.Stepper.WellFormed .Osaka instruction := by
  intro instruction hmem
  apply (templateWellFormed_mem (StackSliceCertificates.leftFacts i).wellFormed)
  change instruction ∈ SharedCallTrace.callPushes (leftReturnPC i.val)
    (leftAddress i.val) (leftHelperPC i.val) (leftRotation i.val) ++
      [op .JUMP, op .JUMPDEST]
  exact List.mem_append_left _ hmem

private theorem rightCallWellFormed (i : Fin 80) :
    ∀ instruction ∈
        SharedCallTrace.callPushes (rightReturnPC i.val) (rightAddress i.val)
          (rightHelperPC i.val) (rightRotation i.val),
      Challenge.EvmProof.Stepper.WellFormed .Osaka instruction := by
  intro instruction hmem
  apply (templateWellFormed_mem (StackSliceCertificates.rightFacts i).wellFormed)
  change instruction ∈ SharedCallTrace.callPushes (rightReturnPC i.val)
    (rightAddress i.val) (rightHelperPC i.val) (rightRotation i.val) ++
      [op .JUMP, op .JUMPDEST]
  exact List.mem_append_left _ hmem

private theorem leftWrapperAt (i : Fin 80) (offset : Nat) (hoffset : offset < 6) :
    Artifact.submissionArtifact.instructions[leftStartIndex i.val + offset]? =
      some (leftTemplate i.val)[offset] := by
  exact getElem_of_slice (leftStartIndex i.val) (leftTemplate i.val)
    (StackSliceCertificates.leftFacts i).slice offset (by simpa using hoffset)

private theorem rightWrapperAt (i : Fin 80) (offset : Nat) (hoffset : offset < 6) :
    Artifact.submissionArtifact.instructions[rightStartIndex i.val + offset]? =
      some (rightTemplate i.val)[offset] := by
  exact getElem_of_slice (rightStartIndex i.val) (rightTemplate i.val)
    (StackSliceCertificates.rightFacts i).slice offset (by simpa using hoffset)

def leftCallPushes (i : Fin 80) :
    GenericRoundSite Artifact.submissionArtifact .Osaka
      (SharedCallTrace.callPushes (leftReturnPC i.val) (leftAddress i.val)
        (leftHelperPC i.val) (leftRotation i.val)) :=
  StackSiteBuilder.ofSlice
    (SharedCallTrace.callPushes (leftReturnPC i.val) (leftAddress i.val)
      (leftHelperPC i.val) (leftRotation i.val))
    (leftStartIndex i.val)
    (leftCallSlice i)
    (leftCallFits i)
    artifact_code_bound
    (leftCallWellFormed i)
    (by simp [SharedCallTrace.callPushes])

def rightCallPushes (i : Fin 80) :
    GenericRoundSite Artifact.submissionArtifact .Osaka
      (SharedCallTrace.callPushes (rightReturnPC i.val) (rightAddress i.val)
        (rightHelperPC i.val) (rightRotation i.val)) :=
  StackSiteBuilder.ofSlice
    (SharedCallTrace.callPushes (rightReturnPC i.val) (rightAddress i.val)
      (rightHelperPC i.val) (rightRotation i.val))
    (rightStartIndex i.val)
    (rightCallSlice i)
    (rightCallFits i)
    artifact_code_bound
    (rightCallWellFormed i)
    (by simp [SharedCallTrace.callPushes])

def leftCallJump (i : Fin 80) : LocatedSite Artifact.submissionArtifact .Osaka where
  located :=
    { index := leftStartIndex i.val + 4
      instruction := .op .JUMP
      atIndex := by
        simpa [leftTemplate, wrapperTemplate, StackRoundTemplate.op] using leftWrapperAt i 4 (by decide)
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat
    (Artifact.submissionArtifact.instructionPC (leftStartIndex i.val + 4))
  pc_eq := pc_toNat_instructionPC _

def rightCallJump (i : Fin 80) : LocatedSite Artifact.submissionArtifact .Osaka where
  located :=
    { index := rightStartIndex i.val + 4
      instruction := .op .JUMP
      atIndex := by
        simpa [rightTemplate, wrapperTemplate, StackRoundTemplate.op] using rightWrapperAt i 4 (by decide)
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat
    (Artifact.submissionArtifact.instructionPC (rightStartIndex i.val + 4))
  pc_eq := pc_toNat_instructionPC _

def leftCallSite (i : Fin 80) :
    SharedCallTrace.CallSite Artifact.submissionArtifact .Osaka
      (leftReturnPC i.val) (leftAddress i.val) (leftHelperPC i.val)
      (leftRotation i.val) where
  pushes := leftCallPushes i
  jump := leftCallJump i
  jump_instr := by rfl
  jump_pc := by rfl

def rightCallSite (i : Fin 80) :
    SharedCallTrace.CallSite Artifact.submissionArtifact .Osaka
      (rightReturnPC i.val) (rightAddress i.val) (rightHelperPC i.val)
      (rightRotation i.val) where
  pushes := rightCallPushes i
  jump := rightCallJump i
  jump_instr := by rfl
  jump_pc := by rfl

def leftReturnSite (i : Fin 80) : LocatedSite Artifact.submissionArtifact .Osaka where
  located :=
    { index := leftStartIndex i.val + 5
      instruction := .op .JUMPDEST
      atIndex := by
        simpa [leftTemplate, wrapperTemplate, StackRoundTemplate.op] using leftWrapperAt i 5 (by decide)
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := leftReturnPC i.val
  pc_eq := by
    rw [StackPC.instructionPC_eq_byteLength]
    fin_cases i <;> decide

def rightReturnSite (i : Fin 80) : LocatedSite Artifact.submissionArtifact .Osaka where
  located :=
    { index := rightStartIndex i.val + 5
      instruction := .op .JUMPDEST
      atIndex := by
        simpa [rightTemplate, wrapperTemplate, StackRoundTemplate.op] using rightWrapperAt i 5 (by decide)
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := rightReturnPC i.val
  pc_eq := by
    rw [StackPC.instructionPC_eq_byteLength]
    fin_cases i <;> decide

def leftHelperSite (group : Fin 5) (xAddress : UInt256) (rotation : Nat) :
    GenericRoundSite Artifact.submissionArtifact .Osaka
      (helperBeforeJumpTemplate group.val xAddress rotation
        (leftConstant (16 * group.val))) :=
  StackSiteBuilder.ofSlice
    (helperBeforeJumpTemplate group.val xAddress rotation
      (leftConstant (16 * group.val)))
    (leftHelperStartIndex group.val)
    (by fin_cases group <;> rfl)
    (by
      change leftHelperStartIndex group.val +
        (helperBeforeJumpTemplate group.val 0 0 (leftConstant (16 * group.val))).length ≤
          Artifact.submissionArtifact.instructions.length
      fin_cases group <;> decide)
    artifact_code_bound
    (templateWellFormed_mem (by
      change TemplateWellFormed
        (helperBeforeJumpTemplate group.val 0 0 (leftConstant (16 * group.val)))
      fin_cases group <;> decide))
    (by
      change helperBeforeJumpTemplate group.val 0 0 (leftConstant (16 * group.val)) ≠ []
      fin_cases group <;> decide)

def rightHelperSite (group : Fin 5) (xAddress : UInt256) (rotation : Nat) :
    GenericRoundSite Artifact.submissionArtifact .Osaka
      (helperBeforeJumpTemplate (4 - group.val) xAddress rotation
        (rightConstant (16 * group.val))) :=
  StackSiteBuilder.ofSlice
    (helperBeforeJumpTemplate (4 - group.val) xAddress rotation
      (rightConstant (16 * group.val)))
    (rightHelperStartIndex group.val)
    (by fin_cases group <;> rfl)
    (by
      change rightHelperStartIndex group.val +
        (helperBeforeJumpTemplate (4 - group.val) 0 0 (rightConstant (16 * group.val))).length ≤
          Artifact.submissionArtifact.instructions.length
      fin_cases group <;> decide)
    artifact_code_bound
    (templateWellFormed_mem (by
      change TemplateWellFormed
        (helperBeforeJumpTemplate (4 - group.val) 0 0 (rightConstant (16 * group.val)))
      fin_cases group <;> decide))
    (by
      change helperBeforeJumpTemplate (4 - group.val) 0 0 (rightConstant (16 * group.val)) ≠ []
      fin_cases group <;> decide)

def leftHelperJump (group : Fin 5) : LocatedSite Artifact.submissionArtifact .Osaka where
  located :=
    { index := leftHelperJumpIndex group.val
      instruction := .op .JUMP
      atIndex := by fin_cases group <;> rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat
    (Artifact.submissionArtifact.instructionPC (leftHelperJumpIndex group.val))
  pc_eq := pc_toNat_instructionPC _

def rightHelperJump (group : Fin 5) : LocatedSite Artifact.submissionArtifact .Osaka where
  located :=
    { index := rightHelperJumpIndex group.val
      instruction := .op .JUMP
      atIndex := by fin_cases group <;> rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat
    (Artifact.submissionArtifact.instructionPC (rightHelperJumpIndex group.val))
  pc_eq := pc_toNat_instructionPC _

theorem leftHelperSite_start_eq (group : Fin 5) (xAddress : UInt256)
    (rotation : Nat) :
    (leftHelperSite group xAddress rotation).startPC =
      leftHelperPCOfGroup group.val := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC
    (leftHelperStartIndex group.val)) = _
  rw [StackPC.instructionPC_eq_byteLength]
  fin_cases group <;> decide

theorem rightHelperSite_start_eq (group : Fin 5) (xAddress : UInt256)
    (rotation : Nat) :
    (rightHelperSite group xAddress rotation).startPC =
      rightHelperPCOfGroup group.val := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC
    (rightHelperStartIndex group.val)) = _
  rw [StackPC.instructionPC_eq_byteLength]
  fin_cases group <;> decide

theorem leftHelperSite_end_eq (group : Fin 5) (xAddress : UInt256)
    (rotation : Nat) :
    (leftHelperJump group).pc =
      (leftHelperSite group xAddress rotation).endPC := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC
    (leftHelperJumpIndex group.val)) = UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (leftHelperStartIndex group.val +
        (helperBeforeJumpTemplate group.val 0 0
          (leftConstant (16 * group.val))).length))
  rw [leftHelperEndIndex group]

theorem rightHelperSite_end_eq (group : Fin 5) (xAddress : UInt256)
    (rotation : Nat) :
    (rightHelperJump group).pc =
      (rightHelperSite group xAddress rotation).endPC := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC
    (rightHelperJumpIndex group.val)) = UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (rightHelperStartIndex group.val +
        (helperBeforeJumpTemplate (4 - group.val) 0 0
          (rightConstant (16 * group.val))).length))
  rw [rightHelperEndIndex group]

theorem leftReturnSite_at (i : Fin 80) :
    (leftReturnSite i).pc = leftReturnPC i.val := by
  rfl

theorem rightReturnSite_at (i : Fin 80) :
    (rightReturnSite i).pc = rightReturnPC i.val := by
  rfl

theorem leftCallSite_start_eq (i : Fin 80) :
    (leftCallSite i).pushes.startPC = StackSites.leftPC i.val := by
  rfl

theorem rightCallSite_start_eq (i : Fin 80) :
    (rightCallSite i).pushes.startPC = StackSites.rightPC i.val := by
  rfl

theorem leftReturnSite_succ_next (i : Fin 80) :
    (leftReturnSite i).pc.succ = leftNextPC i.val := by
  fin_cases i <;> decide

theorem rightReturnSite_succ_next (i : Fin 80) :
    (rightReturnSite i).pc.succ = rightNextPC i.val := by
  fin_cases i <;> decide

theorem leftNextPC_eq_stackPC (i : Fin 80) :
    leftNextPC i.val = StackSites.leftPC (i.val + 1) := by
  change leftNextPC i.val = UInt256.ofNat
    (Artifact.submissionArtifact.instructionPC (leftStartIndex (i.val + 1)))
  rw [StackPC.instructionPC_eq_byteLength]
  fin_cases i <;> decide

theorem rightNextPC_eq_stackPC (i : Fin 80) :
    rightNextPC i.val = StackSites.rightPC (i.val + 1) := by
  change rightNextPC i.val = UInt256.ofNat
    (Artifact.submissionArtifact.instructionPC (rightStartIndex (i.val + 1)))
  rw [StackPC.instructionPC_eq_byteLength]
  fin_cases i <;> decide

theorem leftHelper_valid (group : Fin 5) :
    Decode.isValidJumpDest Artifact.submissionArtifact.code
      (leftHelperPCOfGroup group.val).toNat = true := by
  have hpc : (leftHelperPCOfGroup group.val).toNat =
      Artifact.submissionArtifact.instructionPC
        (leftHelperStartIndex group.val) := by
    rw [StackPC.instructionPC_eq_byteLength]
    fin_cases group <;> decide
  rw [hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index
    (leftHelperStartIndex group.val) (by fin_cases group <;> rfl)

theorem rightHelper_valid (group : Fin 5) :
    Decode.isValidJumpDest Artifact.submissionArtifact.code
      (rightHelperPCOfGroup group.val).toNat = true := by
  have hpc : (rightHelperPCOfGroup group.val).toNat =
      Artifact.submissionArtifact.instructionPC
        (rightHelperStartIndex group.val) := by
    rw [StackPC.instructionPC_eq_byteLength]
    fin_cases group <;> decide
  rw [hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index
    (rightHelperStartIndex group.val) (by fin_cases group <;> rfl)

theorem leftReturn_valid (i : Fin 80) :
    Decode.isValidJumpDest Artifact.submissionArtifact.code
      (leftReturnPC i.val).toNat = true := by
  have hpc : (leftReturnPC i.val).toNat =
      Artifact.submissionArtifact.instructionPC (leftStartIndex i.val + 5) :=
    (leftReturnSite i).pc_eq
  rw [hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index
    (leftStartIndex i.val + 5) (leftReturnSite i).located.atIndex

theorem rightReturn_valid (i : Fin 80) :
    Decode.isValidJumpDest Artifact.submissionArtifact.code
      (rightReturnPC i.val).toNat = true := by
  have hpc : (rightReturnPC i.val).toNat =
      Artifact.submissionArtifact.instructionPC (rightStartIndex i.val + 5) :=
    (rightReturnSite i).pc_eq
  rw [hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index
    (rightStartIndex i.val + 5) (rightReturnSite i).located.atIndex

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedSites
