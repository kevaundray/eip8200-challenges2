import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTemplate

def template (j : Nat) (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) : List Instr :=
  match j with
  | 0 => f0Template xAddress rotation
  | 1 => f1Template xAddress rotation constant
  | 2 => f2Template xAddress rotation constant
  | 3 => f3Template xAddress rotation constant
  | _ => f4Template xAddress rotation constant

def leftStartIndex (i : Nat) : Nat :=
  996 + 6 * i

def rightStartIndex (i : Nat) : Nat :=
  1486 + 6 * i

def leftWrapperPC (i : Nat) : UInt256 :=
  UInt256.ofNat (0x533 + 13 * i)

def rightWrapperPC (i : Nat) : UInt256 :=
  UInt256.ofNat (0xb5f + 13 * i)

def leftReturnPC (i : Nat) : UInt256 :=
  leftWrapperPC i + UInt256.ofNat 12

def rightReturnPC (i : Nat) : UInt256 :=
  rightWrapperPC i + UInt256.ofNat 12

def leftNextPC (i : Nat) : UInt256 :=
  leftWrapperPC i + UInt256.ofNat 13

def rightNextPC (i : Nat) : UInt256 :=
  rightWrapperPC i + UInt256.ofNat 13

def leftAddress (i : Nat) : UInt256 :=
  UInt256.ofNat (644 + 4 * Crypto.Ripemd160.r[i]!)

def rightAddress (i : Nat) : UInt256 :=
  UInt256.ofNat (644 + 4 * Crypto.Ripemd160.rP[i]!)

def leftRotation (i : Nat) : Nat := Crypto.Ripemd160.s[i]!
def rightRotation (i : Nat) : Nat := Crypto.Ripemd160.sP[i]!

def leftConstant (i : Nat) : UInt256 :=
  Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[i / 16]!)

def rightConstant (i : Nat) : UInt256 :=
  Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[i / 16]!)

def leftHelperPCOfGroup (group : Nat) : UInt256 :=
  match group with
  | 0 => UInt256.ofNat 0xfca
  | 1 => UInt256.ofNat 0xffe
  | 2 => UInt256.ofNat 0xe2d
  | 3 => UInt256.ofNat 0x1075
  | _ => UInt256.ofNat 0x10b1

def rightHelperPCOfGroup (group : Nat) : UInt256 :=
  match group with
  | 0 => UInt256.ofNat 0xedf
  | 1 => UInt256.ofNat 0x1127
  | 2 => UInt256.ofNat 0xf56
  | 3 => UInt256.ofNat 0xf91
  | _ => UInt256.ofNat 0xfcd

def leftHelperPC (i : Nat) : UInt256 :=
  leftHelperPCOfGroup (i / 16)

def rightHelperPC (i : Nat) : UInt256 :=
  rightHelperPCOfGroup (i / 16)

def wrapperTemplate (returnPC xAddress helperPC : UInt256)
    (rotation : Nat) : List Instr :=
  [push1 (UInt256.ofNat (32 - rotation)), push2 returnPC, push2 xAddress,
    push2 helperPC, op .JUMP, op .JUMPDEST]

def leftTemplate (i : Nat) : List Instr :=
  wrapperTemplate (leftReturnPC i) (leftAddress i) (leftHelperPC i) (leftRotation i)

def rightTemplate (i : Nat) : List Instr :=
  wrapperTemplate (rightReturnPC i) (rightAddress i) (rightHelperPC i) (rightRotation i)

@[simp] theorem wrapperTemplate_length (returnPC xAddress helperPC : UInt256)
    (rotation : Nat) :
    (wrapperTemplate returnPC xAddress helperPC rotation).length = 6 := by
  rfl

@[simp] theorem leftTemplate_length (i : Nat) :
    (leftTemplate i).length = 6 := by
  rfl

@[simp] theorem rightTemplate_length (i : Nat) :
    (rightTemplate i).length = 6 := by
  rfl

theorem leftRotation_le_32 (i : Fin 80) : leftRotation i.val ≤ 32 := by
  fin_cases i <;> decide

theorem rightRotation_le_32 (i : Fin 80) : rightRotation i.val ≤ 32 := by
  fin_cases i <;> decide

def TemplateWellFormed (instructions : List Instr) : Prop :=
  ∀ i : Fin instructions.length,
    Challenge.EvmProof.Stepper.WellFormed .Osaka instructions[i]

private def plainDecidable (operation : Operation) : Decidable (plainOp operation) := by
  cases operation <;> dsimp only [plainOp] <;> infer_instance

/-- A transparent decision procedure avoids casts in the general Stepper instance. -/
private def instructionWellFormedDecidable (instruction : Instr) :
    Decidable (Challenge.EvmProof.Stepper.WellFormed .Osaka instruction) :=
  match instruction with
  | .push width value => inferInstanceAs (Decidable
      (value.toNat < 256 ^ width.val ∧
        (Operation.Push ⟨width⟩).availableInFork .Osaka = true))
  | .op operation =>
    letI := plainDecidable operation
    inferInstanceAs (Decidable (Decode.opcodeOf (Instr.opByte operation) = some operation ∧
      plainOp operation ∧ operation.availableInFork .Osaka = true))

instance (instructions : List Instr) : Decidable (TemplateWellFormed instructions) :=
  letI := instructionWellFormedDecidable
  inferInstanceAs (Decidable (∀ i : Fin instructions.length,
    Challenge.EvmProof.Stepper.WellFormed .Osaka instructions[i]))

theorem templateWellFormed_mem {instructions : List Instr}
    (h : TemplateWellFormed instructions) :
    ∀ instruction ∈ instructions, Challenge.EvmProof.Stepper.WellFormed .Osaka instruction := by
  intro instruction hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
  exact h ⟨i, hi⟩

theorem artifact_code_bound : Artifact.submissionArtifact.code.size < 2 ^ 256 := by
  change submissionBytecode.size < 2 ^ 256
  rw [referenceBytecode_size]
  norm_num

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
