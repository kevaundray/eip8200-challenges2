import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackPC
open YulEvmCompiler Challenge.EvmProof

/-- Instruction widths suffice to calculate a PC; push values are irrelevant. -/
def byteLength : List Instr → Nat
  | [] => 0
  | .op _ :: rest => 1 + byteLength rest
  | .push width _ :: rest => (1 + width.val) + byteLength rest

theorem byteLength_eq_assemble (instructions : List Instr) :
    byteLength instructions = (assembleBytes instructions).length := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction <;> simp [byteLength, assembleBytes_cons, ih, Nat.add_comm]

theorem instructionPC_eq_byteLength (artifact : ProgramArtifact) (index : Nat) :
    artifact.instructionPC index = byteLength (artifact.instructions.take index) :=
  (byteLength_eq_assemble _).symm

theorem tailPC : Artifact.submissionArtifact.instructionPC 1580 = 0xa84 := by
  rw [instructionPC_eq_byteLength]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackPC
