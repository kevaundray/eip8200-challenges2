import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
import Challenge.Modexp.Submission.Proofs.Memo.Logic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! Generic single-instruction lemmas for taken jumps, stated over an arbitrary
state so the per-site proofs only discharge small side conditions. -/

namespace Challenge.Modexp.Submission.Proofs.Memo.Step

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode

theorem runLocated_jump (loc : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka)
    (hins : loc.instruction = .op .JUMP)
    (s : State) (dest : Nat) (rest : List UInt256)
    (hpc : s.pc.toNat = Artifact.submissionArtifact.instructionPC loc.index)
    (hstack : s.stack = UInt256.ofNat dest :: rest) (hlen : rest.length < 1023)
    (hcode : s.executionEnv.code = submissionBytecode) (hdest : dest < 2 ^ 256)
    (hjump : Decode.isValidJumpDest submissionBytecode dest = true) :
    Challenge.EvmProof.Stepper.runLocated loc s =
      some { s with stack := rest, pc := UInt256.ofNat dest } := by
  unfold Challenge.EvmProof.Stepper.runLocated
  rw [if_pos hpc, hins]
  unfold Challenge.EvmProof.Stepper.runInstr
  have hcap : s.stack.length < 1024 := by rw [hstack]; simp; omega
  rw [if_pos hcap]
  simp only [hstack]
  rw [hcode, Logic.toNat_ofNat_self hdest, hjump]
  simp

theorem runLocated_jumpi_taken (loc : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka)
    (hins : loc.instruction = .op .JUMPI)
    (s : State) (dest : Nat) (cond : UInt256) (rest : List UInt256)
    (hpc : s.pc.toNat = Artifact.submissionArtifact.instructionPC loc.index)
    (hstack : s.stack = UInt256.ofNat dest :: cond :: rest) (hlen : rest.length < 1022)
    (hcond : UInt256.isTrue cond)
    (hcode : s.executionEnv.code = submissionBytecode) (hdest : dest < 2 ^ 256)
    (hjump : Decode.isValidJumpDest submissionBytecode dest = true) :
    Challenge.EvmProof.Stepper.runLocated loc s =
      some { s with stack := rest, pc := UInt256.ofNat dest } := by
  unfold Challenge.EvmProof.Stepper.runLocated
  rw [if_pos hpc, hins]
  unfold Challenge.EvmProof.Stepper.runInstr
  have hcap : s.stack.length < 1024 := by rw [hstack]; simp; omega
  rw [if_pos hcap]
  simp only [hstack]
  rw [if_pos hcond, hcode, Logic.toNat_ofNat_self hdest, hjump]
  simp

end Challenge.Modexp.Submission.Proofs.Memo.Step

namespace Challenge.Modexp.Submission.Proofs.Memo.Step

theorem runLocatedBlock_two {artifact : Challenge.EvmProof.ProgramArtifact} {fork : EvmSemantics.Fork}
    (l1 l2 : Challenge.EvmProof.Stepper.Located artifact fork) (s t u : EvmSemantics.EVM.State)
    (h1 : Challenge.EvmProof.Stepper.runLocated l1 s = some t)
    (ht : t.halt = .Running)
    (h2 : Challenge.EvmProof.Stepper.runLocated l2 t = some u) :
    Challenge.EvmProof.Stepper.runLocatedBlock [l1, l2] s = some u := by
  simp [Challenge.EvmProof.Stepper.runLocatedBlock, h1, ht, h2]

end Challenge.Modexp.Submission.Proofs.Memo.Step
