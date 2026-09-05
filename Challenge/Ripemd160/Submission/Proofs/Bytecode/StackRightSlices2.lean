import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRightSlices2
open StackRoundData

theorem slice (i : Fin 16) :
    (Artifact.submissionArtifact.instructions.drop (rightStartIndex (32 + i.val))).take
        (rightTemplate (32 + i.val)).length = rightTemplate (32 + i.val) := by
  fin_cases i <;> rfl

theorem wellFormed (i : Fin 16) :
    TemplateWellFormed (rightTemplate (32 + i.val)) := by
  fin_cases i <;> decide

theorem nextIndex (i : Fin 16) :
    rightStartIndex (32 + i.val) + (rightTemplate (32 + i.val)).length =
      rightStartIndex (32 + i.val + 1) := by
  fin_cases i <;> rfl

theorem nonempty (i : Fin 16) :
    rightTemplate (32 + i.val) ≠ [] := by
  fin_cases i <;> decide

theorem fits (i : Fin 16) :
    rightStartIndex (32 + i.val) + (rightTemplate (32 + i.val)).length ≤
      Artifact.submissionArtifact.instructions.length := by
  fin_cases i <;> decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRightSlices2

