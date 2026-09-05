import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLeftSlices3
open StackRoundData

theorem slice (i : Fin 16) :
    (Artifact.submissionArtifact.instructions.drop (leftStartIndex (48 + i.val))).take
        (leftTemplate (48 + i.val)).length = leftTemplate (48 + i.val) := by
  fin_cases i <;> rfl

theorem wellFormed (i : Fin 16) :
    TemplateWellFormed (leftTemplate (48 + i.val)) := by
  fin_cases i <;> decide

theorem nextIndex (i : Fin 16) :
    leftStartIndex (48 + i.val) + (leftTemplate (48 + i.val)).length =
      leftStartIndex (48 + i.val + 1) := by
  fin_cases i <;> rfl

theorem nonempty (i : Fin 16) :
    leftTemplate (48 + i.val) ≠ [] := by
  fin_cases i <;> decide

theorem fits (i : Fin 16) :
    leftStartIndex (48 + i.val) + (leftTemplate (48 + i.val)).length ≤
      Artifact.submissionArtifact.instructions.length := by
  fin_cases i <;> decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLeftSlices3

