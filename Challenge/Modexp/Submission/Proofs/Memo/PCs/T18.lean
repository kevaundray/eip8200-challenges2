import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc18 (i : Nat) (hlo : 1607 ≤ i) (hhi : i ≤ 1624) :
    Artifact.submissionArtifact.instructionPC i =
      [3962,3995,3997,3998,4031,4033,4034,4067,4069,4070,4103,4105,4106,4139,4141,4142,4145,4146][i - 1607]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
