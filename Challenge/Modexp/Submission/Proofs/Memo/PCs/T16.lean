import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc16 (i : Nat) (hlo : 1537 ≤ i) (hhi : i ≤ 1571) :
    Artifact.submissionArtifact.instructionPC i =
      [3448,3451,3452,3453,3454,3487,3490,3491,3492,3493,3526,3529,3530,3531,3532,3565,3568,3569,3570,3571,3604,3607,3608,3609,3610,3643,3646,3647,3648,3649,3682,3685,3686,3687,3688][i - 1537]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
