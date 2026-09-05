import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc17 (i : Nat) (hlo : 1572 ≤ i) (hhi : i ≤ 1606) :
    Artifact.submissionArtifact.instructionPC i =
      [3721,3724,3725,3726,3727,3760,3763,3764,3765,3766,3799,3802,3803,3804,3805,3838,3841,3842,3843,3844,3845,3848,3849,3850,3853,3854,3855,3888,3889,3890,3923,3925,3926,3959,3961][i - 1572]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
