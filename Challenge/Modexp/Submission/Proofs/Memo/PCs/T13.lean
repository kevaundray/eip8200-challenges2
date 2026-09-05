import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc13 (i : Nat) (hlo : 1432 ≤ i) (hhi : i ≤ 1466) :
    Artifact.submissionArtifact.instructionPC i =
      [2734,2735,2736,2769,2771,2772,2773,2774,2807,2809,2810,2811,2812,2845,2847,2848,2849,2850,2883,2886,2887,2888,2889,2922,2925,2926,2927,2928,2961,2964,2965,2966,2967,3000,3003][i - 1432]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
