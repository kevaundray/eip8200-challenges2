import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc12 (i : Nat) (hlo : 1397 ≤ i) (hhi : i ≤ 1431) :
    Artifact.submissionArtifact.instructionPC i =
      [2591,2594,2595,2596,2599,2600,2601,2634,2635,2636,2638,2639,2640,2641,2643,2644,2645,2646,2648,2650,2651,2652,2653,2655,2657,2658,2659,2660,2693,2695,2696,2697,2698,2731,2733][i - 1397]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
