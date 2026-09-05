import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc14 (i : Nat) (hlo : 1467 ≤ i) (hhi : i ≤ 1501) :
    Artifact.submissionArtifact.instructionPC i =
      [3004,3005,3006,3007,3010,3011,3012,3015,3016,3017,3050,3051,3052,3085,3087,3088,3121,3123,3124,3157,3159,3160,3162,3163,3164,3165,3168,3169,3170,3171,3173,3175,3176,3177,3178][i - 1467]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
