import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc15 (i : Nat) (hlo : 1502 ≤ i) (hhi : i ≤ 1536) :
    Artifact.submissionArtifact.instructionPC i =
      [3181,3183,3184,3185,3186,3219,3221,3222,3223,3224,3257,3259,3260,3261,3262,3295,3297,3298,3299,3300,3333,3335,3336,3337,3338,3371,3373,3374,3375,3376,3409,3412,3413,3414,3415][i - 1502]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
