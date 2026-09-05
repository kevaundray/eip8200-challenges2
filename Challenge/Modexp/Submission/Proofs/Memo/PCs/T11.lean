import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc11 (i : Nat) (hlo : 1362 ≤ i) (hhi : i ≤ 1396) :
    Artifact.submissionArtifact.instructionPC i =
      [2451,2452,2454,2455,2456,2457,2459,2460,2461,2462,2464,2466,2467,2468,2469,2471,2473,2474,2475,2476,2509,2511,2512,2513,2514,2547,2549,2550,2551,2552,2585,2587,2588,2589,2590][i - 1362]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
