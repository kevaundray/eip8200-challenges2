import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc10 (i : Nat) (hlo : 1327 ≤ i) (hhi : i ≤ 1361) :
    Artifact.submissionArtifact.instructionPC i =
      [2277,2278,2279,2281,2283,2284,2285,2286,2288,2290,2291,2292,2293,2326,2328,2329,2330,2331,2364,2366,2367,2368,2369,2402,2404,2405,2406,2407,2408,2411,2412,2415,2416,2417,2450][i - 1327]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
