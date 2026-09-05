import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc9 (i : Nat) (hlo : 1292 ≤ i) (hhi : i ≤ 1326) :
    Artifact.submissionArtifact.instructionPC i =
      [2104,2106,2107,2108,2109,2142,2144,2145,2146,2147,2180,2182,2183,2184,2185,2216,2218,2219,2220,2221,2222,2225,2226,2227,2230,2231,2232,2265,2267,2268,2270,2272,2273,2274,2276][i - 1292]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
