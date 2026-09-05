import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc8 (i : Nat) (hlo : 1257 ≤ i) (hhi : i ≤ 1291) :
    Artifact.submissionArtifact.instructionPC i =
      [1994,1995,2028,2030,2031,2032,2033,2034,2036,2037,2038,2039,2040,2043,2044,2045,2048,2049,2050,2083,2084,2085,2087,2088,2089,2090,2092,2093,2094,2095,2097,2099,2100,2101,2102][i - 1257]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
