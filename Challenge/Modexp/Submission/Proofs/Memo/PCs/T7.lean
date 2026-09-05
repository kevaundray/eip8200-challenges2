import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc7 (i : Nat) (hlo : 1222 ≤ i) (hhi : i ≤ 1256) :
    Artifact.submissionArtifact.instructionPC i =
      [1883,1884,1917,1919,1920,1921,1922,1955,1957,1958,1959,1960,1961,1964,1965,1966,1969,1970,1971,1973,1974,1975,1976,1978,1979,1980,1981,1983,1985,1986,1987,1988,1990,1992,1993][i - 1222]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
