import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc2 (i : Nat) (hlo : 1047 ≤ i) (hhi : i ≤ 1081) :
    Artifact.submissionArtifact.instructionPC i =
      [1423,1424,1425,1426,1428,1430,1431,1432,1433,1466,1468,1469,1470,1471,1472,1475,1476,1477,1480,1481,1482,1484,1485,1486,1488,1490,1491,1492,1494,1495,1496,1497,1498,1500,1501][i - 1047]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
