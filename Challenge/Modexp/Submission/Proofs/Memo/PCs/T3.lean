import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc3 (i : Nat) (hlo : 1082 ≤ i) (hhi : i ≤ 1116) :
    Artifact.submissionArtifact.instructionPC i =
      [1502,1503,1505,1507,1508,1509,1510,1543,1545,1546,1547,1548,1549,1552,1553,1556,1557,1558,1560,1561,1562,1564,1566,1567,1568,1570,1571,1572,1573,1575,1577,1578,1579,1580,1581][i - 1082]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
