import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc4 (i : Nat) (hlo : 1117 ≤ i) (hhi : i ≤ 1151) :
    Artifact.submissionArtifact.instructionPC i =
      [1583,1584,1585,1586,1619,1621,1622,1623,1624,1625,1628,1629,1630,1633,1634,1635,1636,1637,1638,1639,1641,1642,1643,1644,1646,1648,1649,1650,1651,1653,1655,1656,1657,1658,1691][i - 1117]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
