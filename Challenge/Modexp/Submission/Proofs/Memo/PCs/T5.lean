import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc5 (i : Nat) (hlo : 1152 ≤ i) (hhi : i ≤ 1186) :
    Artifact.submissionArtifact.instructionPC i =
      [1693,1694,1695,1696,1697,1700,1701,1702,1705,1706,1707,1709,1711,1712,1713,1715,1716,1717,1718,1720,1722,1723,1724,1725,1727,1729,1730,1731,1732,1765,1767,1768,1769,1770,1803][i - 1152]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
