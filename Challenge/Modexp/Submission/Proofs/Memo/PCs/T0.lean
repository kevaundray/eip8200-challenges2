import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc0 (i : Nat) (hlo : 977 ≤ i) (hhi : i ≤ 1011) :
    Artifact.submissionArtifact.instructionPC i =
      [1314,1315,1316,1317,1318,1321,1322,1323,1325,1326,1329,1330,1331,1333,1334,1337,1338,1339,1341,1342,1345,1346,1347,1349,1350,1353,1354,1355,1357,1358,1361,1362,1363,1365,1366][i - 977]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
