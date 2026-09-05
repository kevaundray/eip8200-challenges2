import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc1 (i : Nat) (hlo : 1012 ≤ i) (hhi : i ≤ 1046) :
    Artifact.submissionArtifact.instructionPC i =
      [1369,1370,1371,1373,1374,1377,1378,1379,1381,1382,1385,1386,1387,1390,1391,1394,1395,1396,1399,1400,1403,1404,1405,1408,1409,1410,1411,1412,1413,1414,1416,1417,1418,1419,1421][i - 1012]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
