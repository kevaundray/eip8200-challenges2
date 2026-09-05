import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestB

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestC

open KnownInputDigest

theorem step9 : CompressionCorrect.normalizedCompress H8 allA = H9 := by decide
theorem step10 : CompressionCorrect.normalizedCompress H9 allA = H10 := by decide
theorem step11 : CompressionCorrect.normalizedCompress H10 allA = H11 := by decide
theorem step12 : CompressionCorrect.normalizedCompress H11 allA = H12 := by decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestC
