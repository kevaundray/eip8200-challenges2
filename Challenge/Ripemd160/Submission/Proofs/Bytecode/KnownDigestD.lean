import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestC

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestD

open KnownInputDigest

theorem step13 : CompressionCorrect.normalizedCompress H12 allA = H13 := by decide
theorem step14 : CompressionCorrect.normalizedCompress H13 allA = H14 := by decide
theorem step15 : CompressionCorrect.normalizedCompress H14 allA = H15 := by decide
theorem step16 : CompressionCorrect.normalizedCompress H15 finalWords = H16 := by decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestD
