import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputDigest

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestA

open KnownInputDigest

theorem step1 : CompressionCorrect.normalizedCompress H0 allA = H1 := by decide
theorem step2 : CompressionCorrect.normalizedCompress H1 allA = H2 := by decide
theorem step3 : CompressionCorrect.normalizedCompress H2 allA = H3 := by decide
theorem step4 : CompressionCorrect.normalizedCompress H3 allA = H4 := by decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestA
