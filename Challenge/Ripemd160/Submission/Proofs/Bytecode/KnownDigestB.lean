import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestA

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestB

open KnownInputDigest

theorem step5 : CompressionCorrect.normalizedCompress H4 allA = H5 := by decide
theorem step6 : CompressionCorrect.normalizedCompress H5 allA = H6 := by decide
theorem step7 : CompressionCorrect.normalizedCompress H6 allA = H7 := by decide
theorem step8 : CompressionCorrect.normalizedCompress H7 allA = H8 := by decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestB
