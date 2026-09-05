import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestStates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionSeamBridge

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestSteps

open EvmSemantics.Crypto KnownInputDigest KnownDigestStates

theorem step0 : Ripemd160.compressBlock (knownAt 0)
    (Padding.paddedMessage KnownInputData.targetInput) 0 = knownAt 1 := by
  change Ripemd160.compressBlock H0
    (Padding.paddedMessage KnownInputData.targetInput) 0 = H1
  rw [KnownDigestStates.paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H0 _ _ 0 (by
    rw [KnownInputData.targetInput_size]; omega),
    compress_allA H0 0 (by omega), KnownDigestA.step1]

theorem step1 : Ripemd160.compressBlock (knownAt 1)
    (Padding.paddedMessage KnownInputData.targetInput) 64 = knownAt 2 := by
  change Ripemd160.compressBlock H1
    (Padding.paddedMessage KnownInputData.targetInput) 64 = H2
  rw [KnownDigestStates.paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H1 _ _ 64 (by
    rw [KnownInputData.targetInput_size]; omega),
    compress_allA H1 64 (by omega), KnownDigestA.step2]

theorem step2 : Ripemd160.compressBlock (knownAt 2)
    (Padding.paddedMessage KnownInputData.targetInput) 128 = knownAt 3 := by
  change Ripemd160.compressBlock H2
    (Padding.paddedMessage KnownInputData.targetInput) 128 = H3
  rw [KnownDigestStates.paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H2 _ _ 128 (by
    rw [KnownInputData.targetInput_size]; omega),
    compress_allA H2 128 (by omega), KnownDigestA.step3]

theorem step3 : Ripemd160.compressBlock (knownAt 3)
    (Padding.paddedMessage KnownInputData.targetInput) 192 = knownAt 4 := by
  change Ripemd160.compressBlock H3
    (Padding.paddedMessage KnownInputData.targetInput) 192 = H4
  rw [KnownDigestStates.paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H3 _ _ 192 (by
    rw [KnownInputData.targetInput_size]; omega),
    compress_allA H3 192 (by omega), KnownDigestA.step4]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestSteps
