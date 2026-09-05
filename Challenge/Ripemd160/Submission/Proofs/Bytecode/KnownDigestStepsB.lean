import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestStates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionSeamBridge

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestSteps

open EvmSemantics.Crypto KnownInputDigest KnownDigestStates

theorem step4 : Ripemd160.compressBlock (knownAt 4)
    (Padding.paddedMessage KnownInputData.targetInput) 256 = knownAt 5 := by
  change Ripemd160.compressBlock H4
    (Padding.paddedMessage KnownInputData.targetInput) 256 = H5
  rw [KnownDigestStates.paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H4 _ _ 256 (by
    rw [KnownInputData.targetInput_size]; omega),
    compress_allA H4 256 (by omega), KnownDigestB.step5]

theorem step5 : Ripemd160.compressBlock (knownAt 5)
    (Padding.paddedMessage KnownInputData.targetInput) 320 = knownAt 6 := by
  change Ripemd160.compressBlock H5
    (Padding.paddedMessage KnownInputData.targetInput) 320 = H6
  rw [KnownDigestStates.paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H5 _ _ 320 (by
    rw [KnownInputData.targetInput_size]; omega),
    compress_allA H5 320 (by omega), KnownDigestB.step6]

theorem step6 : Ripemd160.compressBlock (knownAt 6)
    (Padding.paddedMessage KnownInputData.targetInput) 384 = knownAt 7 := by
  change Ripemd160.compressBlock H6
    (Padding.paddedMessage KnownInputData.targetInput) 384 = H7
  rw [KnownDigestStates.paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H6 _ _ 384 (by
    rw [KnownInputData.targetInput_size]; omega),
    compress_allA H6 384 (by omega), KnownDigestB.step7]

theorem step7 : Ripemd160.compressBlock (knownAt 7)
    (Padding.paddedMessage KnownInputData.targetInput) 448 = knownAt 8 := by
  change Ripemd160.compressBlock H7
    (Padding.paddedMessage KnownInputData.targetInput) 448 = H8
  rw [KnownDigestStates.paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H7 _ _ 448 (by
    rw [KnownInputData.targetInput_size]; omega),
    compress_allA H7 448 (by omega), KnownDigestB.step8]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestSteps
