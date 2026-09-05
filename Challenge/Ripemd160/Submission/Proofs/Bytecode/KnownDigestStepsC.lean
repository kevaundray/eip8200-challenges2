import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestStates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionSeamBridge

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestSteps

open EvmSemantics.Crypto KnownInputDigest KnownDigestStates

theorem step8 : Ripemd160.compressBlock (knownAt 8)
    (Padding.paddedMessage KnownInputData.targetInput) 512 = knownAt 9 := by
  change Ripemd160.compressBlock H8
    (Padding.paddedMessage KnownInputData.targetInput) 512 = H9
  rw [KnownDigestStates.paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H8 _ _ 512 (by
    rw [KnownInputData.targetInput_size]; omega),
    compress_allA H8 512 (by omega), KnownDigestC.step9]

theorem step9 : Ripemd160.compressBlock (knownAt 9)
    (Padding.paddedMessage KnownInputData.targetInput) 576 = knownAt 10 := by
  change Ripemd160.compressBlock H9
    (Padding.paddedMessage KnownInputData.targetInput) 576 = H10
  rw [KnownDigestStates.paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H9 _ _ 576 (by
    rw [KnownInputData.targetInput_size]; omega),
    compress_allA H9 576 (by omega), KnownDigestC.step10]

theorem step10 : Ripemd160.compressBlock (knownAt 10)
    (Padding.paddedMessage KnownInputData.targetInput) 640 = knownAt 11 := by
  change Ripemd160.compressBlock H10
    (Padding.paddedMessage KnownInputData.targetInput) 640 = H11
  rw [KnownDigestStates.paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H10 _ _ 640 (by
    rw [KnownInputData.targetInput_size]; omega),
    compress_allA H10 640 (by omega), KnownDigestC.step11]

theorem step11 : Ripemd160.compressBlock (knownAt 11)
    (Padding.paddedMessage KnownInputData.targetInput) 704 = knownAt 12 := by
  change Ripemd160.compressBlock H11
    (Padding.paddedMessage KnownInputData.targetInput) 704 = H12
  rw [KnownDigestStates.paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H11 _ _ 704 (by
    rw [KnownInputData.targetInput_size]; omega),
    compress_allA H11 704 (by omega), KnownDigestC.step12]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestSteps
