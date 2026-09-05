import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestStates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionSeamBridge

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestSteps

open EvmSemantics.Crypto KnownInputDigest KnownDigestStates

theorem step12 : Ripemd160.compressBlock (knownAt 12)
    (Padding.paddedMessage KnownInputData.targetInput) 768 = knownAt 13 := by
  change Ripemd160.compressBlock H12
    (Padding.paddedMessage KnownInputData.targetInput) 768 = H13
  rw [KnownDigestStates.paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H12 _ _ 768 (by
    rw [KnownInputData.targetInput_size]; omega),
    compress_allA H12 768 (by omega), KnownDigestD.step13]

theorem step13 : Ripemd160.compressBlock (knownAt 13)
    (Padding.paddedMessage KnownInputData.targetInput) 832 = knownAt 14 := by
  change Ripemd160.compressBlock H13
    (Padding.paddedMessage KnownInputData.targetInput) 832 = H14
  rw [KnownDigestStates.paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H13 _ _ 832 (by
    rw [KnownInputData.targetInput_size]; omega),
    compress_allA H13 832 (by omega), KnownDigestD.step14]

theorem step14 : Ripemd160.compressBlock (knownAt 14)
    (Padding.paddedMessage KnownInputData.targetInput) 896 = knownAt 15 := by
  change Ripemd160.compressBlock H14
    (Padding.paddedMessage KnownInputData.targetInput) 896 = H15
  rw [KnownDigestStates.paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H14 _ _ 896 (by
    rw [KnownInputData.targetInput_size]; omega),
    compress_allA H14 896 (by omega), KnownDigestD.step15]

theorem step15 : Ripemd160.compressBlock (knownAt 15)
    (Padding.paddedMessage KnownInputData.targetInput) 960 = knownAt 16 := by
  change Ripemd160.compressBlock H15
    (Padding.paddedMessage KnownInputData.targetInput) 960 = H16
  rw [HashSpecBridge.paddedMessage_eq_prefix_tail]
  have hprefix : (HashSpecBridge.fullPrefix KnownInputData.targetInput).size = 960 := by
    simp [KnownInputData.targetInput_size]
  have hright := HashSpecBridge.compressBlock_append_right H15
    (HashSpecBridge.fullPrefix KnownInputData.targetInput)
    (HashSpecBridge.canonicalTail KnownInputData.targetInput) 0
  rw [hprefix] at hright
  norm_num at hright
  rw [hright, KnownInputDigest.canonicalTail_target,
    KnownInputDigest.compress_final, KnownDigestD.step16]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestSteps
