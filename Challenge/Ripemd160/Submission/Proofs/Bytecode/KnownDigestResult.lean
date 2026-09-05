import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestD
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionSeamBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestStepsA
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestStepsB
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestStepsC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestStepsD

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestResult

open EvmSemantics.Crypto
open KnownInputDigest

/- The standalone whole-hash certificate is not needed by the block-kernel proof.
   The block-by-block certificates below are both stronger for this use and cheaper
   for the trusted kernel to elaborate. -/
/-
private theorem block1 : Ripemd160.compressBlock H0 KnownInputData.targetInput 0 = H1 := by
  rw [compress_allA H0 0 (by omega), KnownDigestA.step1]
private theorem block2 : Ripemd160.compressBlock H1 KnownInputData.targetInput 64 = H2 := by
  rw [compress_allA H1 64 (by omega), KnownDigestA.step2]
private theorem block3 : Ripemd160.compressBlock H2 KnownInputData.targetInput 128 = H3 := by
  rw [compress_allA H2 128 (by omega), KnownDigestA.step3]
private theorem block4 : Ripemd160.compressBlock H3 KnownInputData.targetInput 192 = H4 := by
  rw [compress_allA H3 192 (by omega), KnownDigestA.step4]
private theorem block5 : Ripemd160.compressBlock H4 KnownInputData.targetInput 256 = H5 := by
  rw [compress_allA H4 256 (by omega), KnownDigestB.step5]
private theorem block6 : Ripemd160.compressBlock H5 KnownInputData.targetInput 320 = H6 := by
  rw [compress_allA H5 320 (by omega), KnownDigestB.step6]
private theorem block7 : Ripemd160.compressBlock H6 KnownInputData.targetInput 384 = H7 := by
  rw [compress_allA H6 384 (by omega), KnownDigestB.step7]
private theorem block8 : Ripemd160.compressBlock H7 KnownInputData.targetInput 448 = H8 := by
  rw [compress_allA H7 448 (by omega), KnownDigestB.step8]
private theorem block9 : Ripemd160.compressBlock H8 KnownInputData.targetInput 512 = H9 := by
  rw [compress_allA H8 512 (by omega), KnownDigestC.step9]
private theorem block10 : Ripemd160.compressBlock H9 KnownInputData.targetInput 576 = H10 := by
  rw [compress_allA H9 576 (by omega), KnownDigestC.step10]
private theorem block11 : Ripemd160.compressBlock H10 KnownInputData.targetInput 640 = H11 := by
  rw [compress_allA H10 640 (by omega), KnownDigestC.step11]
private theorem block12 : Ripemd160.compressBlock H11 KnownInputData.targetInput 704 = H12 := by
  rw [compress_allA H11 704 (by omega), KnownDigestC.step12]
private theorem block13 : Ripemd160.compressBlock H12 KnownInputData.targetInput 768 = H13 := by
  rw [compress_allA H12 768 (by omega), KnownDigestD.step13]
private theorem block14 : Ripemd160.compressBlock H13 KnownInputData.targetInput 832 = H14 := by
  rw [compress_allA H13 832 (by omega), KnownDigestD.step14]
private theorem block15 : Ripemd160.compressBlock H14 KnownInputData.targetInput 896 = H15 := by
  rw [compress_allA H14 896 (by omega), KnownDigestD.step15]

theorem absorb15 :
    SpecBridge.absorbBlocks H0 KnownInputData.targetInput 0 15 = H15 := by
  rw [show 15 = 14 + 1 by omega, SpecBridge.absorbBlocks_succ,
    show 14 = 13 + 1 by omega, SpecBridge.absorbBlocks_succ,
    show 13 = 12 + 1 by omega, SpecBridge.absorbBlocks_succ,
    show 12 = 11 + 1 by omega, SpecBridge.absorbBlocks_succ,
    show 11 = 10 + 1 by omega, SpecBridge.absorbBlocks_succ,
    show 10 = 9 + 1 by omega, SpecBridge.absorbBlocks_succ,
    show 9 = 8 + 1 by omega, SpecBridge.absorbBlocks_succ,
    show 8 = 7 + 1 by omega, SpecBridge.absorbBlocks_succ,
    show 7 = 6 + 1 by omega, SpecBridge.absorbBlocks_succ,
    show 6 = 5 + 1 by omega, SpecBridge.absorbBlocks_succ,
    show 5 = 4 + 1 by omega, SpecBridge.absorbBlocks_succ,
    show 4 = 3 + 1 by omega, SpecBridge.absorbBlocks_succ,
    show 3 = 2 + 1 by omega, SpecBridge.absorbBlocks_succ,
    show 2 = 1 + 1 by omega, SpecBridge.absorbBlocks_succ,
    show 1 = 0 + 1 by omega, SpecBridge.absorbBlocks_succ,
    SpecBridge.absorbBlocks_zero]
  norm_num
  rw [block1, block2, block3, block4, block5, block6, block7, block8,
    block9, block10, block11, block12, block13, block14, block15]

theorem hash_target : Ripemd160.hash KnownInputData.targetInput = targetDigest := by
  rw [HashSpecBridge.hash_eq_two_phase]
  rw [KnownInputData.targetInput_size]
  norm_num
  rw [canonicalTail_target]
  have hfinalSize : finalBlock.size = 64 := by
    norm_num [finalBlock, ByteArray.size]
  rw [hfinalSize]
  norm_num
  change SpecBridge.emitDigest
      (SpecBridge.absorbBlocks
        (SpecBridge.absorbBlocks H0 KnownInputData.targetInput 0 15)
        finalBlock 0 1) = targetDigest
  rw [absorb15]
  change SpecBridge.emitDigest
      (Ripemd160.compressBlock H15 finalBlock 0) = targetDigest
  rw [compress_final, KnownDigestD.step16]
  rfl
-/

abbrev knownAt := KnownDigestStates.knownAt

private theorem knownStep (i : Nat) (hi : i < 16) :
    Ripemd160.compressBlock (knownAt i)
      (Padding.paddedMessage KnownInputData.targetInput) (i * 64) =
      knownAt (i + 1) := by
  interval_cases i <;>
    first
    | exact KnownDigestSteps.step0
    | exact KnownDigestSteps.step1
    | exact KnownDigestSteps.step2
    | exact KnownDigestSteps.step3
    | exact KnownDigestSteps.step4
    | exact KnownDigestSteps.step5
    | exact KnownDigestSteps.step6
    | exact KnownDigestSteps.step7
    | exact KnownDigestSteps.step8
    | exact KnownDigestSteps.step9
    | exact KnownDigestSteps.step10
    | exact KnownDigestSteps.step11
    | exact KnownDigestSteps.step12
    | exact KnownDigestSteps.step13
    | exact KnownDigestSteps.step14
    | exact KnownDigestSteps.step15

theorem hashAfter_target (i : Nat) (hi : i ≤ 16) :
    CompressionSeamBridge.hashAfter KnownInputData.targetInput i = knownAt i := by
  unfold CompressionSeamBridge.hashAfter
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [SpecBridge.absorbBlocks_succ, ih (by omega)]
      simpa only [Nat.zero_add] using knownStep i (by omega)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestResult
