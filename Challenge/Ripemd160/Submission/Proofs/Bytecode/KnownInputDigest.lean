import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputData

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputDigest

open EvmSemantics.Crypto

def allA : Array UInt32 := Array.replicate 16 0x61616161
def finalWords : Array UInt32 := #[
  0x61616161, 0x61616161, 0x61616161, 0x61616161,
  0x61616161, 0x61616161, 0x61616161, 0x61616161,
  0x61616161, 0x61616161, 0x80, 0, 0, 0, 0x1f40, 0]

def H0 : Array UInt32 := #[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]
def H1 : Array UInt32 := #[0xd42339f0, 0xce5b9f6f, 0x2874a075, 0xdf67aaf1, 0xc6c1be1c]
def H2 : Array UInt32 := #[0x1444f17f, 0x45ea518a, 0x833387fa, 0xd50de705, 0x8cda43b8]
def H3 : Array UInt32 := #[0x0f072e90, 0x51f9c511, 0x1728d4d5, 0xb0c62f49, 0xaa734e75]
def H4 : Array UInt32 := #[0x22399a7c, 0xfa8e03fd, 0x89206743, 0x086255a6, 0x73f32ce6]
def H5 : Array UInt32 := #[0x340a2702, 0xb54c0d9d, 0xd8ad9bd1, 0xc8a6b825, 0xab84fe05]
def H6 : Array UInt32 := #[0xe24a8593, 0xa02db7e9, 0xa0554cd6, 0x2610702b, 0xf4119667]
def H7 : Array UInt32 := #[0xd8ee6fbe, 0x376d3aaf, 0x04966be9, 0x38d9201f, 0xc2251beb]
def H8 : Array UInt32 := #[0x91a278d9, 0xdd952af9, 0x0c614fd7, 0x0ecefde0, 0xd98aac12]
def H9 : Array UInt32 := #[0x97b5bc36, 0x295e856a, 0x4a0d0fd6, 0x2b5a9ba3, 0xad79b7f2]
def H10 : Array UInt32 := #[0x527b5e73, 0xae790937, 0xe97abdaa, 0x44b0c7a2, 0x6859fde1]
def H11 : Array UInt32 := #[0x7eeb5617, 0x2a8cc540, 0xd76b2368, 0x4f6ec6a5, 0x46ea8772]
def H12 : Array UInt32 := #[0xccc1166f, 0x70955e7b, 0xf18c7fee, 0x05dab55f, 0xdc6ee379]
def H13 : Array UInt32 := #[0xa9dee3a8, 0xa27f6780, 0x5b19456b, 0xec99deee, 0x76d20369]
def H14 : Array UInt32 := #[0xde7e43d2, 0x9718642b, 0xd8d6f20d, 0xa641f68a, 0x77f0d5cc]
def H15 : Array UInt32 := #[0x18453887, 0x3d42f166, 0xa3be41eb, 0xa36e4124, 0x8cfd905c]
def H16 : Array UInt32 := #[0xeede69aa, 0xe922899a, 0xe005812f, 0x1061f707, 0xcfe981f3]

def targetDigest : ByteArray := SpecBridge.emitDigest H16

def finalBlock : ByteArray := ByteArray.mk #[
  0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61,
  0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61,
  0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61,
  0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61,
  0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61,
  0x80, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0x40, 0x1f, 0, 0, 0, 0, 0, 0]

theorem canonicalTail_target :
    HashSpecBridge.canonicalTail KnownInputData.targetInput = finalBlock := by
  rw [HashSpecBridge.canonicalTail_eq]
  apply ByteArray.ext
  simp [KnownInputData.targetInput, finalBlock, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    ByteArray.data_append, ByteArray.size]

theorem read_allA (off i : Nat) (hoff : off + 64 ≤ 1000) (hi : i < 16) :
    Ripemd160.readLE32 KnownInputData.targetInput (off + i * 4) = 0x61616161 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : off + i * 4 < KnownInputData.targetInput.size := by
    rw [KnownInputData.targetInput_size]; omega
  have h1 : off + i * 4 + 1 < KnownInputData.targetInput.size := by
    rw [KnownInputData.targetInput_size]; omega
  have h2 : off + i * 4 + 2 < KnownInputData.targetInput.size := by
    rw [KnownInputData.targetInput_size]; omega
  have h3 : off + i * 4 + 3 < KnownInputData.targetInput.size := by
    rw [KnownInputData.targetInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    KnownInputData.targetInput_getElem _ h0,
    KnownInputData.targetInput_getElem _ h1,
    KnownInputData.targetInput_getElem _ h2,
    KnownInputData.targetInput_getElem _ h3]
  decide

theorem schedule_allA (off : Nat) (hoff : off + 64 ≤ 1000) :
    CompressionCorrect.schedule KnownInputData.targetInput off = allA := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 0 * 4) = 0x61616161 from read_allA off 0 hoff (by omega)]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 1 * 4) = 0x61616161 from read_allA off 1 hoff (by omega)]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 2 * 4) = 0x61616161 from read_allA off 2 hoff (by omega)]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 3 * 4) = 0x61616161 from read_allA off 3 hoff (by omega)]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 4 * 4) = 0x61616161 from read_allA off 4 hoff (by omega)]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 5 * 4) = 0x61616161 from read_allA off 5 hoff (by omega)]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 6 * 4) = 0x61616161 from read_allA off 6 hoff (by omega)]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 7 * 4) = 0x61616161 from read_allA off 7 hoff (by omega)]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 8 * 4) = 0x61616161 from read_allA off 8 hoff (by omega)]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 9 * 4) = 0x61616161 from read_allA off 9 hoff (by omega)]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 10 * 4) = 0x61616161 from read_allA off 10 hoff (by omega)]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 11 * 4) = 0x61616161 from read_allA off 11 hoff (by omega)]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 12 * 4) = 0x61616161 from read_allA off 12 hoff (by omega)]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 13 * 4) = 0x61616161 from read_allA off 13 hoff (by omega)]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 14 * 4) = 0x61616161 from read_allA off 14 hoff (by omega)]
  rw [show Ripemd160.readLE32 KnownInputData.targetInput (off + 15 * 4) = 0x61616161 from read_allA off 15 hoff (by omega)]
  decide

theorem compress_allA (h : Array UInt32) (off : Nat) (hoff : off + 64 ≤ 1000) :
    Ripemd160.compressBlock h KnownInputData.targetInput off =
      CompressionCorrect.normalizedCompress h allA := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule_allA off hoff]

theorem read_final (i : Nat) (hi : i < 16) :
    Ripemd160.readLE32 finalBlock (i * 4) = finalWords[i]! := by
  interval_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [finalBlock, finalWords, Ripemd160.readLE32,
        List.range', List.foldl, ByteArray.size,
        ByteArray.getElem_eq_getElem_data] <;>
    try (apply UInt32.eq_of_toBitVec_eq; decide)

theorem schedule_final : CompressionCorrect.schedule finalBlock 0 = finalWords := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 finalBlock (0 * 4) = finalWords[0]! from read_final 0 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (1 * 4) = finalWords[1]! from read_final 1 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (2 * 4) = finalWords[2]! from read_final 2 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (3 * 4) = finalWords[3]! from read_final 3 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (4 * 4) = finalWords[4]! from read_final 4 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (5 * 4) = finalWords[5]! from read_final 5 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (6 * 4) = finalWords[6]! from read_final 6 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (7 * 4) = finalWords[7]! from read_final 7 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (8 * 4) = finalWords[8]! from read_final 8 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (9 * 4) = finalWords[9]! from read_final 9 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (10 * 4) = finalWords[10]! from read_final 10 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (11 * 4) = finalWords[11]! from read_final 11 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (12 * 4) = finalWords[12]! from read_final 12 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (13 * 4) = finalWords[13]! from read_final 13 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (14 * 4) = finalWords[14]! from read_final 14 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (15 * 4) = finalWords[15]! from read_final 15 (by omega)]
  decide

theorem compress_final (h : Array UInt32) :
    Ripemd160.compressBlock h finalBlock 0 =
      CompressionCorrect.normalizedCompress h finalWords := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule_final]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputDigest
