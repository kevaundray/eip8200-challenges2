import Challenge.EvmProof.Word
import Challenge.EvmProof.Bytes

set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleMath

open EvmSemantics
open Challenge.EvmProof

abbrev EWord := EvmSemantics.UInt256

/-- The EVM logical right shift with a natural shift amount. -/
def shr (v : EWord) (n : Nat) : EWord :=
  UInt256.shiftRight v (UInt256.ofNat n)

/-- The EVM logical left shift with a natural shift amount. -/
def shl (v : EWord) (n : Nat) : EWord :=
  UInt256.shiftLeft v (UInt256.ofNat n)

/-- `0x00ff` repeated sixteen times. -/
def mask8 : EWord :=
  UInt256.ofNat 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff

/-- `0x0000ffff` repeated eight times. -/
def mask16 : EWord :=
  UInt256.ofNat 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff

/-- Reverse the bytes inside each four-byte lane of a 256-bit word. -/
def packed (v : EWord) : EWord :=
  let t :=
    (shr v 8 &&& mask8) ||| shl (v &&& mask8) 8
  (shr t 16 &&& mask16) ||| shl (t &&& mask16) 16

/-- Decode four consecutive big-endian bytes as one little-endian word. -/
def le4 (v : EWord) (j : Nat) : EWord :=
  let b0 := UInt256.byteAt (UInt256.ofNat (4 * j + 0)) v
  let b1 := UInt256.byteAt (UInt256.ofNat (4 * j + 1)) v
  let b2 := UInt256.byteAt (UInt256.ofNat (4 * j + 2)) v
  let b3 := UInt256.byteAt (UInt256.ofNat (4 * j + 3)) v
  (b0 ||| shl b1 8) ||| (shl b2 16 ||| shl b3 24)

private theorem shr_toNat (v : EWord) (n : Nat) (hn : n < 256) :
    (shr v n).toNat = v.toNat >>> n := by
  exact Challenge.EvmProof.Word.shiftRight_toNat v hn

private theorem shl_toNat (v : EWord) (n : Nat) (hn : n < 256) :
    (shl v n).toNat = (v.toNat <<< n) % 2 ^ 256 := by
  unfold shl UInt256.shiftLeft
  have hshift : (UInt256.ofNat n).toNat = n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [if_neg (by omega), hshift,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [show UInt256.size = 2 ^ 256 by rfl, Nat.mod_mod]

private theorem lor_toNat (a b : EWord) :
    (a ||| b).toNat = a.toNat ||| b.toNat := by
  exact Challenge.EvmProof.Word.word_toNat_lor a b

private theorem land_toNat (a b : EWord) :
    (a &&& b).toNat = a.toNat &&& b.toNat := by
  exact Challenge.EvmProof.Word.word_toNat_land a b

private theorem mask8_toNat : mask8.toNat =
    0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff := by
  unfold mask8
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (by norm_num)

private theorem mask16_toNat : mask16.toNat =
    0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff := by
  unfold mask16
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (by norm_num)

private theorem shr8_toNat (v : EWord) : (shr v 8).toNat = v.toNat >>> 8 := by
  exact shr_toNat v 8 (by norm_num)

private theorem shr16_toNat (v : EWord) : (shr v 16).toNat = v.toNat >>> 16 := by
  exact shr_toNat v 16 (by norm_num)

private theorem shl8_toNat (v : EWord) :
    (shl v 8).toNat = (v.toNat <<< 8) % 2 ^ 256 := by
  exact shl_toNat v 8 (by norm_num)

private theorem shl16_toNat (v : EWord) :
    (shl v 16).toNat = (v.toNat <<< 16) % 2 ^ 256 := by
  exact shl_toNat v 16 (by norm_num)

private theorem shl24_toNat (v : EWord) :
    (shl v 24).toNat = (v.toNat <<< 24) % 2 ^ 256 := by
  exact shl_toNat v 24 (by norm_num)

private theorem byteAt_toNat (v : EWord) (i : Nat) (hi : i < 32) :
    (UInt256.byteAt (UInt256.ofNat i) v).toNat =
      (v.toNat >>> (8 * (31 - i))) &&& 0xff := by
  unfold UInt256.byteAt
  have hi256 : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans hi (by norm_num))
  rw [hi256, if_neg (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat]
  have hlow :
      (v.toNat >>> (8 * (31 - i))) &&& 0xff ≤ 0xff := Nat.and_le_right
  exact Nat.mod_eq_of_lt (by omega)

theorem packed_extract (v : EWord) (j : Nat) (hj : j < 8) :
    Challenge.EvmProof.Word.mask32 (shr (packed v) (32 * (7 - j))) =
      Challenge.EvmProof.Word.mask32 (le4 v j) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.mask32_toNat,
    Challenge.EvmProof.Word.mask32_toNat]
  rw [show 0xffffffff = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 32
  · simp only [Nat.testBit_mod_two_pow, hk, decide_true, Bool.true_and]
    simp only [packed, le4]
    rw [shr_toNat _ _ (by omega)]
    repeat
      first
      | rw [lor_toNat]
      | rw [land_toNat]
      | rw [shr8_toNat]
      | rw [shr16_toNat]
      | rw [shl8_toNat]
      | rw [shl16_toNat]
      | rw [shl24_toNat]
      | rw [mask8_toNat]
      | rw [mask16_toNat]
    rw [byteAt_toNat v (4 * j + 0) (by omega),
      byteAt_toNat v (4 * j + 1) (by omega),
      byteAt_toNat v (4 * j + 2) (by omega),
      byteAt_toNat v (4 * j + 3) (by omega)]
    simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_or,
      Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
    interval_cases j <;> interval_cases k <;>
      norm_num [Nat.testBit_eq_decide_div_mod_eq]
  · simp only [Nat.testBit_mod_two_pow, hk, decide_false, Bool.false_and]

theorem le4_readWord_offset (bytes : ByteArray) (offset j : Nat) (hj : j < 8) :
    le4 (MachineState.readWord bytes offset) j =
      le4 (MachineState.readWord bytes (offset + 4 * j)) 0 := by
  simp only [le4, Nat.mul_zero, Nat.zero_add]
  rw [Challenge.EvmProof.Bytes.byteAt_readWord bytes offset (4 * j + 0) (by omega),
    Challenge.EvmProof.Bytes.byteAt_readWord bytes offset (4 * j + 1) (by omega),
    Challenge.EvmProof.Bytes.byteAt_readWord bytes offset (4 * j + 2) (by omega),
    Challenge.EvmProof.Bytes.byteAt_readWord bytes offset (4 * j + 3) (by omega),
    Challenge.EvmProof.Bytes.byteAt_readWord (bytes) (offset + 4 * j) 0 (by omega),
    Challenge.EvmProof.Bytes.byteAt_readWord (bytes) (offset + 4 * j) 1 (by omega),
    Challenge.EvmProof.Bytes.byteAt_readWord (bytes) (offset + 4 * j) 2 (by omega),
    Challenge.EvmProof.Bytes.byteAt_readWord (bytes) (offset + 4 * j) 3 (by omega)]
  have h0 : offset + (4 * j + 0) = offset + 4 * j + 0 := by omega
  have h1 : offset + (4 * j + 1) = offset + 4 * j + 1 := by omega
  have h2 : offset + (4 * j + 2) = offset + 4 * j + 2 := by omega
  have h3 : offset + (4 * j + 3) = offset + 4 * j + 3 := by omega
  rw [h0, h1, h2, h3]

theorem mask32_shr224 (v : EWord) :
    Challenge.EvmProof.Word.mask32 (shr v 224) = shr v 224 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.mask32_toNat]
  rw [show 0xffffffff = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  rw [shr_toNat v 224 (by norm_num)]
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftRight_eq_div_pow]
  apply (Nat.div_lt_iff_lt_mul (by positivity)).2
  calc
    v.toNat < 2 ^ 256 := v.val.isLt
    _ = 2 ^ 32 * 2 ^ 224 := by rw [← Nat.pow_add]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleMath
