import Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationFold
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.Ring

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationMultiply

open EvmSemantics
open Challenge.EvmProof.Word

private theorem factor_toNat :
    (UInt256.ofNat (0x100000001 : Nat)).toNat = 2 ^ 32 + 1 := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  norm_num

private theorem shiftLeft_toNat (v : UInt256) (n : Nat) (hn : n < 256) :
    (UInt256.shiftLeft v (UInt256.ofNat n)).toNat =
      (v.toNat <<< n) % 2 ^ 256 := by
  unfold UInt256.shiftLeft
  have hshift : (UInt256.ofNat n).toNat = n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [if_neg (by omega), hshift,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [show UInt256.size = 2 ^ 256 by rfl, Nat.mod_mod]

private theorem shiftLeft_low32_toNat (q : UInt256) (r : Nat)
    (hq : q.toNat < 2 ^ 32) (hr : r ≤ 32) :
    (UInt256.shiftLeft q (UInt256.ofNat r)).toNat = q.toNat <<< r := by
  have hmul_le : q.toNat * 2 ^ r ≤ 2 ^ 32 * 2 ^ 32 :=
    Nat.mul_le_mul (Nat.le_of_lt hq)
      (Nat.pow_le_pow_right Nat.zero_lt_two hr)
  have hmul : q.toNat * 2 ^ r < 2 ^ 256 := by
    calc
      q.toNat * 2 ^ r ≤ 2 ^ 32 * 2 ^ 32 := hmul_le
      _ < 2 ^ 256 := by norm_num [← Nat.pow_add]
  rw [shiftLeft_toNat q r (by omega), Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt hmul

private theorem mul_toNat (a b : UInt256) :
    (UInt256.mul a b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

private theorem lor_toNat (a b : UInt256) :
    (a ||| b).toNat = a.toNat ||| b.toNat := by
  exact Challenge.EvmProof.Word.word_toNat_lor a b

theorem factor_product_le (q : UInt256) (hq : q.toNat < 2 ^ 32) :
    (2 ^ 32 + 1) * q.toNat ≤ 2 ^ 64 - 1 := by
  have hqle : q.toNat ≤ 2 ^ 32 - 1 := by omega
  calc
    (2 ^ 32 + 1) * q.toNat ≤ (2 ^ 32 + 1) * (2 ^ 32 - 1) :=
      Nat.mul_le_mul_left _ hqle
    _ = 2 ^ 64 - 1 := by norm_num [← Nat.pow_add]

private theorem factor_product_lt_size (q : UInt256)
    (hq : q.toNat < 2 ^ 32) :
    (2 ^ 32 + 1) * q.toNat < 2 ^ 256 := by
  exact lt_of_le_of_lt (factor_product_le q hq) (by norm_num)

theorem factor_mul_eq_or_shift (q : UInt256) (hq : q.toNat < 2 ^ 32) :
    UInt256.mul (UInt256.ofNat (0x100000001 : Nat)) q =
      q ||| UInt256.shiftLeft q (UInt256.ofNat 32) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [mul_toNat, factor_toNat,
    lor_toNat,
    shiftLeft_low32_toNat q 32 hq (by omega)]
  have hprod : (2 ^ 32 + 1) * q.toNat < 2 ^ 256 := by
    exact factor_product_lt_size q hq
  rw [Nat.mod_eq_of_lt hprod]
  calc
    (2 ^ 32 + 1) * q.toNat = q.toNat <<< 32 + q.toNat := by
      rw [Nat.shiftLeft_eq]
      ring
    _ = (q.toNat <<< 32) ||| q.toNat :=
      Nat.shiftLeft_add_eq_or_of_lt hq q.toNat
    _ = q.toNat ||| (q.toNat <<< 32) := Nat.or_comm _ _

theorem factor_mul_mask32_eq_or_shift (q : UInt256) :
    UInt256.mul (UInt256.ofNat (0x100000001 : Nat)) (mask32 q) =
      mask32 q ||| UInt256.shiftLeft (mask32 q) (UInt256.ofNat 32) := by
  apply factor_mul_eq_or_shift
  rw [Challenge.EvmProof.Word.mask32_toNat,
    show 0xffffffff = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

theorem rawRot_mul (q : UInt256) (r : Nat)
    (hq : q.toNat < 2 ^ 32) (hr : r ≤ 32) :
    UInt256.shiftRight
      (UInt256.mul (UInt256.ofNat (0x100000001 : Nat)) q)
      (UInt256.ofNat (32 - r)) = StackRound.stackRawRot q r := by
  rw [factor_mul_eq_or_shift q hq]
  exact RotationFold.rawRot_or_fold q r hq hr

end Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationMultiply
