import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Mathlib.Data.Nat.Bits

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationFold

open EvmSemantics
open Challenge.EvmProof.Word

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

private theorem lor_toNat (a b : UInt256) :
    (a ||| b).toNat = a.toNat ||| b.toNat := by
  exact Challenge.EvmProof.Word.word_toNat_lor a b

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

theorem C10_or_fold (c : UInt256) :
    mask32 (UInt256.shiftRight
      (c ||| UInt256.shiftLeft c (UInt256.ofNat 32))
      (UInt256.ofNat 22)) = StackRound.stackC10 c := by
  apply Challenge.EvmProof.Word.word_ext
  unfold StackRound.stackC10
  rw [Challenge.EvmProof.Word.mask32_toNat,
    Challenge.EvmProof.Word.mask32_toNat]
  rw [show 0xffffffff = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 32
  · simp only [Nat.testBit_mod_two_pow, hk, decide_true, Bool.true_and]
    rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by norm_num),
      lor_toNat,
      shiftLeft_toNat c 32 (by norm_num),
      lor_toNat,
      shiftLeft_toNat c 10 (by norm_num),
      Challenge.EvmProof.Word.shiftRight_toNat c (by norm_num)]
    simp only [Nat.testBit_or, Nat.testBit_shiftRight,
      Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
    by_cases hk10 : 10 ≤ k
    · have h1 : 22 + k < 256 := by omega
      have h2 : 32 ≤ 22 + k := by omega
      have h3 : k < 256 := by omega
      have h4 : 22 + k - 32 = k - 10 := by omega
      simp [hk10, h1, h2, h3, h4, Bool.or_comm]
    · have h1 : 22 + k < 256 := by omega
      have h2 : ¬32 ≤ 22 + k := by omega
      have h3 : k < 256 := by omega
      simp [hk10, h1, h2, h3]
  · simp only [Nat.testBit_mod_two_pow, hk, decide_false, Bool.false_and]

theorem rawRot_or_fold (q : UInt256) (r : Nat)
    (hq : q.toNat < 2 ^ 32) (hr : r ≤ 32) :
    UInt256.shiftRight
      (q ||| UInt256.shiftLeft q (UInt256.ofNat 32))
      (UInt256.ofNat (32 - r)) = StackRound.stackRawRot q r := by
  apply Challenge.EvmProof.Word.word_ext
  unfold StackRound.stackRawRot
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by omega),
    lor_toNat,
    shiftLeft_low32_toNat q 32 hq (by omega),
    lor_toNat,
    shiftLeft_low32_toNat q r hq hr,
    Challenge.EvmProof.Word.shiftRight_toNat q (by omega)]
  have hrot : (q.toNat <<< 32) >>> (32 - r) = q.toNat <<< r := by
    have hsub := Nat.shiftLeft_sub q.toNat (n := 32) (k := 32 - r)
      (by omega)
    simpa only [Nat.sub_sub_self hr] using hsub.symm
  calc
    (q.toNat ||| q.toNat <<< 32) >>> (32 - r) =
        (q.toNat >>> (32 - r)) ||| ((q.toNat <<< 32) >>> (32 - r)) :=
      Nat.shiftRight_or_distrib
    _ = (q.toNat >>> (32 - r)) ||| (q.toNat <<< r) := by rw [hrot]
    _ = (q.toNat <<< r) ||| (q.toNat >>> (32 - r)) := Nat.or_comm _ _

end Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationFold
