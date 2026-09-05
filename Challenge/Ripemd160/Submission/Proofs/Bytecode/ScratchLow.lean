import Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationFold
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationMultiply

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ScratchLow

open EvmSemantics
open Challenge.EvmProof.Word

theorem toUInt32_lnot (x : UInt256) :
    toUInt32 (~~~x) = Crypto.Ripemd160.bnot32 (toUInt32 x) := by
  apply UInt32.toNat_inj.mp
  rw [toUInt32_toNat]
  change (UInt256.lnot x).toNat % 2 ^ 32 =
    (Crypto.Ripemd160.bnot32 (toUInt32 x)).toNat
  unfold UInt256.lnot Crypto.Ripemd160.bnot32
  rw [word_toNat_ofNat]
  have hall : (0xffffffff : UInt32) = -1 := by decide
  rw [hall, UInt32.xor_neg_one, UInt32.toNat_not]
  rw [toUInt32_toNat]
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  have hq : x.toNat / 2 ^ 32 < 2 ^ 224 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    norm_num [← pow_add]
    exact hx
  have hdecomp := Nat.mod_add_div x.toNat (2 ^ 32)
  have hsplit :
      2 ^ 256 - 1 - x.toNat =
        (2 ^ 32 - 1 - x.toNat % 2 ^ 32) +
          2 ^ 32 * (2 ^ 224 - 1 - x.toNat / 2 ^ 32) := by
    omega
  rw [show UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)), hsplit, Nat.add_mod,
    Nat.mul_mod_right, Nat.add_zero]
  rw [Nat.mod_mod]
  rw [show UInt32.size = 2 ^ 32 by rfl]
  change (2 ^ 32 - 1 - x.toNat % 2 ^ 32) % 2 ^ 32 =
    2 ^ 32 - 1 - x.toNat % 2 ^ 32
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem toUInt32_mask32 (x : UInt256) :
    toUInt32 (mask32 x) = toUInt32 x := by
  rw [mask32_eq_ofUInt32, toUInt32_ofUInt32]

private theorem toUInt32_and (x y : UInt256) :
    toUInt32 (x &&& y) = toUInt32 x &&& toUInt32 y := by
  apply ofUInt32_injective
  rw [← mask32_eq_ofUInt32, mask32_and]

theorem stackF_project (j : Nat) (b c d : UInt256) (hj : j < 5) :
    toUInt32 (StackRound.stackF j b c d) =
      Crypto.Ripemd160.f j (toUInt32 b) (toUInt32 c) (toUInt32 d) := by
  calc
    toUInt32 (StackRound.stackF j b c d) =
        toUInt32 (StackRound.stackF j (ofUInt32 (toUInt32 b))
          (ofUInt32 (toUInt32 c)) (ofUInt32 (toUInt32 d))) := by
      interval_cases j <;>
        simp [StackRound.stackF, toUInt32_mask32, toUInt32_and,
          toUInt32_lnot]
    _ = Crypto.Ripemd160.f j (toUInt32 b) (toUInt32 c)
          (toUInt32 d) := by
      rw [StackRound.stackF_embed j (toUInt32 b) (toUInt32 c)
        (toUInt32 d) hj, toUInt32_ofUInt32]

def rawC10 (c : UInt256) : UInt256 :=
  UInt256.shiftRight
    (UInt256.mul (UInt256.ofNat (0x100000001 : Nat)) c)
    (UInt256.ofNat 22)

theorem rawC10_low (c : UInt256) (hc : c.toNat < 2 ^ 32) :
    toUInt32 (rawC10 c) = toUInt32 (StackRound.stackC10 c) := by
  have hfold := congrArg toUInt32 (RotationFold.C10_or_fold c)
  simp only [toUInt32_mask32] at hfold
  simp only [rawC10]
  rw [RotationMultiply.factor_mul_eq_or_shift c hc]
  exact hfold

def rawRound (x : Compression.EvmWorking) (j : Nat)
    (word : UInt256) (rotation : Nat)
    (constant : UInt256) : Compression.EvmWorking :=
  { a := x.e
    b := mask32 (StackRound.stackRawRot
      (StackRound.stackSum (StackRound.stackF j x.b x.c x.d)
        x.a word constant) rotation + x.e)
    c := x.b
    d := rawC10 x.c
    e := x.d }

structure WorkingRepresents (x : Compression.EvmWorking)
    (y : Compression.Working) : Prop where
  a : toUInt32 x.a = y.a
  b : x.b = ofUInt32 y.b
  c : x.c = ofUInt32 y.c
  d : toUInt32 x.d = y.d
  e : toUInt32 x.e = y.e

@[simp] theorem embed_represents (x : Compression.Working) :
    WorkingRepresents (Compression.embed x) x := by
  constructor <;> simp [Compression.embed]

theorem rawRound_represents (x : Compression.EvmWorking)
    (y : Compression.Working) (j : Nat) (word constant : UInt32)
    (rotation : Nat) (hxy : WorkingRepresents x y)
    (hj : j < 5) (hr0 : 0 < rotation) (hr : rotation < 32) :
    WorkingRepresents
      (rawRound x j (ofUInt32 word) rotation (ofUInt32 constant))
      (Compression.round y j word rotation constant) := by
  have hf0 := stackF_project j x.b x.c x.d hj
  have hf : toUInt32 (StackRound.stackF j x.b x.c x.d) =
      Crypto.Ripemd160.f j y.b y.c y.d := by
    rw [hf0, hxy.b, hxy.c, toUInt32_ofUInt32, toUInt32_ofUInt32, hxy.d]
  have hsum : StackRound.stackSum (StackRound.stackF j x.b x.c x.d)
      x.a (ofUInt32 word) (ofUInt32 constant) =
      ofUInt32 (y.a + Crypto.Ripemd160.f j y.b y.c y.d + word + constant) := by
    rw [StackRound.stackSum, mask32_eq_ofUInt32]
    apply congrArg ofUInt32
    simp only [toUInt32_add, toUInt32_ofUInt32, hf, hxy.a]
    rw [UInt32.add_comm (Crypto.Ripemd160.f j y.b y.c y.d) y.a]
  have hrot := StackRound.stackRawRot_embed
    (y.a + Crypto.Ripemd160.f j y.b y.c y.d + word + constant)
    rotation hr0 hr
  have hrot32 := congrArg toUInt32 hrot
  simp only [toUInt32_mask32, toUInt32_ofUInt32] at hrot32
  have hc : x.c.toNat < 2 ^ 32 := by
    rw [hxy.c, ofUInt32_toNat]
    exact y.c.toNat_lt
  have hc10 := rawC10_low x.c hc
  constructor
  · exact hxy.e
  · simp only [rawRound, Compression.round, mask32_eq_ofUInt32]
    apply congrArg ofUInt32
    simp only [hsum, toUInt32_add, hrot32, hxy.e]
  · simpa [rawRound, Compression.round] using hxy.b
  · simp only [rawRound, Compression.round]
    rw [hc10, hxy.c, StackRound.stackC10_eq,
      Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.evmRotl32_ofUInt32
        y.c 10 (by decide) (by decide),
      toUInt32_ofUInt32]
  · exact hxy.d

theorem evmCombine_of_represents (h : Compression.HashState)
    (left right : Compression.EvmWorking)
    (leftModel rightModel : Compression.Working)
    (hl : WorkingRepresents left leftModel)
    (hr : WorkingRepresents right rightModel) :
    Compression.evmCombine (Compression.embedHash h) left right =
      Compression.embedHash (Compression.combine h leftModel rightModel) := by
  have hlb : toUInt32 left.b = leftModel.b := by
    rw [hl.b, toUInt32_ofUInt32]
  have hlc : toUInt32 left.c = leftModel.c := by
    rw [hl.c, toUInt32_ofUInt32]
  have hrb : toUInt32 right.b = rightModel.b := by
    rw [hr.b, toUInt32_ofUInt32]
  have hrc : toUInt32 right.c = rightModel.c := by
    rw [hr.c, toUInt32_ofUInt32]
  simp [Compression.evmCombine, Compression.embedHash, Compression.combine,
    mask32_eq_ofUInt32, toUInt32_add, hl.a, hlb, hlc, hl.d, hl.e,
    hr.a, hrb, hrc, hr.d, hr.e]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ScratchLow
