import Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanSelect
import Mathlib.Tactic.IntervalCases
set_option warningAsError true
/-!
# H10 direct stack-resident round probe

This module models one unrolled H10 stack round exactly as emitted by
`benchmark-results/ripemd160/h10/gen_h10.py` (`ops_for_f`, `ops_for_sum`,
`ops_for_rot_t`, `ops_for_c10_shuffle`) and `build_h10.py`
(`ops_for_round`, `verify_round`).

The stack holds `[A, B, C, D, E]` top-first. One round computes the five
specialized Boolean forms, the masked sum, the inline variable rotate
merged with the addition of `E`, the inline `rotl(C, 10)`, and the
transition `[A, B, C, D, E]` to `[E, T, B, rotl(C, 10), D]`.

All statements are for embedded 32-bit values only. The two low-32
facts are proved explicitly: full-width `NOT` inside `f2`/`f4` is
absorbed by the outer `SUM`/`F` mask, and the omitted inner rotate mask
is absorbed by the final `T` mask before adding `E`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound

open EvmSemantics
open Challenge.EvmProof.Word

/-- Direct H10 Boolean form for round group `j`.

Mirrors `ops_for_f` in `gen_h10.py`:
`0`: `B ^ C ^ D`,
`1`: `((C ^ D) & B) ^ D`,
`2`: `mask32 ((B | ~C) ^ D)` with full-width `NOT`,
`3`: `((B ^ C) & D) ^ C`,
otherwise: `mask32 (B ^ (C | ~D))` with full-width `NOT`.
-/
def stackF (j : Nat) (b c d : UInt256) : UInt256 :=
  match j with
  | 0 => (b ^^^ c) ^^^ d
  | 1 => ((c ^^^ d) &&& b) ^^^ d
  | 2 => mask32 ((b ||| ~~~c) ^^^ d)
  | 3 => ((b ^^^ c) &&& d) ^^^ c
  | _ => mask32 (b ^^^ (c ||| ~~~d))

/-- Inline variable rotate without an intermediate mask.

Mirrors `ops_for_rot_t`: `SHL(sum, r) OR SHR(sum, 32 - r)` on 256-bit
words. The caller applies the final `T` mask after adding `E`.
-/
def stackRawRot (s : UInt256) (r : Nat) : UInt256 :=
  UInt256.shiftLeft s (UInt256.ofNat r) |||
    UInt256.shiftRight s (UInt256.ofNat (32 - r))

/-- Inline `rotl(C, 10)` with its final mask.

Mirrors `ops_for_c10_shuffle`: `SHL(C, 10) OR SHR(C, 22)` then
`AND 0xffffffff`.
-/
def stackC10 (c : UInt256) : UInt256 :=
  mask32 (UInt256.shiftLeft c (UInt256.ofNat 10) |||
    UInt256.shiftRight c (UInt256.ofNat 22))

/-- Masked H10 sum with stack order `f + A` first.

Mirrors `ops_for_sum`: `ADD f A`, `MLOAD X`, `ADD`, optional `ADD K`,
then `AND 0xffffffff`. Adding `0` for `K = 0` is the identity.
-/
def stackSum (f a word constant : UInt256) : UInt256 :=
  mask32 (((f + a) + word) + constant)

/-- One direct H10 stack round.

`f` is `stackF`, `sum` is `stackSum` with stack order `f + A` first,
`t` is the merged rotate plus `E` with only the final mask, and the
result is `[E, T, B, rotl(C, 10), D]`.
-/
def stackRound (x : Compression.EvmWorking) (j : Nat)
    (word : UInt256) (rotation : Nat)
    (constant : UInt256) : Compression.EvmWorking :=
  { a := x.e
    b := mask32 (stackRawRot
      (stackSum (stackF j x.b x.c x.d) x.a word constant)
      rotation + x.e)
    c := x.b
    d := stackC10 x.c
    e := x.d }

/-- The five direct Boolean forms agree with `Word.evmF` on embedded
words. Cases `1` and `3` use the proved selection identities. -/
theorem stackF_eq_evmF (j : Nat) (b c d : UInt32)
    (hj : j < 5) :
    stackF j (ofUInt32 b) (ofUInt32 c) (ofUInt32 d) =
      Word.evmF j (ofUInt32 b) (ofUInt32 c) (ofUInt32 d) := by
  interval_cases j
  · rfl
  · exact (BooleanSelect.select1 _ _ _).symm
  · rfl
  · exact (BooleanSelect.select3 _ _ _).symm
  · rfl

/-- Direct Boolean forms implement the specification `f`, including the
low-32 absorption of full-width `NOT` in cases `2` and `4`. -/
theorem stackF_embed (j : Nat) (b c d : UInt32)
    (hj : j < 5) :
    stackF j (ofUInt32 b) (ofUInt32 c) (ofUInt32 d) =
      ofUInt32 (Crypto.Ripemd160.f j b c d) := by
  rw [stackF_eq_evmF j b c d hj,
    Word.evmF_ofUInt32 j b c d hj]

/-- Projecting after `mask32` forgets nothing new. -/
private theorem toUInt32_mask32 (x : UInt256) :
    toUInt32 (mask32 x) = toUInt32 x := by
  rw [mask32_eq_ofUInt32, toUInt32_ofUInt32]

/-- Low-32 fact for the merged rotate: adding `E` before the final mask
makes a separate inner rotate mask redundant. -/
theorem mask_add_omitted (raw e : UInt256) :
    mask32 (raw + e) = mask32 (mask32 raw + e) := by
  have h1 : mask32 (raw + e) =
      ofUInt32 (toUInt32 raw + toUInt32 e) := by
    rw [mask32_eq_ofUInt32, toUInt32_add]
  have h2 : mask32 (mask32 raw + e) =
      ofUInt32 (toUInt32 raw + toUInt32 e) := by
    rw [mask32_eq_ofUInt32, toUInt32_add, toUInt32_mask32]
  rw [h1, h2]

/-- `Word.evmRotl32` is exactly the masked inline raw rotate. -/
theorem evmRotl_eq_mask_raw (s : UInt256) (r : Nat) :
    Word.evmRotl32 s r = mask32 (stackRawRot s r) := by
  rfl

/-- Masked inline raw rotate implements the specification rotate. -/
theorem stackRawRot_embed (x : UInt32) (n : Nat)
    (hn0 : 0 < n) (hn : n < 32) :
    mask32 (stackRawRot (ofUInt32 x) n) =
      ofUInt32 (Crypto.Ripemd160.rotl32 x n) := by
  rw [← evmRotl_eq_mask_raw]
  exact Word.evmRotl32_ofUInt32 x n hn0 hn

/-- Inline rotate without a separate mask agrees with the masked
`Word.evmRotl32` form once `E` is added under the final mask. -/
theorem stackT_omitted (s e : UInt256) (r : Nat) :
    mask32 (stackRawRot s r + e) =
      mask32 (Word.evmRotl32 s r + e) := by
  rw [evmRotl_eq_mask_raw, mask_add_omitted]

/-- Inline `rotl(C, 10)` agrees with `Word.evmRotl32` at `10`. -/
theorem stackC10_eq (c : UInt256) :
    stackC10 c = Word.evmRotl32 c 10 := by
  rfl

/-- Direct H10 stack round equals the reference `Compression.evmRound`
for all embedded working values, `j < 5`, embedded word and constant,
and `0 < rotation < 32`. -/
theorem stackRound_eq_evmRound (x : Compression.Working)
    (j : Nat) (word constant : UInt32) (rotation : Nat)
    (hj : j < 5) (hr0 : 0 < rotation) (hr : rotation < 32) :
    stackRound (Compression.embed x) j (ofUInt32 word)
      rotation (ofUInt32 constant) =
      Compression.evmRound (Compression.embed x) j
        (ofUInt32 word) rotation (ofUInt32 constant) := by
  have _ : 0 < rotation := hr0
  have _ : rotation < 32 := hr
  have hf : stackF j (ofUInt32 x.b) (ofUInt32 x.c)
      (ofUInt32 x.d) =
      Word.evmF j (ofUInt32 x.b) (ofUInt32 x.c)
        (ofUInt32 x.d) :=
    stackF_eq_evmF j x.b x.c x.d hj
  unfold stackRound stackSum Compression.evmRound Compression.embed
  rw [hf]
  rw [word_add_comm (Word.evmF j (ofUInt32 x.b)
    (ofUInt32 x.c) (ofUInt32 x.d)) (ofUInt32 x.a)]
  rw [stackT_omitted, stackC10_eq]

/-- Direct H10 stack round implements the specification `round` under
embedding, via `Compression.evmRound_embed`. -/
theorem stackRound_embed (x : Compression.Working)
    (j : Nat) (word constant : UInt32) (rotation : Nat)
    (hj : j < 5) (hr0 : 0 < rotation) (hr : rotation < 32) :
    stackRound (Compression.embed x) j (ofUInt32 word)
      rotation (ofUInt32 constant) =
      Compression.embed
        (Compression.round x j word rotation constant) := by
  rw [stackRound_eq_evmRound x j word constant rotation hj hr0 hr,
    Compression.evmRound_embed x j word constant rotation hj hr0 hr]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
