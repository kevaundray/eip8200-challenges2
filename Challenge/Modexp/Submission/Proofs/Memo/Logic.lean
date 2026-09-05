import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Word
import Challenge.Modexp.Spec
import Batteries.Data.Nat.Bitwise.Lemmas

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Generic facts for exact-calldata memo guards

A memo guard compares fixed calldata words against constants by XOR/OR
accumulation.  This module states the accumulator's zero test, the word-level
equality it certifies, and the bridge from matched words to the operand
values `spec` decodes.
-/

namespace Challenge.Modexp.Submission.Proofs.Memo.Logic

open EvmSemantics
open EvmSemantics.EVM

private theorem natOr_eq_zero_iff (a b : Nat) :
    a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hbit (i : Nat) :
        a.testBit i = false ∧ b.testBit i = false := by
      have := congrArg (fun n => n.testBit i) h
      simpa using this
    constructor
    · apply Nat.eq_of_testBit_eq
      intro i
      simpa using (hbit i).1
    · apply Nat.eq_of_testBit_eq
      intro i
      simpa using (hbit i).2
  · rintro ⟨rfl, rfl⟩
    decide

theorem wordOr_eq_zero_iff (a b : UInt256) :
    UInt256.lor a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hzeroNat : (0 : UInt256).toNat = 0 := by decide
    have hnat : a.toNat ||| b.toNat = 0 := by
      rw [← Challenge.EvmProof.Word.word_toNat_lor, h]
      rfl
    rcases (natOr_eq_zero_iff a.toNat b.toNat).1 hnat with ⟨ha, hb⟩
    constructor
    · apply Challenge.EvmProof.Word.word_ext
      rw [hzeroNat]
      exact ha
    · apply Challenge.EvmProof.Word.word_ext
      rw [hzeroNat]
      exact hb
  · rintro ⟨rfl, rfl⟩
    decide

private theorem word_toNat_xor (a b : UInt256) :
    (UInt256.xor a b).toNat = a.toNat ^^^ b.toNat := by
  change (a.val ^^^ b.val).val = _
  rw [Fin.xor_val]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le
    (Nat.xor_lt_two_pow a.val.isLt b.val.isLt) (by rfl)

theorem wordXor_eq_zero_iff (a b : UInt256) :
    UInt256.xor a b = 0 ↔ a = b := by
  constructor
  · intro h
    apply Challenge.EvmProof.Word.word_ext
    apply Nat.eq_of_xor_eq_zero
    rw [← word_toNat_xor, h]
    rfl
  · rintro rfl
    apply Challenge.EvmProof.Word.word_ext
    rw [word_toNat_xor, Nat.xor_self]
    rfl

/-- Sequential accumulator: each check ORs the XOR of a calldata word with its
expected constant into the accumulator. -/
def scanDiff (input : ByteArray) : List (Nat × UInt256) → UInt256 → UInt256
  | [], acc => acc
  | p :: ps, acc =>
      scanDiff input ps (UInt256.lor
        (UInt256.xor (MachineState.readWord input p.1) p.2) acc)

/-- The first check seeds the accumulator; the rest are ORed in. -/
def guardDiff (checks : List (Nat × UInt256)) (input : ByteArray) : UInt256 :=
  match checks with
  | [] => 0
  | c :: cs => scanDiff input cs (UInt256.xor (MachineState.readWord input c.1) c.2)

def WordsMatch (checks : List (Nat × UInt256)) (input : ByteArray) : Prop :=
  ∀ p, p ∈ checks → MachineState.readWord input p.1 = p.2

private theorem scanDiff_eq_zero_iff (input : ByteArray)
    (xs : List (Nat × UInt256)) (acc : UInt256) :
    scanDiff input xs acc = 0 ↔
      acc = 0 ∧ ∀ p, p ∈ xs → MachineState.readWord input p.1 = p.2 := by
  induction xs generalizing acc with
  | nil => simp [scanDiff]
  | cons p ps ih =>
      rw [scanDiff, ih]
      simp only [wordOr_eq_zero_iff, wordXor_eq_zero_iff,
        List.mem_cons, forall_eq_or_imp]
      aesop

theorem guardDiff_eq_zero_iff (checks : List (Nat × UInt256)) (input : ByteArray) :
    guardDiff checks input = 0 ↔ WordsMatch checks input := by
  cases checks with
  | nil => simp [guardDiff, WordsMatch]
  | cons c cs =>
      rw [guardDiff, scanDiff_eq_zero_iff]
      simp only [wordXor_eq_zero_iff, WordsMatch, List.mem_cons, forall_eq_or_imp]

theorem isZero_of_eq (a : UInt256) (h : a = 0) :
    UInt256.isZero a = UInt256.ofNat 1 := by rw [h]; decide

theorem isZero_of_ne (a : UInt256) (h : a ≠ 0) :
    UInt256.isZero a = UInt256.ofNat 0 := by
  have hnat : a.toNat ≠ 0 := by
    intro hz
    apply h
    apply Challenge.EvmProof.Word.word_ext
    rw [show (0 : UInt256).toNat = 0 by decide]
    exact hz
  simp [UInt256.isZero, hnat]

theorem toNat_ofNat_self {a : Nat} (ha : a < 2 ^ 256) :
    (UInt256.ofNat a).toNat = a := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem isZero_ofNat_of_ne {a : Nat} (ha : a < 2 ^ 256) (h : a ≠ 0) :
    UInt256.isZero (UInt256.ofNat a) = UInt256.ofNat 0 := by
  rw [UInt256.isZero, toNat_ofNat_self ha, if_neg h]

theorem isZero_ofNat_of_eq {a : Nat} (h : a = 0) :
    UInt256.isZero (UInt256.ofNat a) = UInt256.ofNat 1 := by
  rw [h]; decide

theorem eq_ofNat_of_ne {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (h : b ≠ a) :
    UInt256.eq (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat 0 := by
  rw [UInt256.eq, toNat_ofNat_self ha, toNat_ofNat_self hb, if_neg (Ne.symm h)]

theorem eq_ofNat_of_eq {a b : Nat} (h : b = a) :
    UInt256.eq (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat 1 := by
  rw [h, UInt256.eq, if_pos rfl]

theorem isTrue_one : UInt256.isTrue (UInt256.ofNat 1) := by decide

theorem not_isTrue_zero : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide

/-! ## From matched words to decoded operands -/

theorem byte_eq_of_words (input target : ByteArray) (p : Nat)
    (h : MachineState.readWord input (32 * (p / 32)) =
      MachineState.readWord target (32 * (p / 32))) :
    YulSemantics.EVM.byteFrom input.toList p =
      YulSemantics.EVM.byteFrom target.toList p := by
  have hlt : p % 32 < 32 := Nat.mod_lt _ (by omega)
  have h1 := Challenge.EvmProof.Bytes.byteAt_readWord input (32 * (p / 32)) (p % 32) hlt
  have h2 := Challenge.EvmProof.Bytes.byteAt_readWord target (32 * (p / 32)) (p % 32) hlt
  rw [h] at h1
  rw [Nat.div_add_mod p 32] at h1 h2
  have h3 := congrArg UInt256.toNat (h1.symm.trans h2)
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt _) (by norm_num)),
    Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt _) (by norm_num))] at h3
  exact UInt8.toNat.inj h3

theorem bytesToNatPadded_eq_of_words (input target : ByteArray) (off len : Nat)
    (hw : ∀ k, 32 * k < off + len →
      MachineState.readWord input (32 * k) = MachineState.readWord target (32 * k)) :
    Precompile.bytesToNatPadded input off len =
      Precompile.bytesToNatPadded target off len := by
  induction len with
  | zero => simp
  | succ n ih =>
      rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ,
        Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
      rw [ih (fun k hk => hw k (by omega))]
      rw [byte_eq_of_words input target (off + n) (hw _ (by omega))]

theorem bytesToNatPadded_eq_of_checks (input target : ByteArray)
    (checks : List (Nat × UInt256)) (off len : Nat)
    (hm : WordsMatch checks input)
    (hcover : ∀ k, 32 * k < off + len →
      (32 * k, MachineState.readWord target (32 * k)) ∈ checks) :
    Precompile.bytesToNatPadded input off len =
      Precompile.bytesToNatPadded target off len :=
  bytesToNatPadded_eq_of_words input target off len
    (fun k hk => hm (32 * k, MachineState.readWord target (32 * k)) (hcover k hk))

theorem eq_empty_of_size_eq_zero (input : ByteArray) (h : input.size = 0) :
    input = ByteArray.empty := by
  cases input with
  | mk data =>
      have hd : data = #[] := Array.eq_empty_of_size_eq_zero h
      subst hd
      rfl

end Challenge.Modexp.Submission.Proofs.Memo.Logic
