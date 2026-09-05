import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardData
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word
import Batteries.Data.Nat.Bitwise.Lemmas
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

/-!
# Pure logic for the exact `1000 a's` guard

This file models the bytecode's XOR/OR accumulator and, independently of any
particular instruction trace, proves that the size check plus all 32 padded
word checks characterize exactly `ExactGuardData.targetInput`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardLogic

open EvmSemantics
open EvmSemantics.EVM
open ExactGuardData

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

/-- Sequential XOR/OR accumulator used by the 32 word comparisons. -/
def scanDiff (input : ByteArray) : List (Nat × UInt256) → UInt256 → UInt256
  | [], acc => acc
  | p :: ps, acc =>
      scanDiff input ps (UInt256.lor
        (UInt256.xor (MachineState.readWord input p.1) p.2) acc)

/-- The complete size-and-contents guard difference. -/
def guardDiff (input : ByteArray) : UInt256 :=
  scanDiff input checks
    (UInt256.lor
      (UInt256.xor (UInt256.ofNat input.size) (UInt256.ofNat 1000)) 0)

/-- Declarative form of the runtime guard. -/
def Matches (input : ByteArray) : Prop :=
  input.size = 1000 ∧
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

theorem guardDiff_eq_zero_iff (input : ByteArray)
    (hbound : input.size < 2 ^ 256) :
    guardDiff input = 0 ↔ Matches input := by
  rw [guardDiff, scanDiff_eq_zero_iff]
  simp only [wordOr_eq_zero_iff, wordXor_eq_zero_iff, and_true, Matches]
  constructor
  · rintro ⟨hsize, hwords⟩
    constructor
    · have hnat := congrArg UInt256.toNat hsize
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat] at hnat
      rw [Nat.mod_eq_of_lt hbound] at hnat
      norm_num at hnat ⊢
      exact hnat
    · exact hwords
  · rintro ⟨hsize, hwords⟩
    constructor
    · rw [hsize]
    · exact hwords

/-- Reuse the promoted frontier's byte-level characterization. -/
theorem matches_iff_eq_targetInput (input : ByteArray) :
    Matches input ↔ input = targetInput := by
  constructor
  · rintro ⟨hsize, hwords⟩
    apply KnownInputLogic.matches_eq_targetInput input
    refine ⟨hsize, ?_⟩
    intro i hi
    exact hwords (32 * i, expectedWord i) (check_mem i hi)
  · intro hinput
    subst input
    refine ⟨targetInput_size, ?_⟩
    intro p hp
    rw [checks] at hp
    rcases List.mem_map.mp hp with ⟨i, hi, rfl⟩
    exact targetInput_readWord i (List.mem_range.mp hi)

/-- Runtime accumulator form of the same exact-input characterization. -/
theorem guardDiff_eq_zero_iff_targetInput (input : ByteArray)
    (hbound : input.size < 2 ^ 256) :
    guardDiff input = 0 ↔ input = targetInput :=
  (guardDiff_eq_zero_iff input hbound).trans
    (matches_iff_eq_targetInput input)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardLogic
