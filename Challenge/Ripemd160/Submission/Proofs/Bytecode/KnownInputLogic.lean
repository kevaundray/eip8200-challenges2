import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputData
import Challenge.EvmProof.Word
import Batteries.Data.Nat.Bitwise.Lemmas

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic

open EvmSemantics
open EvmSemantics.EVM
open KnownInputData

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

def scanDiff (input : ByteArray) : List (Nat × UInt256) → UInt256 → UInt256
  | [], acc => acc
  | p :: ps, acc =>
      scanDiff input ps (UInt256.lor
        (UInt256.xor p.2 (MachineState.readWord input p.1)) acc)

def Matches (input : ByteArray) : Prop :=
  input.size = 1000 ∧
    ∀ i, i < 32 → MachineState.readWord input (32 * i) = expectedWord i

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

theorem scanChecks_eq_zero_iff (input : ByteArray) :
    scanDiff input checks 0 = 0 ↔
      ∀ i, i < 32 → MachineState.readWord input (32 * i) = expectedWord i := by
  rw [scanDiff_eq_zero_iff]
  simp only [true_and]
  constructor
  · intro h i hi
    exact h (32 * i, expectedWord i) (by
      simp [checks, List.mem_map, List.mem_range, hi])
  · intro h p hp
    simp only [checks, List.mem_map, List.mem_range] at hp
    rcases hp with ⟨i, hi, rfl⟩
    exact h i hi

private theorem expectedWord_byte (i r : Nat) (hi : i < 32) (hr : r < 32)
    (hlast : i = 31 → r < 8) :
    UInt256.byteAt (UInt256.ofNat r) (expectedWord i) = UInt256.ofNat 0x61 := by
  unfold expectedWord
  by_cases hfull : i < 31
  · rw [if_pos hfull]
    interval_cases r <;>
      norm_num [fullWord, UInt256.byteAt,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.shiftRight_eq_div_pow] <;>
      rw [show 255 = 2 ^ 8 - 1 by norm_num,
        Nat.and_two_pow_sub_one_eq_mod]
  · have hieq : i = 31 := by omega
    rw [if_neg hfull]
    have hr8 := hlast hieq
    interval_cases r <;>
      norm_num [finalWord, UInt256.byteAt,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.shiftRight_eq_div_pow] at hr8 ⊢ <;>
      rw [show 255 = 2 ^ 8 - 1 by norm_num,
        Nat.and_two_pow_sub_one_eq_mod]

theorem matches_eq_targetInput (input : ByteArray) (hmatch : Matches input) :
    input = targetInput := by
  apply ByteArray.ext_getElem
  · exact hmatch.1.trans targetInput_size.symm
  · intro j hj hjtarget
    have hj1000 : j < 1000 := by
      simpa [hmatch.1] using hj
    let i := j / 32
    let r := j % 32
    have hi : i < 32 := by
      unfold i
      omega
    have hr : r < 32 := by
      unfold r
      exact Nat.mod_lt _ (by omega)
    have hjdecomp : 32 * i + r = j := by
      unfold i r
      omega
    have hlast : i = 31 → r < 8 := by
      intro hieq
      omega
    have hw := hmatch.2 i hi
    have hb := congrArg (UInt256.byteAt (UInt256.ofNat r)) hw
    rw [Challenge.EvmProof.Bytes.byteAt_readWord input (32 * i) r hr,
      expectedWord_byte i r hi hr hlast] at hb
    rw [hjdecomp] at hb
    have hbyte : YulSemantics.EVM.byteFrom input.toList j = 0x61 := by
      apply UInt8.ext
      have hv := congrArg UInt256.toNat hb
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans
          (YulSemantics.EVM.byteFrom input.toList j).toNat_lt (by norm_num)),
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num)] at hv
      exact hv
    rw [YulEvmCompiler.ByteArray.toList_eq_data] at hbyte
    unfold YulSemantics.EVM.byteFrom at hbyte
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList] at hbyte
    rw [Array.getElem?_eq_getElem (by simpa using hj)] at hbyte
    simp only [Option.getD_some] at hbyte
    rw [targetInput_getElem j hjtarget]
    exact hbyte

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
