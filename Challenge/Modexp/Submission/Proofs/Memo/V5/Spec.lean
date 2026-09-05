import Challenge.Modexp.Submission.Proofs.Memo.V5.Data
import Challenge.Modexp.Submission.Proofs.Algorithm
import Mathlib.Tactic.ReduceModChar

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Memo.V5.Spec

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Data

theorem sizes {input : ByteArray} (hm : WordsMatch checks input) :
    baseSize input = 1 ∧ exponentSize input = 32 ∧ modulusSize input = 32 := by
  have h0 := hm (0, 1) (by simp [checks])
  have h1 := hm (32, 32) (by simp [checks])
  have h2 := hm (64, 32) (by simp [checks])
  refine ⟨?_, ?_, ?_⟩
  · show Precompile.bytesToNatPadded input 0 32 = 1
    rw [← Challenge.EvmProof.Bytes.readWord_toNat, h0]; decide +kernel
  · show Precompile.bytesToNatPadded input 32 32 = 32
    rw [← Challenge.EvmProof.Bytes.readWord_toNat, h1]; decide +kernel
  · show Precompile.bytesToNatPadded input 64 32 = 32
    rw [← Challenge.EvmProof.Bytes.readWord_toNat, h2]; decide +kernel

theorem cover : ∀ k, k < 6 → (32 * k, MachineState.readWord target (32 * k)) ∈ checks := by
  decide +kernel

theorem base_eq {input : ByteArray} (hm : WordsMatch checks input) :
    Precompile.bytesToNatPadded input 96 1 = 3 := by
  rw [Logic.bytesToNatPadded_eq_of_checks input target checks 96 1 hm
    (fun k hk => cover k (by omega))]
  decide +kernel

theorem exp_eq {input : ByteArray} (hm : WordsMatch checks input) :
    Precompile.bytesToNatPadded input 97 32 = 115792089237316195423570985008687907853269984665640564039457584007908834671662 := by
  rw [Logic.bytesToNatPadded_eq_of_checks input target checks 97 32 hm
    (fun k hk => cover k (by omega))]
  decide +kernel

theorem mod_eq {input : ByteArray} (hm : WordsMatch checks input) :
    Precompile.bytesToNatPadded input 129 32 = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  rw [Logic.bytesToNatPadded_eq_of_checks input target checks 129 32 hm
    (fun k hk => cover k (by omega))]
  decide +kernel

theorem cert : Precompile.modPow 3 115792089237316195423570985008687907853269984665640564039457584007908834671662 115792089237316195423570985008687907853269984665640564039457584007908834671663 = 1 := by
  rw [Challenge.Modexp.Submission.Proofs.Algorithm.modPow_eq, if_neg (by norm_num)]
  have h : ((3 : ℕ) : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ^ 115792089237316195423570985008687907853269984665640564039457584007908834671662 = ((1 : ℕ) : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) := by
    reduce_mod_char
  have h2 := congrArg ZMod.val h
  rw [← Nat.cast_pow, ZMod.val_natCast, ZMod.val_natCast] at h2
  rw [h2]

theorem spec_eq {input : ByteArray} (hm : WordsMatch checks input) :
    spec input = Precompile.natToBytes 1 32 := by
  obtain ⟨hb, he, hmm⟩ := sizes hm
  simp only [spec, hb, he, hmm, base_eq hm, exp_eq hm, mod_eq hm, cert]
  rw [if_neg (by decide)]

end Challenge.Modexp.Submission.Proofs.Memo.V5.Spec
