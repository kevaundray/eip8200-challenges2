import Challenge.Modexp.Submission.Proofs.Memo.V4.Data
import Challenge.Modexp.Submission.Proofs.Algorithm
import Mathlib.Tactic.ReduceModChar

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Memo.V4.Spec

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Data

theorem sizes {input : ByteArray} (hm : WordsMatch checks input) :
    baseSize input = 1 ∧ exponentSize input = 1 ∧ modulusSize input = 12 := by
  have h0 := hm (0, 1) (by simp [checks])
  have h1 := hm (32, 1) (by simp [checks])
  have h2 := hm (64, 12) (by simp [checks])
  refine ⟨?_, ?_, ?_⟩
  · show Precompile.bytesToNatPadded input 0 32 = 1
    rw [← Challenge.EvmProof.Bytes.readWord_toNat, h0]; decide +kernel
  · show Precompile.bytesToNatPadded input 32 32 = 1
    rw [← Challenge.EvmProof.Bytes.readWord_toNat, h1]; decide +kernel
  · show Precompile.bytesToNatPadded input 64 32 = 12
    rw [← Challenge.EvmProof.Bytes.readWord_toNat, h2]; decide +kernel

theorem cover : ∀ k, k < 4 → (32 * k, MachineState.readWord target (32 * k)) ∈ checks := by
  decide +kernel

theorem base_eq {input : ByteArray} (hm : WordsMatch checks input) :
    Precompile.bytesToNatPadded input 96 1 = 42 := by
  rw [Logic.bytesToNatPadded_eq_of_checks input target checks 96 1 hm
    (fun k hk => cover k (by omega))]
  decide +kernel

theorem exp_eq {input : ByteArray} (hm : WordsMatch checks input) :
    Precompile.bytesToNatPadded input 97 1 = 7 := by
  rw [Logic.bytesToNatPadded_eq_of_checks input target checks 97 1 hm
    (fun k hk => cover k (by omega))]
  decide +kernel

theorem mod_eq {input : ByteArray} (hm : WordsMatch checks input) :
    Precompile.bytesToNatPadded input 98 12 = 0 := by
  rw [Logic.bytesToNatPadded_eq_of_checks input target checks 98 12 hm
    (fun k hk => cover k (by omega))]
  decide +kernel

theorem cert : Precompile.modPow 42 7 0 = 0 := by
  simp [Challenge.Modexp.Submission.Proofs.Algorithm.modPow_eq]

theorem spec_eq {input : ByteArray} (hm : WordsMatch checks input) :
    spec input = Precompile.natToBytes 0 12 := by
  obtain ⟨hb, he, hmm⟩ := sizes hm
  simp only [spec, hb, he, hmm, base_eq hm, exp_eq hm, mod_eq hm, cert]
  rw [if_neg (by decide)]

end Challenge.Modexp.Submission.Proofs.Memo.V4.Spec
