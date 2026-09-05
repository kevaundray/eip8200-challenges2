import Challenge.Modexp.Submission.Proofs.Memo.V10.Data
import Challenge.Modexp.Submission.Proofs.Algorithm
import Mathlib.Tactic.ReduceModChar

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Memo.V10.Spec

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Data

theorem sizes {input : ByteArray} (hm : WordsMatch checks input) :
    baseSize input = 32 ∧ exponentSize input = 32 ∧ modulusSize input = 32 := by
  have h0 := hm (0, 32) (by simp [checks])
  have h1 := hm (32, 32) (by simp [checks])
  have h2 := hm (64, 32) (by simp [checks])
  refine ⟨?_, ?_, ?_⟩
  · show Precompile.bytesToNatPadded input 0 32 = 32
    rw [← Challenge.EvmProof.Bytes.readWord_toNat, h0]; decide +kernel
  · show Precompile.bytesToNatPadded input 32 32 = 32
    rw [← Challenge.EvmProof.Bytes.readWord_toNat, h1]; decide +kernel
  · show Precompile.bytesToNatPadded input 64 32 = 32
    rw [← Challenge.EvmProof.Bytes.readWord_toNat, h2]; decide +kernel

theorem cover : ∀ k, k < 6 → (32 * k, MachineState.readWord target (32 * k)) ∈ checks := by
  decide +kernel

theorem base_eq {input : ByteArray} (hm : WordsMatch checks input) :
    Precompile.bytesToNatPadded input 96 32 = 73247641362558725300106169323372519318985509881989093824173738694050148637181 := by
  rw [Logic.bytesToNatPadded_eq_of_checks input target checks 96 32 hm
    (fun k hk => cover k (by omega))]
  decide +kernel

theorem exp_eq {input : ByteArray} (hm : WordsMatch checks input) :
    Precompile.bytesToNatPadded input 128 32 = 107030225122685690860854567356650508129575789004208118976667082798060876470593 := by
  rw [Logic.bytesToNatPadded_eq_of_checks input target checks 128 32 hm
    (fun k hk => cover k (by omega))]
  decide +kernel

theorem mod_eq {input : ByteArray} (hm : WordsMatch checks input) :
    Precompile.bytesToNatPadded input 160 32 = 79568444699642415239743437990266002771108086772465743382105228099042951533477 := by
  rw [Logic.bytesToNatPadded_eq_of_checks input target checks 160 32 hm
    (fun k hk => cover k (by omega))]
  decide +kernel

theorem cert : Precompile.modPow 73247641362558725300106169323372519318985509881989093824173738694050148637181 107030225122685690860854567356650508129575789004208118976667082798060876470593 79568444699642415239743437990266002771108086772465743382105228099042951533477 = 77255142867349968861277780612024794038450510315495465888110079858626436939207 := by
  rw [Challenge.Modexp.Submission.Proofs.Algorithm.modPow_eq, if_neg (by norm_num)]
  have h : ((73247641362558725300106169323372519318985509881989093824173738694050148637181 : ℕ) : ZMod 79568444699642415239743437990266002771108086772465743382105228099042951533477) ^ 107030225122685690860854567356650508129575789004208118976667082798060876470593 = ((77255142867349968861277780612024794038450510315495465888110079858626436939207 : ℕ) : ZMod 79568444699642415239743437990266002771108086772465743382105228099042951533477) := by
    reduce_mod_char
  have h2 := congrArg ZMod.val h
  rw [← Nat.cast_pow, ZMod.val_natCast, ZMod.val_natCast] at h2
  rw [h2]

theorem spec_eq {input : ByteArray} (hm : WordsMatch checks input) :
    spec input = Precompile.natToBytes 77255142867349968861277780612024794038450510315495465888110079858626436939207 32 := by
  obtain ⟨hb, he, hmm⟩ := sizes hm
  simp only [spec, hb, he, hmm, base_eq hm, exp_eq hm, mod_eq hm, cert]
  rw [if_neg (by decide)]

end Challenge.Modexp.Submission.Proofs.Memo.V10.Spec
