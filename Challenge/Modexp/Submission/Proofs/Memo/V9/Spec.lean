import Challenge.Modexp.Submission.Proofs.Memo.V9.Data
import Challenge.Modexp.Submission.Proofs.Algorithm
import Mathlib.Tactic.ReduceModChar

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Memo.V9.Spec

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
    Precompile.bytesToNatPadded input 96 32 = 5964364953636342908918930162962566239787286640968493902593843747347131818633 := by
  rw [Logic.bytesToNatPadded_eq_of_checks input target checks 96 32 hm
    (fun k hk => cover k (by omega))]
  decide +kernel

theorem exp_eq {input : ByteArray} (hm : WordsMatch checks input) :
    Precompile.bytesToNatPadded input 128 32 = 21888242871839275222246405745257275088696311157297823662689037894645226208581 := by
  rw [Logic.bytesToNatPadded_eq_of_checks input target checks 128 32 hm
    (fun k hk => cover k (by omega))]
  decide +kernel

theorem mod_eq {input : ByteArray} (hm : WordsMatch checks input) :
    Precompile.bytesToNatPadded input 160 32 = 21888242871839275222246405745257275088696311157297823662689037894645226208583 := by
  rw [Logic.bytesToNatPadded_eq_of_checks input target checks 160 32 hm
    (fun k hk => cover k (by omega))]
  decide +kernel

theorem cert : Precompile.modPow 5964364953636342908918930162962566239787286640968493902593843747347131818633 21888242871839275222246405745257275088696311157297823662689037894645226208581 21888242871839275222246405745257275088696311157297823662689037894645226208583 = 6720979588572738974916628410083100159223021409556719026881700545747062357561 := by
  rw [Challenge.Modexp.Submission.Proofs.Algorithm.modPow_eq, if_neg (by norm_num)]
  have h : ((5964364953636342908918930162962566239787286640968493902593843747347131818633 : ℕ) : ZMod 21888242871839275222246405745257275088696311157297823662689037894645226208583) ^ 21888242871839275222246405745257275088696311157297823662689037894645226208581 = ((6720979588572738974916628410083100159223021409556719026881700545747062357561 : ℕ) : ZMod 21888242871839275222246405745257275088696311157297823662689037894645226208583) := by
    reduce_mod_char
  have h2 := congrArg ZMod.val h
  rw [← Nat.cast_pow, ZMod.val_natCast, ZMod.val_natCast] at h2
  rw [h2]

theorem spec_eq {input : ByteArray} (hm : WordsMatch checks input) :
    spec input = Precompile.natToBytes 6720979588572738974916628410083100159223021409556719026881700545747062357561 32 := by
  obtain ⟨hb, he, hmm⟩ := sizes hm
  simp only [spec, hb, he, hmm, base_eq hm, exp_eq hm, mod_eq hm, cert]
  rw [if_neg (by decide)]

end Challenge.Modexp.Submission.Proofs.Memo.V9.Spec
