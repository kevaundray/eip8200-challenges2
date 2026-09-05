import Challenge.Modexp.Submission.Proofs.Memo.V3.Data
import Challenge.Modexp.Submission.Proofs.Algorithm
import Mathlib.Tactic.ReduceModChar

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Memo.V3.Spec

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Data

theorem sizes {input : ByteArray} (hm : WordsMatch checks input) :
    baseSize input = 1 ∧ exponentSize input = 1 ∧ modulusSize input = 0 := by
  have h0 := hm (0, 1) (by simp [checks])
  have h1 := hm (32, 1) (by simp [checks])
  have h2 := hm (64, 0) (by simp [checks])
  refine ⟨?_, ?_, ?_⟩
  · show Precompile.bytesToNatPadded input 0 32 = 1
    rw [← Challenge.EvmProof.Bytes.readWord_toNat, h0]; decide +kernel
  · show Precompile.bytesToNatPadded input 32 32 = 1
    rw [← Challenge.EvmProof.Bytes.readWord_toNat, h1]; decide +kernel
  · show Precompile.bytesToNatPadded input 64 32 = 0
    rw [← Challenge.EvmProof.Bytes.readWord_toNat, h2]; decide +kernel

theorem spec_eq {input : ByteArray} (hm : WordsMatch checks input) :
    spec input = ByteArray.empty := by
  obtain ⟨hb, he, hmm⟩ := sizes hm
  simp only [spec, hb, he, hmm]
  rw [if_pos trivial]

end Challenge.Modexp.Submission.Proofs.Memo.V3.Spec
