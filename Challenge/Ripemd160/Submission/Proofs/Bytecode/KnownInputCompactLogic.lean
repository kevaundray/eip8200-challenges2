import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactState
import Challenge.EvmProof.Bytes

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactLogic

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

theorem loopAcc_zero_iff (input : ByteArray) (n : Nat) :
    loopAcc input n = 0 ↔
      referenceWord input = KnownInputData.fullWord ∧
      ∀ j, j ≤ n → MachineState.readWord input (32 * j) =
        KnownInputData.fullWord := by
  induction n with
  | zero =>
      simp only [loopAcc, KnownInputLogic.wordXor_eq_zero_iff]
      constructor
      · intro href
        refine ⟨href, ?_⟩
        intro j hj
        have : j = 0 := by omega
        subst j
        simpa [referenceWord] using href
      · rintro ⟨href, _⟩
        exact href
  | succ n ih =>
      rw [loopAcc, KnownInputLogic.wordOr_eq_zero_iff,
        KnownInputLogic.wordXor_eq_zero_iff, ih]
      constructor
      · rintro ⟨hnext, href, hprev⟩
        refine ⟨href, ?_⟩
        intro j hj
        by_cases heq : j = n + 1
        · subst j
          exact hnext.trans href
        · exact hprev j (by omega)
      · rintro ⟨href, hall⟩
        exact ⟨(hall (n + 1) (by omega)).trans href.symm,
          href, fun j hj => hall j (by omega)⟩

private theorem tailBytes_zero (input : ByteArray) (hsize : input.size = 1000) :
    EVM.Precompile.bytesToNatPadded input 1000 24 = 0 := by
  unfold EVM.Precompile.bytesToNatPadded
  simp [MachineState.readPadded, hsize, Data.Bytes.bytesToBigEndianNat,
    Challenge.EvmProof.Bytecode.toList_eq_data, Array.toList_replicate,
    List.replicate_succ]

theorem finalWord_of_size_shift (input : ByteArray)
    (hsize : input.size = 1000)
    (hshift : UInt256.shiftRight (MachineState.readWord input 992)
        (UInt256.ofNat 192) =
      UInt256.shiftRight KnownInputData.fullWord (UInt256.ofNat 192)) :
    MachineState.readWord input 992 = KnownInputData.finalWord := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat]
  rw [Challenge.EvmProof.Bytes.bytesToNatPadded_add input 992 8 24,
    tailBytes_zero input hsize, Nat.add_zero]
  have hread := Challenge.EvmProof.Bytes.shiftRight_readWord input 992 8
    (by omega) (by omega)
  have hfull : UInt256.shiftRight KnownInputData.fullWord (UInt256.ofNat 192) =
      UInt256.ofNat 7016996765293437281 := by
    decide
  rw [hshift, hfull] at hread
  have hnat := congrArg UInt256.toNat hread
  have hbytesLt : EVM.Precompile.bytesToNatPadded input 992 8 < 2 ^ 256 :=
    (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 992 8).trans_le
      (by norm_num)
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num), Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hbytesLt] at hnat
  rw [← hnat]
  norm_num [KnownInputData.finalWord,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem finalAcc_zero_iff_matches (input : ByteArray)
    (hsize : input.size = 1000) :
    finalAcc input = 0 ↔ KnownInputLogic.Matches input := by
  rw [finalAcc, KnownInputLogic.wordOr_eq_zero_iff,
    KnownInputLogic.wordXor_eq_zero_iff, loopAcc_zero_iff]
  constructor
  · rintro ⟨htail, href, hwords⟩
    refine ⟨hsize, ?_⟩
    intro i hi
    by_cases hilast : i = 31
    · subst i
      rw [KnownInputData.expectedWord, if_neg (by omega)]
      exact finalWord_of_size_shift input hsize
        (htail.trans (congrArg (fun w => UInt256.shiftRight w
          (UInt256.ofNat 192)) href))
    · rw [KnownInputData.expectedWord, if_pos (by omega)]
      exact hwords i (by omega)
  · rintro ⟨_, hwords⟩
    have href : referenceWord input = KnownInputData.fullWord := by
      have hw0 := hwords 0 (by omega)
      rw [KnownInputData.expectedWord, if_pos (by omega)] at hw0
      simpa [referenceWord] using hw0
    refine ⟨?_, href, ?_⟩
    · rw [href]
      have hlast := hwords 31 (by omega)
      rw [KnownInputData.expectedWord, if_neg (by omega)] at hlast
      rw [hlast]
      decide
    · intro j hj
      have hw := hwords j (by omega)
      rw [KnownInputData.expectedWord, if_pos (by omega)] at hw
      exact hw

theorem finalAcc_zero_iff_target (input : ByteArray)
    (hsize : input.size = 1000) :
    finalAcc input = 0 ↔ input = KnownInputData.targetInput := by
  rw [finalAcc_zero_iff_matches input hsize]
  constructor
  · exact KnownInputLogic.matches_eq_targetInput input
  · intro h
    subst input
    exact ⟨KnownInputData.targetInput_size,
      KnownInputData.targetInput_readWord⟩

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactLogic
