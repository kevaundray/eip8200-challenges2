import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleActiveWords
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# Active-memory endpoint for the dense schedule

The dense schedule keeps the three-word warmup and replaces the sixteen
schedule-slot stores by the two stores at byte offsets 672 and 704.  This
module proves the active-word result from those direct lists.  It does not
claim that the corresponding memory bytes are equal.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleActiveWords

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

private theorem ofNat_toNat (w : UInt256) : UInt256.ofNat w.toNat = w := by
  cases w with
  | mk val => simp [UInt256.ofNat, UInt256.toNat, UInt256.size]

private theorem activeWordsAfter_eq_of_end_le (curr offset size : Nat)
    (hend : offset + size ≤ curr * 32) :
    MachineState.activeWordsAfter curr offset size = curr := by
  unfold MachineState.activeWordsAfter
  split
  · rfl
  · dsimp only
    apply Nat.max_eq_left
    have hq : (offset + size - 1) / 32 < curr :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega

def activeAfterWord (current offset : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.activeWordsAfter current.toNat offset.toNat 32)

private theorem activeAfterWord_toNat (current offset : UInt256)
    (hlt : MachineState.activeWordsAfter current.toNat offset.toNat 32 <
      2 ^ 256) :
    (activeAfterWord current offset).toNat =
      MachineState.activeWordsAfter current.toNat offset.toNat 32 := by
  unfold activeAfterWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlt]

private theorem activeAfterWord_eq (current offset : UInt256)
    (hend : offset.toNat + 32 ≤ current.toNat * 32) :
    activeAfterWord current offset = current := by
  unfold activeAfterWord
  rw [activeWordsAfter_eq_of_end_le _ _ _ hend]
  exact ofNat_toNat current

def loadedActiveWords (s : State) (messageOffset : UInt256) : UInt256 :=
  let a0 := activeAfterWord s.activeWords messageOffset
  activeAfterWord a0 (messageOffset + UInt256.ofNat 32)

def storeActiveWords (current : UInt256) (addresses : List Nat) : UInt256 :=
  addresses.foldl
    (fun current address => activeAfterWord current (UInt256.ofNat address)) current

def expectedActiveWords (s : State) (messageOffset : UInt256) : UInt256 :=
  storeActiveWords (loadedActiveWords s messageOffset) [704, 672]

theorem storeActiveWords_704_672 (current : UInt256)
    (hcurrent : 23 ≤ current.toNat) :
    storeActiveWords current [704, 672] = current := by
  have h672 : (UInt256.ofNat 672).toNat + 32 ≤ current.toNat * 32 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num : (672 : Nat) < 2 ^ 256)]
    omega
  have h704 : (UInt256.ofNat 704).toNat + 32 ≤ current.toNat * 32 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num : (704 : Nat) < 2 ^ 256)]
    omega
  simp only [storeActiveWords, List.foldl]
  rw [activeAfterWord_eq current (UInt256.ofNat 704) h704]
  rw [activeAfterWord_eq current (UInt256.ofNat 672) h672]

theorem storeActiveWords_loaded_eq (s : State) (messageOffset : UInt256)
    (hcurrent : 23 ≤ (loadedActiveWords s messageOffset).toNat) :
    storeActiveWords (loadedActiveWords s messageOffset) [704, 672] =
      loadedActiveWords s messageOffset :=
  storeActiveWords_704_672 _ hcurrent

private theorem message_bounds (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < DriverTrace.blockCount input) :
    Padding.messageOffset + 64 * i < 2 ^ 256 ∧
    Padding.messageOffset + 64 * i + 32 < 2 ^ 256 ∧
    65 + 2 * i < 2 ^ 256 ∧
    66 + 2 * i < 2 ^ 256 ∧
    (Padding.messageOffset + 64 * i + 32 - 1) / 32 + 1 =
      65 + 2 * i ∧
    (Padding.messageOffset + 64 * i + 32 + 32 - 1) / 32 + 1 =
      66 + 2 * i := by
  have hpadded := Padding.paddedLength_lt input.size
  have hoff : 64 * i < Padding.paddedLength input.size := by
    rw [DriverTrace.paddedLength_eq_blockCount input]
    omega
  have hsize : input.size < 2 ^ 64 := by
    simpa [CalldataFits] using hfit
  have hp : Padding.messageOffset + 64 * i < 2 ^ 256 := by
    norm_num [Padding.messageOffset] at hsize ⊢
    omega
  have hp32 : Padding.messageOffset + 64 * i + 32 < 2 ^ 256 := by
    change 2048 + 64 * i + 32 < 2 ^ 256
    omega
  have htarget0 : 65 + 2 * i < 2 ^ 256 := by
    norm_num [Padding.messageOffset] at hsize ⊢
    omega
  have htarget1 : 66 + 2 * i < 2 ^ 256 := by
    norm_num [Padding.messageOffset] at hsize ⊢
    omega
  have hread0 :
      (Padding.messageOffset + 64 * i + 32 - 1) / 32 + 1 =
        65 + 2 * i := by
    norm_num [Padding.messageOffset]
    omega
  have hread1 :
      (Padding.messageOffset + 64 * i + 32 + 32 - 1) / 32 + 1 =
        66 + 2 * i := by
    norm_num [Padding.messageOffset]
    omega
  exact ⟨hp, hp32, htarget0, htarget1, hread0, hread1⟩

private theorem message_words (i : Nat)
    (hp : Padding.messageOffset + 64 * i < 2 ^ 256)
    (hp32 : Padding.messageOffset + 64 * i + 32 < 2 ^ 256) :
    DriverTrace.messageOffsetWord i =
        UInt256.ofNat (Padding.messageOffset + 64 * i) ∧
    (DriverTrace.messageOffsetWord i).toNat =
        Padding.messageOffset + 64 * i ∧
    (DriverTrace.messageOffsetWord i + UInt256.ofNat 32).toNat =
        Padding.messageOffset + 64 * i + 32 := by
  have hmsgWord : DriverTrace.messageOffsetWord i =
      UInt256.ofNat (Padding.messageOffset + 64 * i) := by
    simp [DriverTrace.messageOffsetWord, DriverTrace.blockOffset, Nat.mul_comm]
  have hmsg : (DriverTrace.messageOffsetWord i).toNat =
      Padding.messageOffset + 64 * i := by
    rw [hmsgWord, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hp]
  have hmsg32 :
      (DriverTrace.messageOffsetWord i + UInt256.ofNat 32).toNat =
        Padding.messageOffset + 64 * i + 32 := by
    rw [hmsgWord, Challenge.EvmProof.Word.ofNat_add_ofNat hp32,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hp32]
  exact ⟨hmsgWord, hmsg, hmsg32⟩

private theorem loadedActiveWords_toNat_of_bounds (s : State)
    (messageOffset : UInt256) (p target0 target1 : Nat)
    (hmessage : messageOffset.toNat = p)
    (hmessage32 : (messageOffset + UInt256.ofNat 32).toNat = p + 32)
    (htarget0 : target0 < 2 ^ 256)
    (htarget1 : target1 < 2 ^ 256)
    (hread0 : (p + 32 - 1) / 32 + 1 = target0)
    (hread1 : (p + 32 + 32 - 1) / 32 + 1 = target1)
    (htargetLe : target0 ≤ target1) :
    (loadedActiveWords s messageOffset).toNat =
      max s.activeWords.toNat target1 := by
  have hfirstRaw :
      MachineState.activeWordsAfter s.activeWords.toNat
          messageOffset.toNat 32 =
        max s.activeWords.toNat target0 := by
    rw [hmessage]
    simp only [MachineState.activeWordsAfter, if_neg (by omega : (32 : Nat) ≠ 0)]
    rw [hread0]
  have hfirstLt :
      MachineState.activeWordsAfter s.activeWords.toNat
          messageOffset.toNat 32 < 2 ^ 256 := by
    rw [hfirstRaw]
    exact (Nat.max_lt).2 ⟨s.activeWords.val.isLt, htarget0⟩
  have hfirst :
      (activeAfterWord s.activeWords messageOffset).toNat =
        max s.activeWords.toNat target0 := by
    rw [activeAfterWord_toNat _ _ hfirstLt]
    exact hfirstRaw
  let a0 := activeAfterWord s.activeWords messageOffset
  have ha0 : a0.toNat = max s.activeWords.toNat target0 := by
    dsimp [a0]
    exact hfirst
  have hsecondRaw :
      MachineState.activeWordsAfter a0.toNat
          (messageOffset + UInt256.ofNat 32).toNat 32 =
        max s.activeWords.toNat target1 := by
    rw [hmessage32]
    simp only [MachineState.activeWordsAfter, if_neg (by omega : (32 : Nat) ≠ 0)]
    dsimp
    have hread1' : (p + 63) / 32 + 1 = target1 := by omega
    rw [hread1', ha0]
    change max (max s.activeWords.toNat target0) target1 =
      max s.activeWords.toNat target1
    rw [max_assoc, max_eq_right htargetLe]
  have hsecondLt :
      MachineState.activeWordsAfter a0.toNat
          (messageOffset + UInt256.ofNat 32).toNat 32 < 2 ^ 256 := by
    rw [hsecondRaw]
    exact (Nat.max_lt).2 ⟨s.activeWords.val.isLt, htarget1⟩
  change (activeAfterWord a0 (messageOffset + UInt256.ofNat 32)).toNat = _
  rw [activeAfterWord_toNat _ _ hsecondLt, hsecondRaw]

private theorem loadedActiveWords_toNat (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat)
    (hi : i < DriverTrace.blockCount input) :
    (loadedActiveWords s (DriverTrace.messageOffsetWord i)).toNat =
      max s.activeWords.toNat (66 + 2 * i) := by
  rcases message_bounds input hfit i hi with
    ⟨hp, hp32, htarget0, htarget1, hread0, hread1⟩
  rcases message_words i hp hp32 with
    ⟨_, hmsg, hmsg32⟩
  exact loadedActiveWords_toNat_of_bounds s
    (DriverTrace.messageOffsetWord i) (Padding.messageOffset + 64 * i)
    (65 + 2 * i) (66 + 2 * i) hmsg hmsg32 htarget0 htarget1 hread0 hread1
    (by omega)

theorem expectedActiveWords_toNat (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat)
    (hi : i < DriverTrace.blockCount input) :
    (expectedActiveWords s (DriverTrace.messageOffsetWord i)).toNat =
      max s.activeWords.toNat (66 + 2 * i) := by
  have hloaded := loadedActiveWords_toNat s input hfit i hi
  have hloaded23 : 23 ≤
      (loadedActiveWords s (DriverTrace.messageOffsetWord i)).toNat := by
    rw [hloaded]
    exact (by omega : 23 ≤ 66 + 2 * i).trans (Nat.le_max_right _ _)
  unfold expectedActiveWords
  rw [storeActiveWords_704_672 _ hloaded23, hloaded]

theorem expectedActiveWords_ge_66 (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat)
    (hi : i < DriverTrace.blockCount input) :
    66 ≤ (expectedActiveWords s (DriverTrace.messageOffsetWord i)).toNat := by
  rw [expectedActiveWords_toNat s input hfit i hi]
  omega

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleActiveWords
