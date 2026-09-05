import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Schedule

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 100000

/-!
# Active-memory endpoint of the message schedule

The schedule's last unaligned `MLOAD` is the unique high-water access.  The
sixteen iterations therefore end at word `max current (67 + 2 * block)`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleActiveWords

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

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

private theorem activeWordsAfter_le (curr offset size bound : Nat)
    (hcurr : curr ≤ bound) (hend : offset + size ≤ bound * 32) :
    MachineState.activeWordsAfter curr offset size ≤ bound := by
  unfold MachineState.activeWordsAfter
  split
  · exact hcurr
  · dsimp only
    apply (Nat.max_le).2
    constructor
    · exact hcurr
    have hq : (offset + size - 1) / 32 < bound :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega

private theorem activeWordsAfter_ge (curr offset size : Nat) :
    curr ≤ MachineState.activeWordsAfter curr offset size := by
  unfold MachineState.activeWordsAfter
  split
  · exact Nat.le_refl _
  · exact Nat.le_max_left _ _

private theorem ofNat_toNat (w : UInt256) : UInt256.ofNat w.toNat = w := by
  cases w with
  | mk val => simp [UInt256.ofNat, UInt256.toNat, UInt256.size]

theorem activeWordsAfterUInt256_eq (s : State) (offset size : Nat)
    (hend : offset + size ≤ s.activeWords.toNat * 32) :
    s.activeWordsAfterUInt256 offset size = s.activeWords := by
  rw [State.activeWordsAfterUInt256,
    activeWordsAfter_eq_of_end_le _ _ _ hend, ofNat_toNat]

private theorem activeWordsAfterUInt256_toNat (s : State)
    (offset size : Nat)
    (hlt : MachineState.activeWordsAfter s.activeWords.toNat offset size <
      2 ^ 256) :
    (s.activeWordsAfterUInt256 offset size).toNat =
      MachineState.activeWordsAfter s.activeWords.toNat offset size := by
  rw [State.activeWordsAfterUInt256, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hlt]

private theorem messageLoadOffset (input : ByteArray)
    (hfit : CalldataFits input) (i k : Nat)
    (hi : i < DriverTrace.blockCount input) (hk : k < 16) :
    (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord i) k).toNat =
      Padding.messageOffset + 64 * i + 4 * k := by
  have hpadded := Padding.paddedLength_lt input.size
  have hoff : 64 * i < Padding.paddedLength input.size := by
    rw [DriverTrace.paddedLength_eq_blockCount input]
    omega
  have hload : Padding.messageOffset + 64 * i + 4 * k < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  unfold Schedule.loadOffsetWord DriverTrace.messageOffsetWord
    DriverTrace.blockOffset
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide)
      (by omega : k * 2 ^ 2 < 2 ^ 256)]
  rw [show k * 2 ^ 2 = 4 * k by omega]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega :
      4 * k + (Padding.messageOffset + i * 64) < 2 ^ 256)]
  omega

private theorem xSlotOffset (k : Nat) (hk : k < 16) :
    (Schedule.xSlotWord k).toNat = 0x2a0 + 32 * k := by
  unfold Schedule.xSlotWord
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide)
      (by omega : k * 2 ^ 5 < 2 ^ 256)]
  rw [show k * 2 ^ 5 = 32 * k by omega]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 32 * k + 0x2a0 < 2 ^ 256)]
  omega

private theorem scheduleIteration_activeWords_le (s : State)
    (input : ByteArray) (hfit : CalldataFits input) (block k : Nat)
    (hblock : block < DriverTrace.blockCount input) (hk : k < 16)
    (returnDest : UInt256) (rest : List UInt256) (bound : Nat)
    (hs : s.activeWords.toNat ≤ bound)
    (hbound : 67 + 2 * block ≤ bound) (hlt : bound < 2 ^ 256) :
    (Schedule.afterIteration s (DriverTrace.messageOffsetWord block)
      returnDest rest k).activeWords.toNat ≤ bound := by
  have hload := messageLoadOffset input hfit block k hblock hk
  have hx := xSlotOffset k hk
  let loadedWords := MachineState.activeWordsAfter s.activeWords.toNat
    (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord block) k).toNat 32
  have hloaded : loadedWords ≤ bound := by
    apply activeWordsAfter_le _ _ _ _ hs
    rw [hload]
    simp [Padding.messageOffset]
    omega
  have hloadedLt : loadedWords < 2 ^ 256 := lt_of_le_of_lt hloaded hlt
  let loaded := Schedule.afterRead s (DriverTrace.messageOffsetWord block)
    returnDest rest k
  have hloadedEq : loaded.activeWords.toNat = loadedWords := by
    unfold loaded Schedule.afterRead loadedWords
    exact activeWordsAfterUInt256_toNat s _ _ hloadedLt
  have hstored : MachineState.activeWordsAfter loaded.activeWords.toNat
      (Schedule.xSlotWord k).toNat 32 ≤ bound := by
    apply activeWordsAfter_le _ _ _ _ (by rw [hloadedEq]; exact hloaded)
    rw [hx]
    omega
  have hstoredLt : MachineState.activeWordsAfter loaded.activeWords.toNat
      (Schedule.xSlotWord k).toNat 32 < 2 ^ 256 :=
    lt_of_le_of_lt hstored hlt
  change ((loaded.activeWordsAfterUInt256
    (Schedule.xSlotWord k).toNat 32).toNat ≤ bound)
  rw [activeWordsAfterUInt256_toNat loaded _ _ hstoredLt]
  exact hstored

private theorem scheduleLoopPrefix_activeWords_le (s : State)
    (input : ByteArray) (hfit : CalldataFits input) (block : Nat)
    (hblock : block < DriverTrace.blockCount input)
    (returnDest : UInt256) (rest : List UInt256) (n : Nat) (hn : n ≤ 16) :
    (Schedule.loopState s (DriverTrace.messageOffsetWord block)
      returnDest rest n).activeWords.toNat ≤
      max s.activeWords.toNat (67 + 2 * block) := by
  let bound := max s.activeWords.toNat (67 + 2 * block)
  have hlt : bound < 2 ^ 256 := by
    unfold bound
    exact (Nat.max_lt).2 ⟨s.activeWords.val.isLt, by
      have hpadded := Padding.paddedLength_lt input.size
      have hoff : 64 * block < Padding.paddedLength input.size := by
        rw [DriverTrace.paddedLength_eq_blockCount input]
        omega
      unfold CalldataFits at hfit
      norm_num [Padding.messageOffset] at hfit ⊢
      omega⟩
  have hloop : ∀ n, n ≤ 16 →
      (Schedule.loopState s (DriverTrace.messageOffsetWord block)
        returnDest rest n).activeWords.toNat ≤ bound := by
    intro n hn
    induction n with
    | zero => exact Nat.le_max_left _ _
    | succ n ih =>
        rw [Schedule.loopState]
        apply scheduleIteration_activeWords_le
          (Schedule.loopState s (DriverTrace.messageOffsetWord block)
            returnDest rest n)
          input hfit block n hblock (by omega) returnDest rest bound
          (ih (by omega)) (Nat.le_max_right _ _) hlt
  exact hloop n hn

private theorem scheduleLoop_activeWords_le (s : State)
    (input : ByteArray) (hfit : CalldataFits input) (block : Nat)
    (hblock : block < DriverTrace.blockCount input)
    (returnDest : UInt256) (rest : List UInt256) :
    (Schedule.loopState s (DriverTrace.messageOffsetWord block)
      returnDest rest 16).activeWords.toNat ≤
      max s.activeWords.toNat (67 + 2 * block) :=
  scheduleLoopPrefix_activeWords_le s input hfit block hblock returnDest rest
    16 (by omega)

private theorem scheduleIteration_activeWords_ge (s : State)
    (input : ByteArray) (hfit : CalldataFits input) (block k : Nat)
    (hblock : block < DriverTrace.blockCount input) (hk : k < 16)
    (returnDest : UInt256) (rest : List UInt256) (bound : Nat)
    (hs : s.activeWords.toNat ≤ bound)
    (hbound : 67 + 2 * block ≤ bound) (hlt : bound < 2 ^ 256) :
    s.activeWords.toNat ≤
      (Schedule.afterIteration s (DriverTrace.messageOffsetWord block)
        returnDest rest k).activeWords.toNat := by
  have hload := messageLoadOffset input hfit block k hblock hk
  have hx := xSlotOffset k hk
  let loadedWords := MachineState.activeWordsAfter s.activeWords.toNat
    (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord block) k).toNat 32
  have hloaded : loadedWords ≤ bound := by
    apply activeWordsAfter_le _ _ _ _ hs
    rw [hload]
    simp [Padding.messageOffset]
    omega
  have hloadedLt : loadedWords < 2 ^ 256 := lt_of_le_of_lt hloaded hlt
  let loaded := Schedule.afterRead s (DriverTrace.messageOffsetWord block)
    returnDest rest k
  have hloadedEq : loaded.activeWords.toNat = loadedWords := by
    unfold loaded Schedule.afterRead loadedWords
    exact activeWordsAfterUInt256_toNat s _ _ hloadedLt
  have hstored : MachineState.activeWordsAfter loaded.activeWords.toNat
      (Schedule.xSlotWord k).toNat 32 ≤ bound := by
    apply activeWordsAfter_le _ _ _ _ (by rw [hloadedEq]; exact hloaded)
    rw [hx]
    omega
  have hstoredLt : MachineState.activeWordsAfter loaded.activeWords.toNat
      (Schedule.xSlotWord k).toNat 32 < 2 ^ 256 :=
    lt_of_le_of_lt hstored hlt
  change s.activeWords.toNat ≤ (loaded.activeWordsAfterUInt256
    (Schedule.xSlotWord k).toNat 32).toNat
  rw [activeWordsAfterUInt256_toNat loaded _ _ hstoredLt]
  exact le_trans (activeWordsAfter_ge _ _ _)
    (by rw [hloadedEq]
        exact activeWordsAfter_ge _ _ _)

private theorem scheduleLoopPrefix_activeWords_ge (s : State)
    (input : ByteArray) (hfit : CalldataFits input) (block : Nat)
    (hblock : block < DriverTrace.blockCount input)
    (returnDest : UInt256) (rest : List UInt256) (n : Nat) (hn : n ≤ 16) :
    s.activeWords.toNat ≤
      (Schedule.loopState s (DriverTrace.messageOffsetWord block)
        returnDest rest n).activeWords.toNat := by
  let bound := max s.activeWords.toNat (67 + 2 * block)
  have hlt : bound < 2 ^ 256 := by
    exact (Nat.max_lt).2 ⟨s.activeWords.val.isLt, by
      have hpadded := Padding.paddedLength_lt input.size
      have hoff : 64 * block < Padding.paddedLength input.size := by
        rw [DriverTrace.paddedLength_eq_blockCount input]
        omega
      unfold CalldataFits at hfit
      norm_num [Padding.messageOffset] at hfit ⊢
      omega⟩
  have hloop : ∀ n, n ≤ 16 →
      s.activeWords.toNat ≤
        (Schedule.loopState s (DriverTrace.messageOffsetWord block)
          returnDest rest n).activeWords.toNat := by
    intro n hn
    induction n with
    | zero => exact Nat.le_refl _
    | succ n ih =>
        rw [Schedule.loopState]
        exact le_trans (ih (by omega))
          (scheduleIteration_activeWords_ge
            (Schedule.loopState s (DriverTrace.messageOffsetWord block)
              returnDest rest n)
            input hfit block n hblock (by omega) returnDest rest bound
            (by
              exact scheduleLoopPrefix_activeWords_le s input hfit block hblock
                returnDest rest n (by omega))
            (Nat.le_max_right _ _) hlt)
  exact hloop n hn

private theorem scheduleLoop_activeWords_ge (s : State)
    (input : ByteArray) (hfit : CalldataFits input) (block : Nat)
    (hblock : block < DriverTrace.blockCount input)
    (returnDest : UInt256) (rest : List UInt256) :
    s.activeWords.toNat ≤
      (Schedule.loopState s (DriverTrace.messageOffsetWord block)
        returnDest rest 16).activeWords.toNat :=
  scheduleLoopPrefix_activeWords_ge s input hfit block hblock returnDest rest
    16 (by omega)

/-- The sixteen schedule iterations end exactly at the last unaligned message
load's high-water mark. -/
theorem scheduledState_activeWords (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (block : Nat)
    (hblock : block < DriverTrace.blockCount input)
    (returnDest : UInt256) (rest : List UInt256) :
    (Schedule.loopState s (DriverTrace.messageOffsetWord block)
      returnDest rest 16).activeWords.toNat =
      max s.activeWords.toNat (67 + 2 * block) := by
  let prev := Schedule.loopState s (DriverTrace.messageOffsetWord block)
    returnDest rest 15
  let target := 67 + 2 * block
  let bound := max s.activeWords.toNat target
  have hprevLe : prev.activeWords.toNat ≤ bound :=
    scheduleLoopPrefix_activeWords_le s input hfit block hblock returnDest rest
      15 (by omega)
  have hprevGe : s.activeWords.toNat ≤ prev.activeWords.toNat :=
    scheduleLoopPrefix_activeWords_ge s input hfit block hblock returnDest rest
      15 (by omega)
  have hload := messageLoadOffset input hfit block 15 hblock (by omega)
  have hword :
      ((Schedule.loadOffsetWord (DriverTrace.messageOffsetWord block) 15).toNat +
          32 - 1) / 32 + 1 = target := by
    rw [hload]
    simp [target, Padding.messageOffset]
    omega
  have hloadedWords : MachineState.activeWordsAfter prev.activeWords.toNat
      (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord block) 15).toNat
        32 = max prev.activeWords.toNat target := by
    simp only [MachineState.activeWordsAfter, if_neg (by omega : (32 : Nat) ≠ 0)]
    rw [hword]
  have htargetLt : target < 2 ^ 256 := by
    have hpadded := Padding.paddedLength_lt input.size
    have hoff : 64 * block < Padding.paddedLength input.size := by
      rw [DriverTrace.paddedLength_eq_blockCount input]
      omega
    unfold CalldataFits at hfit
    norm_num [target, Padding.messageOffset] at hfit ⊢
    omega
  have hloadedLt : MachineState.activeWordsAfter prev.activeWords.toNat
      (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord block) 15).toNat
        32 < 2 ^ 256 := by
    rw [hloadedWords]
    exact (Nat.max_lt).2 ⟨prev.activeWords.val.isLt, htargetLt⟩
  let loaded := Schedule.afterRead prev (DriverTrace.messageOffsetWord block)
    returnDest rest 15
  have hloaded : loaded.activeWords.toNat =
      max prev.activeWords.toNat target := by
    unfold loaded Schedule.afterRead
    rw [activeWordsAfterUInt256_toNat prev _ _ hloadedLt, hloadedWords]
  have hx := xSlotOffset 15 (by omega)
  have hstore : loaded.activeWordsAfterUInt256
      (Schedule.xSlotWord 15).toNat 32 = loaded.activeWords := by
    apply activeWordsAfterUInt256_eq
    rw [hx, hloaded]
    have ht : target ≤ max prev.activeWords.toNat target := Nat.le_max_right _ _
    simp [target] at ht ⊢
    omega
  rw [show Schedule.loopState s (DriverTrace.messageOffsetWord block)
      returnDest rest 16 =
      Schedule.afterIteration prev (DriverTrace.messageOffsetWord block)
        returnDest rest 15 by rfl]
  change (loaded.activeWordsAfterUInt256
      (Schedule.xSlotWord 15).toNat 32).toNat = bound
  rw [hstore, hloaded]
  apply Nat.le_antisymm
  · apply (Nat.max_le).2
    exact ⟨hprevLe, Nat.le_max_right _ _⟩
  · apply (Nat.max_le).2
    exact ⟨hprevGe.trans (Nat.le_max_left _ _), Nat.le_max_right _ _⟩

theorem scheduledState_activeWords_ge_67 (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (block : Nat)
    (hblock : block < DriverTrace.blockCount input)
    (returnDest : UInt256) (rest : List UInt256) :
    67 ≤ (Schedule.loopState s (DriverTrace.messageOffsetWord block)
      returnDest rest 16).activeWords.toNat := by
  rw [scheduledState_activeWords s input hfit block hblock returnDest rest]
  exact le_trans (by omega) (Nat.le_max_right _ _)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleActiveWords
