import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScratchLow

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleWord

open EvmSemantics
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.ScratchLow
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound

/-! Pure word bridges for dense schedules.  These statements do not claim an
EVM trace; they only identify the effect of replacing a message word by a
word with the same low 32 bits. -/

theorem stackSum_eq_of_toUInt32_eq
    (f a word0 word1 constant : UInt256)
    (hword : toUInt32 word0 = toUInt32 word1) :
    StackRound.stackSum f a word0 constant =
      StackRound.stackSum f a word1 constant := by
  simp only [StackRound.stackSum, mask32_eq_ofUInt32, toUInt32_add, hword]

theorem rawRound_eq_of_toUInt32_eq
    (x : EvmWorking) (j : Nat)
    (word0 word1 : UInt256) (rotation : Nat) (constant : UInt256)
    (hword : toUInt32 word0 = toUInt32 word1) :
    ScratchLow.rawRound x j word0 rotation constant =
      ScratchLow.rawRound x j word1 rotation constant := by
  have hsum := stackSum_eq_of_toUInt32_eq
    (StackRound.stackF j x.b x.c x.d) x.a word0 word1 constant hword
  simp only [ScratchLow.rawRound]
  rw [hsum]

theorem twoRawRound_eq_of_toUInt32_eq
    (x : EvmWorking) (j : Nat)
    (word0 word0' word1 word1' : UInt256)
    (r0 r1 : Nat) (constant : UInt256)
    (hword0 : toUInt32 word0 = toUInt32 word0')
    (hword1 : toUInt32 word1 = toUInt32 word1') :
    ScratchLow.rawRound
        (ScratchLow.rawRound x j word0 r0 constant)
        j word1 r1 constant =
      ScratchLow.rawRound
        (ScratchLow.rawRound x j word0' r0 constant)
        j word1' r1 constant := by
  calc
    ScratchLow.rawRound
        (ScratchLow.rawRound x j word0 r0 constant)
        j word1 r1 constant =
      ScratchLow.rawRound
        (ScratchLow.rawRound x j word0' r0 constant)
        j word1 r1 constant := by
          exact congrArg (fun y => ScratchLow.rawRound y j word1 r1 constant)
            (rawRound_eq_of_toUInt32_eq x j word0 word0' r0 constant hword0)
    _ = ScratchLow.rawRound
        (ScratchLow.rawRound x j word0' r0 constant)
        j word1' r1 constant :=
      rawRound_eq_of_toUInt32_eq
        (ScratchLow.rawRound x j word0' r0 constant)
        j word1 word1' r1 constant hword1

example :
    toUInt32 (UInt256.ofNat 7) =
      toUInt32 (UInt256.ofNat (7 + 2 ^ 32)) := by
  decide

example :
    ScratchLow.rawRound
        ({ a := 0, b := 0, c := 0, d := 0, e := 0 } : EvmWorking)
        0 (UInt256.ofNat 7) 1 0 =
      ScratchLow.rawRound
        ({ a := 0, b := 0, c := 0, d := 0, e := 0 } : EvmWorking)
        0 (UInt256.ofNat (7 + 2 ^ 32)) 1 0 := by
  apply rawRound_eq_of_toUInt32_eq
  decide

example :
    (ScratchLow.rawRound
        ({ a := 0, b := 0, c := 0, d := 0, e := 0 } : EvmWorking)
        0 (UInt256.ofNat 1) 1 0).b ≠
      (ScratchLow.rawRound
        ({ a := 0, b := 0, c := 0, d := 0, e := 0 } : EvmWorking)
        0 (UInt256.ofNat 2) 1 0).b := by
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleWord
