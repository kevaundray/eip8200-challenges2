import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationMultiply

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# H27 paired-round raw traces for the negated Boolean forms

The f2 and f4 helpers execute two full-width scratch rounds. This file stops
immediately before the helper's final `JUMP`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairNegatedRoundTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanSelect
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationMultiply

private theorem word_add_assoc (u v w : UInt256) :
    (u + v) + w = u + (v + w) := by
  apply word_ext
  change ((u.val + v.val) + w.val).val =
    (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

private theorem h16_masked_sum (a x f k : UInt256) :
    mask32 (k + (a + (x + f))) =
      mask32 (k + (a + (x + mask32 f))) := by
  simp only [mask32_eq_ofUInt32, toUInt32_add, toUInt32_ofUInt32]

private theorem sum_base (a word f constant : UInt256) :
    constant.add (a.add (word.add f)) =
      constant.add ((a.add f).add word) := by
  have hcomm (u v : UInt256) : u.add v = v.add u :=
    word_add_comm u v
  rw [hcomm word]
  exact congrArg (fun z : UInt256 => constant.add z)
    (word_add_assoc a f word).symm

private theorem sum_absorption (a word f constant : UInt256) :
    mask.land (constant.add (a.add (word.add f))) =
      mask.land (constant.add (a.add (word.add (f.land mask)))) := by
  calc
    mask.land (constant.add (a.add (word.add f))) =
        (constant.add (a.add (word.add f))).land mask := by
          exact Word.land_comm _ _
    _ = (constant.add (a.add (word.add (f.land mask)))).land mask := by
          exact h16_masked_sum _ _ _ _
    _ = mask.land (constant.add (a.add (word.add (f.land mask)))) := by
          exact (Word.land_comm _ _).symm

private theorem sum_code_equiv (a word f constant : UInt256) :
    mask.land (constant.add (word.add (a.add f))) =
      mask.land (constant.add ((a.add (f.land mask)).add word)) := by
  have hcomm (u v : UInt256) : u.add v = v.add u :=
    word_add_comm u v
  have hperm : word.add (a.add f) = a.add (word.add f) := by
    calc
      word.add (a.add f) = (a.add f).add word := hcomm word (a.add f)
      _ = a.add (f.add word) := word_add_assoc a f word
      _ = a.add (word.add f) := by rw [hcomm f word]
  calc
    mask.land (constant.add (word.add (a.add f))) =
        mask.land (constant.add (a.add (word.add f))) := by
          exact congrArg (fun z : UInt256 => mask.land (constant.add z)) hperm
    _ = mask.land (constant.add (a.add (word.add (f.land mask)))) := by
          exact sum_absorption a word f constant
    _ = mask.land (constant.add ((a.add (f.land mask)).add word)) := by
          exact congrArg (fun z : UInt256 => mask.land z)
            (sum_base a word (f.land mask) constant)

private theorem raw_rotate_target (qcode qtarget e : UInt256) (rotation : Nat)
    (hcode : mask.land qcode = mask.land qtarget)
    (hq : (mask.land qtarget).toNat < 2 ^ 32) (hrot : rotation ≤ 32) :
    mask.land
        (e.add
          (UInt256.shiftRight
            ((mask.land qcode).lor
              ((mask.land qcode).shiftLeft (UInt256.ofNat 32)))
            (UInt256.ofNat (32 - rotation)))) =
      UInt256.land
        (e.add
          (((qtarget.land mask).shiftLeft (UInt256.ofNat rotation)).lor
            ((qtarget.land mask).shiftRight (UInt256.ofNat (32 - rotation)))))
        mask := by
  calc
    mask.land
          (e.add
            (UInt256.shiftRight
              ((mask.land qcode).lor
                ((mask.land qcode).shiftLeft (UInt256.ofNat 32)))
              (UInt256.ofNat (32 - rotation)))) =
        mask.land
          (UInt256.add
            (UInt256.shiftRight
              ((mask.land qcode).lor
                ((mask.land qcode).shiftLeft (UInt256.ofNat 32)))
              (UInt256.ofNat (32 - rotation)))
            e) := by
              exact congrArg (fun z : UInt256 => mask.land z)
                (word_add_comm e _)
    _ = mask.land
          (UInt256.add
            (UInt256.shiftRight
              ((mask.land qtarget).lor
                ((mask.land qtarget).shiftLeft (UInt256.ofNat 32)))
              (UInt256.ofNat (32 - rotation)))
            e) := by
              rw [hcode]
    _ = UInt256.land
          (UInt256.add
            (((qtarget.land mask).shiftLeft (UInt256.ofNat rotation)).lor
              ((qtarget.land mask).shiftRight (UInt256.ofNat (32 - rotation))))
            e)
          mask := raw_rotate_or_fold qtarget e rotation hq hrot
    _ = UInt256.land
          (UInt256.add e
            (((qtarget.land mask).shiftLeft (UInt256.ofNat rotation)).lor
              ((qtarget.land mask).shiftRight (UInt256.ofNat (32 - rotation)))))
          mask := by
            exact congrArg (fun z : UInt256 => UInt256.land z mask)
              (word_add_comm _ _)

private theorem negated_sum_base (x : EvmWorking) (word constant : UInt256) :
    constant.add (x.a.add (word.add
      (x.d.xor (x.b.lor x.c.lnot)))) =
      constant.add ((x.a.add
        (x.d.xor (x.b.lor x.c.lnot))).add word) := by
  have hcomm (u v : UInt256) : u.add v = v.add u :=
    word_add_comm u v
  rw [hcomm word]
  exact congrArg (fun z : UInt256 => constant.add z)
    (word_add_assoc x.a (x.d.xor (x.b.lor x.c.lnot)) word).symm

private theorem negated_sum_absorption (x : EvmWorking)
    (word constant : UInt256) :
    mask.land (constant.add (x.a.add (word.add
      (x.d.xor (x.b.lor x.c.lnot))))) =
      mask.land (constant.add (x.a.add (word.add
        ((x.d.xor (x.b.lor x.c.lnot)).land mask)))) := by
  calc
    mask.land (constant.add (x.a.add (word.add
        (x.d.xor (x.b.lor x.c.lnot))))) =
        (constant.add (x.a.add (word.add
          (x.d.xor (x.b.lor x.c.lnot))))).land mask := by
            exact Word.land_comm _ _
    _ = (constant.add (x.a.add (word.add
          ((x.d.xor (x.b.lor x.c.lnot)).land mask)))).land mask := by
            exact h16_masked_sum _ _ _ _
    _ = mask.land (constant.add (x.a.add (word.add
        ((x.d.xor (x.b.lor x.c.lnot)).land mask)))) := by
            exact (Word.land_comm _ _).symm

private theorem negated4_sum_base (x : EvmWorking) (word constant : UInt256) :
    constant.add (x.a.add (word.add
      (x.b.xor (x.c.lor x.d.lnot)))) =
      constant.add ((x.a.add
        (x.b.xor (x.c.lor x.d.lnot))).add word) := by
  have hcomm (u v : UInt256) : u.add v = v.add u :=
    word_add_comm u v
  rw [hcomm word]
  exact congrArg (fun z : UInt256 => constant.add z)
    (word_add_assoc x.a (x.b.xor (x.c.lor x.d.lnot)) word).symm

private theorem negated4_sum_absorption (x : EvmWorking)
    (word constant : UInt256) :
    mask.land (constant.add (x.a.add (word.add
      (x.b.xor (x.c.lor x.d.lnot))))) =
      mask.land (constant.add (x.a.add (word.add
        ((x.b.xor (x.c.lor x.d.lnot)).land mask)))) := by
  calc
    mask.land (constant.add (x.a.add (word.add
        (x.b.xor (x.c.lor x.d.lnot))))) =
        (constant.add (x.a.add (word.add
          (x.b.xor (x.c.lor x.d.lnot))))).land mask := by
            exact Word.land_comm _ _
    _ = (constant.add (x.a.add (word.add
          ((x.b.xor (x.c.lor x.d.lnot)).land mask)))).land mask := by
            exact h16_masked_sum _ _ _ _
    _ = mask.land (constant.add (x.a.add (word.add
        ((x.b.xor (x.c.lor x.d.lnot)).land mask)))) := by
            exact (Word.land_comm _ _).symm

private theorem or_eq_lor (a b : UInt256) :
    a ||| b = UInt256.lor a b := by
  rfl

private theorem factor_mul_mask_land (q : UInt256) :
    UInt256.mul (UInt256.ofNat 4294967297)
        ((UInt256.ofNat 4294967295).land q) =
      ((UInt256.ofNat 4294967295).land q).lor
        (UInt256.shiftLeft ((UInt256.ofNat 4294967295).land q)
          (UInt256.ofNat 32)) := by
  have hq : ((UInt256.ofNat 4294967295).land q).toNat < 2 ^ 32 := by
    simpa [mask] using (mask_land_toNat_lt q)
  simpa only [or_eq_lor] using (factor_mul_eq_or_shift
    ((UInt256.ofNat 4294967295).land q) hq)

private theorem mul_op (u v : UInt256) : u * v = UInt256.mul u v := by
  rfl

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_f2 (s : State) (startPC p0 p1 returnPC : UInt256)
    (r0 r1 : Nat) (working : EvmWorking) (constant : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1012)
    (hrun : s.halt = .Running) (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32) :
    runInstrSeq (pairBeforeJumpTemplate 2 constant)
        (pairHelperEntry s startPC p0 p1 returnPC r0 r1 working rest) =
      some (pairAfterHelperBeforeJump s
        (pcAfter startPC (pairBeforeJumpTemplate 2 constant))
        returnPC 2 working p0 p1 r0 r1 constant rest) := by
  have hcap (m : Nat) (hm : m ≤ 12) : rest.length + m < 1024 := by
    omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  have hswap2 (u v w : UInt256) (rho : List UInt256) :
      (u :: v :: w :: rho).exchange 0 2 =
        some (w :: v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u w [v] rho
  have hswap3 (u v w z : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: rho).exchange 0 3 =
        some (z :: v :: w :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u z [v, w] rho
  have hswap4 (u v w z q : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: rho).exchange 0 4 =
        some (q :: v :: w :: z :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u q [v, w, z] rho
  have hswap5 (u v w z q r : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: r :: rho).exchange 0 5 =
        some (r :: v :: w :: z :: q :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u r [v, w, z, q] rho
  have hswap6 (u v w z q r t : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: r :: t :: rho).exchange 0 6 =
        some (t :: v :: w :: z :: q :: r :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u t [v, w, z, q, r] rho
  have hswap7 (u v w z q r t k : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: r :: t :: k :: rho).exchange 0 7 =
        some (k :: v :: w :: z :: q :: r :: t :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u k [v, w, z, q, r, t] rho
  have hadd (u v : UInt256) : u + v = u.add v := by
    rfl
  have hcomm (u v : UInt256) : u.add v = v.add u := by
    exact word_add_comm u v
  have hxorcomm (u v : UInt256) : u.xor v = v.xor u := by
    exact BooleanSelect.xor_comm u v
  have hnot (u : UInt256) : ~~~u = u.lnot := by
    rfl
  have hbase0 := negated_sum_base working
    (MachineState.readWord s.memory p0.toNat) constant
  have hsum0 := negated_sum_absorption working
    (MachineState.readWord s.memory p0.toNat) constant
  have hbase1 := negated_sum_base
    (stackRound working 2 (MachineState.readWord s.memory p0.toNat) r0 constant)
    (MachineState.readWord s.memory p1.toNat) constant
  have hsum1 := negated_sum_absorption
    (stackRound working 2 (MachineState.readWord s.memory p0.toNat) r0 constant)
    (MachineState.readWord s.memory p1.toNat) constant
  have hcode0 := sum_code_equiv working.a
    (MachineState.readWord s.memory p0.toNat)
    (working.d.xor (working.b.lor working.c.lnot)) constant
  let word0 : UInt256 := MachineState.readWord s.memory p0.toNat
  let word1 : UInt256 := MachineState.readWord s.memory p1.toNat
  let f0 : UInt256 := working.d.xor (working.b.lor working.c.lnot)
  let q0 : UInt256 :=
    constant.add ((working.a.add (f0.land mask)).add word0)
  have hT0 := raw_rotate_target
    (constant.add (word0.add (working.a.add f0))) q0 working.e r0
    (by simpa [word0, f0, q0] using hcode0)
    (mask_land_toNat_lt _) hrot0
  have hT0_eval := hT0
  simp only [word0, f0] at hT0_eval
  have hT0_eval' := hT0_eval
  simp only [mask] at hT0_eval'
  let t0 : UInt256 :=
    UInt256.land
      (UInt256.add working.e
        (((q0.land mask).shiftLeft (UInt256.ofNat r0)).lor
          ((q0.land mask).shiftRight (UInt256.ofNat (32 - r0)))))
      mask
  let f1 : UInt256 :=
    (ScratchLow.rawC10 working.c).xor (working.b.lnot.lor t0)
  let q1c : UInt256 :=
    constant.add ((working.e.add (f1.land mask)).add word1)
  have hq1c :
      mask.land (constant.add
        (working.e.add (word1.add
          ((ScratchLow.rawC10 working.c).xor (working.b.lnot.lor t0))))) =
      mask.land q1c := by
    have hperm : working.e.add (word1.add f1) =
        word1.add (working.e.add f1) := by
      apply word_ext
      change (working.e.val + (word1.val + f1.val)).val =
        (word1.val + (working.e.val + f1.val)).val
      simp [Fin.add_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    calc
      mask.land (constant.add
          (working.e.add (word1.add
            ((ScratchLow.rawC10 working.c).xor (working.b.lnot.lor t0))))) =
          mask.land (constant.add (word1.add (working.e.add f1))) := by
            exact congrArg (fun z : UInt256 => mask.land (constant.add z))
              (by simpa [f1] using hperm)
      _ = mask.land (constant.add
            ((working.e.add (f1.land mask)).add word1)) :=
            sum_code_equiv working.e word1 f1 constant
      _ = mask.land q1c := by rfl
  have hq1c' := hq1c
  simp only [word1, t0, mask, ScratchLow.rawC10] at hq1c'
  have hbool1 :
      (t0.lor working.b.lnot).xor (ScratchLow.rawC10 working.c) = f1 := by
    calc
      (t0.lor working.b.lnot).xor (ScratchLow.rawC10 working.c) =
          (working.b.lnot.lor t0).xor (ScratchLow.rawC10 working.c) := by
            exact congrArg (fun z : UInt256 => z.xor (ScratchLow.rawC10 working.c))
              (Word.lor_comm t0 working.b.lnot)
      _ = (ScratchLow.rawC10 working.c).xor (working.b.lnot.lor t0) :=
        BooleanSelect.xor_comm _ _
      _ = f1 := by rfl
  have hbool1' :
      (ScratchLow.rawC10 working.c).xor (working.b.lnot.lor t0) = f1 := by
    calc
      (ScratchLow.rawC10 working.c).xor (working.b.lnot.lor t0) =
          (working.b.lnot.lor t0).xor (ScratchLow.rawC10 working.c) :=
        hxorcomm _ _
      _ = (t0.lor working.b.lnot).xor (ScratchLow.rawC10 working.c) := by
            exact congrArg (fun z : UInt256 =>
              z.xor (ScratchLow.rawC10 working.c))
              (Word.lor_comm working.b.lnot t0)
      _ = f1 := hbool1
  have hsecondQ :
      mask.land (constant.add
          (word1.add (working.e.add
          (((t0.lor working.b.lnot).xor (ScratchLow.rawC10 working.c)).land mask)))) =
      mask.land q1c := by
    calc
      mask.land (constant.add
            (word1.add (working.e.add
            (((t0.lor working.b.lnot).xor (ScratchLow.rawC10 working.c)).land mask)))) =
          mask.land (constant.add
            (word1.add (working.e.add (f1.land mask)))) := by
              rw [hbool1]
      _ = mask.land (constant.add
            ((working.e.add (f1.land mask)).add word1)) := by
              exact congrArg (fun z : UInt256 => mask.land (constant.add z))
                (hcomm _ _)
      _ = mask.land q1c := by rfl
  let q1sem : UInt256 :=
    constant.add
      (word1.add (working.e.add
        (((t0.lor working.b.lnot).xor (ScratchLow.rawC10 working.c)).land mask)))
  have hq1pure :
      mask.land (constant.add
        ((working.e.add
          (((ScratchLow.rawC10 working.c).xor
            (working.b.lnot.lor t0)).land mask)).add word1)) =
      mask.land q1sem := by
    calc
      mask.land (constant.add
          ((working.e.add
            (((ScratchLow.rawC10 working.c).xor
              (working.b.lnot.lor t0)).land mask)).add word1)) =
          mask.land (constant.add
            (word1.add (working.e.add
              ((ScratchLow.rawC10 working.c).xor
                (working.b.lnot.lor t0))))) := by
            exact (sum_code_equiv working.e word1
              ((ScratchLow.rawC10 working.c).xor
                (working.b.lnot.lor t0)) constant).symm
      _ = mask.land q1sem := by
        dsimp [q1sem]
        rw [hbool1', hbool1]
        exact sum_absorption word1 working.e f1 constant
  have hq1pure' :
      (constant.add
        ((working.e.add
          (((ScratchLow.rawC10 working.c).xor
            (working.b.lnot.lor t0)).land mask)).add word1)).land mask =
      q1sem.land mask := by
    calc
      (constant.add
          ((working.e.add
            (((ScratchLow.rawC10 working.c).xor
              (working.b.lnot.lor t0)).land mask)).add word1)).land mask =
          mask.land (constant.add
            ((working.e.add
              (((ScratchLow.rawC10 working.c).xor
                (working.b.lnot.lor t0)).land mask)).add word1)) :=
        Word.land_comm _ _
      _ = mask.land q1sem := hq1pure
      _ = q1sem.land mask := (Word.land_comm _ _).symm
  have hq1sem : q1sem.land mask = q1c.land mask := by
    calc
      q1sem.land mask = mask.land q1sem := Word.land_comm _ _
      _ = mask.land q1c := by
        simpa only [q1sem] using hsecondQ
      _ = q1c.land mask := Word.land_comm _ _
  have hT1_sem :
      UInt256.land
          (UInt256.add working.d
            (((q1sem.land mask).shiftLeft (UInt256.ofNat r1)).lor
              ((q1sem.land mask).shiftRight (UInt256.ofNat (32 - r1)))))
          mask =
        UInt256.land
          (UInt256.add working.d
            (((q1c.land mask).shiftLeft (UInt256.ofNat r1)).lor
              ((q1c.land mask).shiftRight (UInt256.ofNat (32 - r1)))))
          mask := by
    exact congrArg
      (fun u : UInt256 =>
        UInt256.land
          (UInt256.add working.d
            ((u.shiftLeft (UInt256.ofNat r1)).lor
              (u.shiftRight (UInt256.ofNat (32 - r1)))))
          mask)
      hq1sem
  have hT1_sem' := hT1_sem
  simp only [mask] at hT1_sem'
  have hsecondRotC := raw_rotate_or_fold q1c working.d r1
    (mask_land_toNat_lt _) hrot1
  have hsecondRotC' :
      mask.land
          (UInt256.add
            (UInt256.shiftRight
              ((mask.land q1c).lor
                ((mask.land q1c).shiftLeft (UInt256.ofNat 32)))
              (UInt256.ofNat (32 - r1))) working.d) =
        UInt256.land
          (UInt256.add working.d
            (((q1c.land mask).shiftLeft (UInt256.ofNat r1)).lor
              ((q1c.land mask).shiftRight (UInt256.ofNat (32 - r1)))))
          mask := by
    calc
      mask.land
          (UInt256.add
            (UInt256.shiftRight
              ((mask.land q1c).lor
                ((mask.land q1c).shiftLeft (UInt256.ofNat 32)))
              (UInt256.ofNat (32 - r1))) working.d) =
          UInt256.land
            (UInt256.add
              (((q1c.land mask).shiftLeft (UInt256.ofNat r1)).lor
                ((q1c.land mask).shiftRight (UInt256.ofNat (32 - r1))))
              working.d)
            mask := hsecondRotC
      _ = UInt256.land
            (UInt256.add working.d
              (((q1c.land mask).shiftLeft (UInt256.ofNat r1)).lor
                ((q1c.land mask).shiftRight (UInt256.ofNat (32 - r1)))))
            mask := by
              rw [hcomm]
  have activeWordsAfter_lt (curr off : Nat)
      (hcurr : curr < UInt256.size) (hoff : off < UInt256.size) :
      MachineState.activeWordsAfter curr off 32 < UInt256.size := by
    unfold MachineState.activeWordsAfter
    split
    · omega
    · dsimp only
      rw [Nat.max_lt]
      constructor
      · exact hcurr
      · simp only [UInt256.size]
        have hoff' : off < 2 ^ 256 := by
          simpa only [UInt256.size] using hoff
        have hdiv : (off + 32 - 1) / 32 < 2 ^ 256 - 1 := by
          apply (Nat.div_lt_iff_lt_mul (by norm_num)).2
          have hoff'' : off ≤ 2 ^ 256 - 1 := by omega
          calc
            off + 32 - 1 ≤ (2 ^ 256 - 1) + 31 := by omega
            _ < (2 ^ 256 - 1) * 32 := by norm_num
        omega
  have hactive0 :
      MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32 <
        UInt256.size :=
    activeWordsAfter_lt s.activeWords.toNat p0.toNat
      s.activeWords.val.isLt p0.val.isLt
  have hactive0mod := Nat.mod_eq_of_lt hactive0
  have hactivePair :
      MachineState.activeWordsAfter
          (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32 %
            UInt256.size) p1.toNat 32 =
        MachineState.activeWordsAfter
          (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32)
            p1.toNat 32 := by
    rw [hactive0mod]
  have hactivePairUInt :
      UInt256.ofNat
          (MachineState.activeWordsAfter
            (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32 %
              UInt256.size) p1.toNat 32) =
        UInt256.ofNat
          (MachineState.activeWordsAfter
            (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32)
              p1.toNat 32) := by
    rw [hactive0mod]
  simp (config := { maxSteps := 3000000 })
    [pairBeforeJumpTemplate, pairFirstBooleanOps, pairSecondBooleanOps,
      pairDup7, pairDup8, pairDup9, pairDup10, pairSwap5, pairSwap7,
      qrot, mul_op, factor_mul_mask_land, cfold, op, push1, push2, push4, dup1,
      dup2, dup3, dup4,
      dup5, dup6, swap1, swap2, swap3, swap4, mask, c10, c22,
      runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      HMul.hMul, Mul.mul,
      pairHelperEntry, pairAfterHelperBeforeJump, pairWorking, roundWords,
      pcAfter, StackRound.stackRound, StackRound.stackF,
      StackRound.stackSum, StackRound.stackRawRot,
      ScratchLow.rawRound,
      Word.mask32, List.exchange, hrun, hcap, hswap1, hswap2, hswap3,
      hswap4, hswap5, hswap6, hswap7, UInt256.succ, Instr.size,
      Instr.size_push, Instr.size_op, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, Word.land_comm, Word.lor_comm,
      BooleanSelect.xor_comm, State.activeWordsAfterUInt256,
      State.activeWordsAfterUInt256_2, hadd, hcomm, hxorcomm,
      hbase0, hsum0, hbase1, hsum1, hcode0, hactive0,
      hactive0mod, hactivePair, hactivePairUInt, hq1pure']
  constructor
  · simpa only [UInt256.size] using hactivePairUInt
  · constructor
    · rw [hT0_eval']
      simp only [hnot]
      rw [hq1c']
      simpa [ScratchLow.rawC10, mask, word0, f0, q0, word1, q1sem, t0,
        HMul.hMul, Mul.mul, UInt256.xor, HXor.hXor, HAnd.hAnd,
        AndOp.and, EvmSemantics.UInt256.instAndOp, HOr.hOr, OrOp.or,
        EvmSemantics.UInt256.instOrOp, hbool1, hbool1', hq1pure, hq1pure',
        Word.lor_comm,
        BooleanSelect.xor_comm, hcomm] using hsecondRotC'.trans hT1_sem.symm
    · constructor
      · rw [hnot]
        simpa [mask, word0, f0, q0, UInt256.xor, HXor.hXor,
          HAnd.hAnd, AndOp.and, EvmSemantics.UInt256.instAndOp,
          HOr.hOr, OrOp.or, EvmSemantics.UInt256.instOrOp] using hT0_eval'
      · constructor
        · rfl
        · rfl

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_f4 (s : State) (startPC p0 p1 returnPC : UInt256)
    (r0 r1 : Nat) (working : EvmWorking) (constant : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1012)
    (hrun : s.halt = .Running) (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32) :
    runInstrSeq (pairBeforeJumpTemplate 4 constant)
        (pairHelperEntry s startPC p0 p1 returnPC r0 r1 working rest) =
      some (pairAfterHelperBeforeJump s
        (pcAfter startPC (pairBeforeJumpTemplate 4 constant))
        returnPC 4 working p0 p1 r0 r1 constant rest) := by
  have hcap (m : Nat) (hm : m ≤ 12) : rest.length + m < 1024 := by
    omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  have hswap2 (u v w : UInt256) (rho : List UInt256) :
      (u :: v :: w :: rho).exchange 0 2 =
        some (w :: v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u w [v] rho
  have hswap3 (u v w z : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: rho).exchange 0 3 =
        some (z :: v :: w :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u z [v, w] rho
  have hswap4 (u v w z q : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: rho).exchange 0 4 =
        some (q :: v :: w :: z :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u q [v, w, z] rho
  have hswap5 (u v w z q r : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: r :: rho).exchange 0 5 =
        some (r :: v :: w :: z :: q :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u r [v, w, z, q] rho
  have hswap6 (u v w z q r t : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: r :: t :: rho).exchange 0 6 =
        some (t :: v :: w :: z :: q :: r :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u t [v, w, z, q, r] rho
  have hswap7 (u v w z q r t k : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: r :: t :: k :: rho).exchange 0 7 =
        some (k :: v :: w :: z :: q :: r :: t :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u k [v, w, z, q, r, t] rho
  have hadd (u v : UInt256) : u + v = u.add v := by
    rfl
  have hcomm (u v : UInt256) : u.add v = v.add u := by
    exact word_add_comm u v
  have hxorcomm (u v : UInt256) : u.xor v = v.xor u := by
    exact BooleanSelect.xor_comm u v
  have hnot (u : UInt256) : ~~~u = u.lnot := by
    rfl
  have hbase0 := negated4_sum_base working
    (MachineState.readWord s.memory p0.toNat) constant
  have hsum0 := negated4_sum_absorption working
    (MachineState.readWord s.memory p0.toNat) constant
  have hbase1 := negated4_sum_base
    (stackRound working 4 (MachineState.readWord s.memory p0.toNat) r0 constant)
    (MachineState.readWord s.memory p1.toNat) constant
  have hsum1 := negated4_sum_absorption
    (stackRound working 4 (MachineState.readWord s.memory p0.toNat) r0 constant)
    (MachineState.readWord s.memory p1.toNat) constant
  have hcode0 := sum_code_equiv working.a
    (MachineState.readWord s.memory p0.toNat)
    (working.b.xor (working.c.lor working.d.lnot)) constant
  let word0 : UInt256 := MachineState.readWord s.memory p0.toNat
  let word1 : UInt256 := MachineState.readWord s.memory p1.toNat
  let f0 : UInt256 := working.b.xor (working.c.lor working.d.lnot)
  let q0 : UInt256 :=
    constant.add ((working.a.add (f0.land mask)).add word0)
  have hT0 := raw_rotate_target
    (constant.add (word0.add (working.a.add f0))) q0 working.e r0
    (by simpa [word0, f0, q0] using hcode0)
    (mask_land_toNat_lt _) hrot0
  have hT0_eval := hT0
  simp only [word0, f0] at hT0_eval
  have hT0_eval' := hT0_eval
  simp only [mask] at hT0_eval'
  let t0 : UInt256 :=
    UInt256.land
      (UInt256.add working.e
        (((q0.land mask).shiftLeft (UInt256.ofNat r0)).lor
          ((q0.land mask).shiftRight (UInt256.ofNat (32 - r0)))))
      mask
  let f1 : UInt256 :=
    t0.xor (working.b.lor (ScratchLow.rawC10 working.c).lnot)
  let q1c : UInt256 :=
    constant.add ((working.e.add (f1.land mask)).add word1)
  have hbool1 :
      (working.b.lor (ScratchLow.rawC10 working.c).lnot).xor t0 = f1 := by
    calc
      (working.b.lor (ScratchLow.rawC10 working.c).lnot).xor t0 =
          t0.xor (working.b.lor (ScratchLow.rawC10 working.c).lnot) :=
        BooleanSelect.xor_comm _ _
      _ = f1 := by rfl
  have hq1c :
      mask.land (constant.add
        (working.e.add (word1.add
          ((working.b.lor (ScratchLow.rawC10 working.c).lnot).xor t0)))) =
      mask.land q1c := by
    have hperm : working.e.add (word1.add f1) =
        word1.add (working.e.add f1) := by
      apply word_ext
      change (working.e.val + (word1.val + f1.val)).val =
        (word1.val + (working.e.val + f1.val)).val
      simp [Fin.add_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    calc
      mask.land (constant.add
          (working.e.add (word1.add
            ((working.b.lor (ScratchLow.rawC10 working.c).lnot).xor t0)))) =
          mask.land (constant.add
            (working.e.add (word1.add f1))) := by
            rw [hbool1]
      _ = mask.land (constant.add (word1.add (working.e.add f1))) := by
            exact congrArg (fun z : UInt256 => mask.land (constant.add z))
              hperm
      _ = mask.land (constant.add
            ((working.e.add (f1.land mask)).add word1)) :=
            sum_code_equiv working.e word1 f1 constant
      _ = mask.land q1c := by rfl
  have hq1c' := hq1c
  simp only [word1, t0, mask, ScratchLow.rawC10] at hq1c'
  have hsecondQ :
      mask.land (constant.add
          (word1.add (working.e.add (f1.land mask)))) =
      mask.land q1c := by
    calc
      mask.land (constant.add
            (word1.add (working.e.add (f1.land mask)))) =
          mask.land (constant.add
            ((working.e.add (f1.land mask)).add word1)) := by
              exact congrArg (fun z : UInt256 => mask.land (constant.add z))
                (hcomm _ _)
      _ = mask.land q1c := by rfl
  let q1sem : UInt256 :=
    constant.add (word1.add (working.e.add (f1.land mask)))
  have hq1pure :
      mask.land (constant.add
        ((working.e.add
          (((working.b.lor (ScratchLow.rawC10 working.c).lnot).xor
            t0).land mask)).add word1)) =
      mask.land q1sem := by
    calc
      mask.land (constant.add
          ((working.e.add
            (((working.b.lor (ScratchLow.rawC10 working.c).lnot).xor
              t0).land mask)).add word1)) =
          mask.land (constant.add
            (word1.add (working.e.add
              ((working.b.lor (ScratchLow.rawC10 working.c).lnot).xor
                t0)))) := by
            exact (sum_code_equiv working.e word1
              ((working.b.lor (ScratchLow.rawC10 working.c).lnot).xor
                t0) constant).symm
      _ = mask.land q1sem := by
        dsimp [q1sem]
        rw [hbool1]
        exact sum_absorption word1 working.e f1 constant
  have hq1pure' :
      (constant.add
        ((working.e.add
          (((working.b.lor (ScratchLow.rawC10 working.c).lnot).xor
            t0).land mask)).add word1)).land mask =
      q1sem.land mask := by
    calc
      (constant.add
          ((working.e.add
            (((working.b.lor (ScratchLow.rawC10 working.c).lnot).xor
              t0).land mask)).add word1)).land mask =
          mask.land (constant.add
            ((working.e.add
              (((working.b.lor (ScratchLow.rawC10 working.c).lnot).xor
                t0).land mask)).add word1)) :=
        Word.land_comm _ _
      _ = mask.land q1sem := hq1pure
      _ = q1sem.land mask := (Word.land_comm _ _).symm
  have hq1sem : q1sem.land mask = q1c.land mask := by
    calc
      q1sem.land mask = mask.land q1sem := Word.land_comm _ _
      _ = mask.land q1c := by
        simpa only [q1sem] using hsecondQ
      _ = q1c.land mask := Word.land_comm _ _
  have hT1_sem :
      UInt256.land
          (UInt256.add working.d
            (((q1sem.land mask).shiftLeft (UInt256.ofNat r1)).lor
              ((q1sem.land mask).shiftRight (UInt256.ofNat (32 - r1)))))
          mask =
        UInt256.land
          (UInt256.add working.d
            (((q1c.land mask).shiftLeft (UInt256.ofNat r1)).lor
              ((q1c.land mask).shiftRight (UInt256.ofNat (32 - r1)))))
          mask := by
    exact congrArg
      (fun u : UInt256 =>
        UInt256.land
          (UInt256.add working.d
            ((u.shiftLeft (UInt256.ofNat r1)).lor
              (u.shiftRight (UInt256.ofNat (32 - r1)))))
          mask)
      hq1sem
  have hT1_sem' := hT1_sem
  simp only [mask] at hT1_sem'
  have hsecondRotC := raw_rotate_or_fold q1c working.d r1
    (mask_land_toNat_lt _) hrot1
  have hsecondRotC' :
      mask.land
          (UInt256.add
            (UInt256.shiftRight
              ((mask.land q1c).lor
                ((mask.land q1c).shiftLeft (UInt256.ofNat 32)))
              (UInt256.ofNat (32 - r1))) working.d) =
        UInt256.land
          (UInt256.add working.d
            (((q1c.land mask).shiftLeft (UInt256.ofNat r1)).lor
              ((q1c.land mask).shiftRight (UInt256.ofNat (32 - r1)))))
          mask := by
    calc
      mask.land
          (UInt256.add
            (UInt256.shiftRight
              ((mask.land q1c).lor
                ((mask.land q1c).shiftLeft (UInt256.ofNat 32)))
              (UInt256.ofNat (32 - r1))) working.d) =
          UInt256.land
            (UInt256.add
              (((q1c.land mask).shiftLeft (UInt256.ofNat r1)).lor
                ((q1c.land mask).shiftRight (UInt256.ofNat (32 - r1))))
              working.d)
            mask := hsecondRotC
      _ = UInt256.land
            (UInt256.add working.d
              (((q1c.land mask).shiftLeft (UInt256.ofNat r1)).lor
                ((q1c.land mask).shiftRight (UInt256.ofNat (32 - r1)))))
            mask := by
              rw [hcomm]
  have activeWordsAfter_lt (curr off : Nat)
      (hcurr : curr < UInt256.size) (hoff : off < UInt256.size) :
      MachineState.activeWordsAfter curr off 32 < UInt256.size := by
    unfold MachineState.activeWordsAfter
    split
    · omega
    · dsimp only
      rw [Nat.max_lt]
      constructor
      · exact hcurr
      · simp only [UInt256.size]
        have hoff' : off < 2 ^ 256 := by
          simpa only [UInt256.size] using hoff
        have hdiv : (off + 32 - 1) / 32 < 2 ^ 256 - 1 := by
          apply (Nat.div_lt_iff_lt_mul (by norm_num)).2
          have hoff'' : off ≤ 2 ^ 256 - 1 := by omega
          calc
            off + 32 - 1 ≤ (2 ^ 256 - 1) + 31 := by omega
            _ < (2 ^ 256 - 1) * 32 := by norm_num
        omega
  have hactive0 :
      MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32 <
        UInt256.size :=
    activeWordsAfter_lt s.activeWords.toNat p0.toNat
      s.activeWords.val.isLt p0.val.isLt
  have hactive0mod := Nat.mod_eq_of_lt hactive0
  have hactivePair :
      MachineState.activeWordsAfter
          (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32 %
            UInt256.size) p1.toNat 32 =
        MachineState.activeWordsAfter
          (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32)
            p1.toNat 32 := by
    rw [hactive0mod]
  have hactivePairUInt :
      UInt256.ofNat
          (MachineState.activeWordsAfter
            (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32 %
              UInt256.size) p1.toNat 32) =
        UInt256.ofNat
          (MachineState.activeWordsAfter
            (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32)
              p1.toNat 32) := by
    rw [hactive0mod]
  simp (config := { maxSteps := 3000000 })
    [pairBeforeJumpTemplate, pairFirstBooleanOps, pairSecondBooleanOps,
      pairDup7, pairDup8, pairDup9, pairDup10, pairSwap5, pairSwap7,
      qrot, mul_op, factor_mul_mask_land, cfold, op, push1, push2, push4, dup1,
      dup2, dup3, dup4,
      dup5, dup6, swap1, swap2, swap3, swap4, mask, c10, c22,
      runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      HMul.hMul, Mul.mul,
      pairHelperEntry, pairAfterHelperBeforeJump, pairWorking, roundWords,
      pcAfter, StackRound.stackRound, StackRound.stackF,
      StackRound.stackSum, StackRound.stackRawRot,
      ScratchLow.rawRound,
      Word.mask32, List.exchange, hrun, hcap, hswap1, hswap2, hswap3,
      hswap4, hswap5, hswap6, hswap7, UInt256.succ, Instr.size,
      Instr.size_push, Instr.size_op, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, Word.land_comm, Word.lor_comm,
      BooleanSelect.xor_comm, State.activeWordsAfterUInt256,
      State.activeWordsAfterUInt256_2, hadd, hcomm, hxorcomm,
      hbase0, hsum0, hbase1, hsum1, hcode0, hactive0,
      hactive0mod, hactivePair, hactivePairUInt, hq1pure']
  constructor
  · simpa only [UInt256.size] using hactivePairUInt
  · constructor
    · rw [hT0_eval']
      simp only [hnot]
      rw [hq1c']
      exact (raw_rotate_target q1c q1c working.d r1 rfl
        (mask_land_toNat_lt _) hrot1).trans hT1_sem.symm
    · constructor
      · rw [hnot]
        simpa [mask, word0, f0, q0, UInt256.xor, HXor.hXor,
          HAnd.hAnd, AndOp.and, EvmSemantics.UInt256.instAndOp,
          HOr.hOr, OrOp.or, EvmSemantics.UInt256.instOrOp] using hT0_eval'
      · constructor
        · rfl
        · rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairNegatedRoundTrace
