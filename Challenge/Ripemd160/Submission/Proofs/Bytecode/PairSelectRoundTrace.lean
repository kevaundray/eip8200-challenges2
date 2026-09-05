import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationMultiply

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# H27 paired selecting-round evaluator traces

These theorems evaluate the pure paired helper body for forms `f1` and `f3`.
The proof is generic in the surrounding state, memory, and stack words.  The
final `JUMP` is outside the before-jump template.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairSelectRoundTrace

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

private theorem pair_hswap1 (u v : UInt256) (rho : List UInt256) :
    (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho

private theorem pair_hswap2 (u v w : UInt256) (rho : List UInt256) :
    (u :: v :: w :: rho).exchange 0 2 =
      some (w :: v :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u w [v] rho

private theorem pair_hswap3 (u v w z : UInt256) (rho : List UInt256) :
    (u :: v :: w :: z :: rho).exchange 0 3 =
      some (z :: v :: w :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u z [v, w] rho

private theorem pair_hswap4 (u v w z q : UInt256) (rho : List UInt256) :
    (u :: v :: w :: z :: q :: rho).exchange 0 4 =
      some (q :: v :: w :: z :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u q [v, w, z] rho

private theorem pair_hswap5 (u v w z q r : UInt256) (rho : List UInt256) :
    (u :: v :: w :: z :: q :: r :: rho).exchange 0 5 =
      some (r :: v :: w :: z :: q :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u r [v, w, z, q] rho

private theorem pair_hswap6 (u v w z q r t : UInt256) (rho : List UInt256) :
    (u :: v :: w :: z :: q :: r :: t :: rho).exchange 0 6 =
      some (t :: v :: w :: z :: q :: r :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u t [v, w, z, q, r] rho

private theorem pair_hswap7 (u v w z q r t k : UInt256) (rho : List UInt256) :
    (u :: v :: w :: z :: q :: r :: t :: k :: rho).exchange 0 7 =
      some (k :: v :: w :: z :: q :: r :: t :: u :: rho) := by
  simpa using YulEvmCompiler.exchange_swap u k [v, w, z, q, r, t] rho

private theorem pair_hadd (u v : UInt256) : u + v = u.add v := by
  rfl

private theorem pair_hzero (u : UInt256) : u.add (0 : UInt256) = u := by
  apply word_ext
  change (u.val + (0 : UInt256).val).val = u.val.val
  rw [Fin.val_add]
  change (u.val.val + 0) % UInt256.size = u.val.val
  rw [Nat.add_zero, Nat.mod_eq_of_lt u.val.isLt]

private theorem pair_hcomm (u v : UInt256) : u.add v = v.add u := by
  exact word_add_comm u v

private theorem pair_hxorcomm (u v : UInt256) : u.xor v = v.xor u := by
  exact BooleanSelect.xor_comm u v

private theorem pair_hbase_f1_sum (constant a b c d word : UInt256) :
    constant.add (a.add (word.add (d.xor (b.land (c.xor d))))) =
      constant.add ((a.add (d.xor ((c.xor d).land b))).add word) := by
  rw [Word.land_comm b (c.xor d),
    pair_hcomm word (d.xor ((c.xor d).land b))]
  exact congrArg (fun z : UInt256 => constant.add z)
    (word_add_assoc a (d.xor ((c.xor d).land b)) word).symm

private theorem pair_hbase_f3_sum (constant a b c d word : UInt256) :
    constant.add (a.add (word.add (c.xor (d.land (b.xor c))))) =
      constant.add ((a.add (c.xor ((b.xor c).land d))).add word) := by
  rw [Word.land_comm d (b.xor c),
    pair_hcomm word (c.xor ((b.xor c).land d))]
  exact congrArg (fun z : UInt256 => constant.add z)
    (word_add_assoc a (c.xor ((b.xor c).land d)) word).symm

private theorem pair_hsum (constant a f word : UInt256) :
    constant.add (a.add (word.add f)) =
      constant.add ((a.add f).add word) := by
  rw [pair_hcomm word f]
  exact congrArg (fun z : UInt256 => constant.add z)
    (word_add_assoc a f word).symm

private theorem factor_mul_mask_land (q : UInt256) :
    UInt256.mul (UInt256.ofNat (0x100000001 : Nat)) (mask.land q) =
      (mask.land q).lor
        (UInt256.shiftLeft (mask.land q) (UInt256.ofNat 32)) := by
  exact factor_mul_eq_or_shift (mask.land q) (mask_land_toNat_lt q)

private theorem factor_mul_mask_land_expanded (q : UInt256) :
    UInt256.mul (UInt256.ofNat 4294967297)
        ((UInt256.ofNat 4294967295).land q) =
      ((UInt256.ofNat 4294967295).land q).lor
        (UInt256.shiftLeft ((UInt256.ofNat 4294967295).land q)
          (UInt256.ofNat 32)) := by
  simpa only [mask] using factor_mul_mask_land q

private theorem mul_op (u v : UInt256) : u * v = UInt256.mul u v := by
  rfl

private theorem activeWordsAfter32_lt (curr off : Nat)
    (hcurr : curr < 2 ^ 256) (hoff : off < 2 ^ 256) :
    MachineState.activeWordsAfter curr off 32 < 2 ^ 256 := by
  unfold MachineState.activeWordsAfter
  split
  · exact hcurr
  · dsimp only
    apply (Nat.max_lt).2
    constructor
    · exact hcurr
    · have hnum : off + 32 - 1 < (2 ^ 256 - 1) * 32 := by
        omega
      have hdiv : (off + 32 - 1) / 32 < 2 ^ 256 - 1 := by
        apply (Nat.div_lt_iff_lt_mul (by norm_num)).2
        exact hnum
      omega

private theorem pair_activeWords (s : State) (p0 p1 : UInt256) :
    ({s with activeWords := s.activeWordsAfterUInt256 p0.toNat 32} : State).activeWordsAfterUInt256
        p1.toNat 32 =
      s.activeWordsAfterUInt256_2 p0.toNat 32 p1.toNat 32 := by
  have h0 : MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32 <
      2 ^ 256 :=
    activeWordsAfter32_lt s.activeWords.toNat p0.toNat
      s.activeWords.val.isLt p0.val.isLt
  unfold State.activeWordsAfterUInt256 State.activeWordsAfterUInt256_2
  rw [word_toNat_ofNat, Nat.mod_eq_of_lt h0]

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_f1 (s : State) (startPC p0 p1 returnPC : UInt256)
    (r0 r1 : Nat) (working : EvmWorking) (constant : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1012)
    (hrun : s.halt = .Running) (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32) :
    runInstrSeq (pairBeforeJumpTemplate 1 constant)
        (pairHelperEntry s startPC p0 p1 returnPC r0 r1 working rest) =
      some (pairAfterHelperBeforeJump s
        (pcAfter startPC (pairBeforeJumpTemplate 1 constant))
        returnPC 1 working p0 p1 r0 r1 constant rest) := by
  have hcap (m : Nat) (hm : m ≤ 12) : rest.length + m < 1024 := by
    omega
  let word0 : UInt256 := MachineState.readWord s.memory p0.toNat
  let word1 : UInt256 := MachineState.readWord s.memory p1.toNat
  let f0e : UInt256 :=
    working.d.xor (working.b.land (working.c.xor working.d))
  let f0t : UInt256 :=
    working.d.xor ((working.c.xor working.d).land working.b)
  let q0e : UInt256 := constant.add (working.a.add (word0.add f0e))
  let q0t : UInt256 := constant.add ((working.a.add f0t).add word0)
  have hq0 : q0e = q0t := by
    exact pair_hbase_f1_sum constant working.a working.b working.c working.d
      word0
  let b1e : UInt256 := UInt256.land mask
    (working.e.add
      (UInt256.shiftRight
        ((mask.land q0e).lor
          ((mask.land q0e).shiftLeft (UInt256.ofNat 32)))
        (UInt256.ofNat (32 - r0))))
  let c1t : UInt256 := ScratchLow.rawC10 working.c
  let t0 : UInt256 := UInt256.land
    (working.e.add
      (((q0t.land mask).shiftLeft (UInt256.ofNat r0)).lor
        ((q0t.land mask).shiftRight (UInt256.ofNat (32 - r0)))))
    mask
  have hT0 : b1e = t0 := by
    simp only [b1e, t0]
    rw [hq0]
    rw [pair_hcomm working.e]
    rw [pair_hcomm working.e]
    exact raw_rotate_or_fold q0t working.e r0
      (mask_land_toNat_lt _) hrot0
  let q1c : UInt256 := constant.add
    ((working.e.add
      (c1t.xor ((working.b.xor c1t).land t0))).add word1)
  have hq1c :
      constant.add
          (working.e.add
            (word1.add (c1t.xor ((working.b.xor c1t).land t0)))) = q1c := by
    simpa [q1c] using pair_hsum constant working.e
      (c1t.xor ((working.b.xor c1t).land t0)) word1
  have hsecondRotC :
      UInt256.land mask
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
          mask :=
    raw_rotate_or_fold q1c working.d r1 (mask_land_toNat_lt _) hrot1
  have hsecondRotC' :
      UInt256.land mask
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
      UInt256.land mask
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
              rw [pair_hcomm]
  have hT0_eval := hT0
  simp only [b1e, t0, q0e, q0t, word0, f0e, f0t] at hT0_eval
  have hT0_eval' := hT0_eval
  simp only [mask] at hT0_eval'
  have hq1c' := hq1c
  simp only [word1, t0, c1t, q0t, word0, f0t, mask,
    ScratchLow.rawC10] at hq1c'
  simp (config := { maxSteps := 3000000 })
    [pairBeforeJumpTemplate, pairFirstBooleanOps, pairSecondBooleanOps,
      pairDup7, pairDup8, pairDup9, pairDup10, pairSwap5, pairSwap6,
      pairSwap7, qrot, mul_op, factor_mul_mask_land,
      factor_mul_mask_land_expanded, cfold, op, push1, push2, push4, dup1, dup2, dup3,
      dup4, dup5, dup6, swap1, swap2, swap3, swap4, mask, c10, c22,
      runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      pairHelperEntry, pairAfterHelperBeforeJump, pairWorking, roundWords,
      pcAfter, ScratchLow.rawRound, StackRound.stackF,
      StackRound.stackSum, StackRound.stackRawRot,
      HMul.hMul, Mul.mul, ScratchLow.rawC10,
      Word.mask32, List.exchange, hrun, hcap, pair_hswap1, pair_hswap2,
      pair_hswap3, pair_hswap4, pair_hswap5, pair_hswap6, pair_hswap7,
      UInt256.succ, Instr.size, Instr.size_push, Instr.size_op,
      Nat.add_assoc, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, Word.land_comm, Word.lor_comm,
      BooleanSelect.xor_comm,
      pair_hadd, pair_hzero, pair_hcomm, pair_hxorcomm]
  constructor
  · simpa [State.activeWordsAfterUInt256] using pair_activeWords s p0 p1
  · constructor
    · rw [hT0_eval']
      rw [pair_hcomm working.d]
      rw [hq1c']
      simpa [mask, q1c, t0, c1t, q0e, q0t, word0, word1, f0e, f0t,
        ScratchLow.rawC10, Word.mask32, Word.land_comm, UInt256.xor,
        HXor.hXor,
        HAnd.hAnd, AndOp.and, EvmSemantics.UInt256.instAndOp,
        HOr.hOr, OrOp.or, EvmSemantics.UInt256.instOrOp,
        BooleanSelect.xor_comm] using hsecondRotC'
    · simpa [q0e, q0t, word0, f0e, f0t, mask, UInt256.xor,
        HXor.hXor, HAnd.hAnd, AndOp.and,
        EvmSemantics.UInt256.instAndOp, HOr.hOr, OrOp.or,
        EvmSemantics.UInt256.instOrOp] using hT0_eval'

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_f3 (s : State) (startPC p0 p1 returnPC : UInt256)
    (r0 r1 : Nat) (working : EvmWorking) (constant : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1012)
    (hrun : s.halt = .Running) (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32) :
    runInstrSeq (pairBeforeJumpTemplate 3 constant)
        (pairHelperEntry s startPC p0 p1 returnPC r0 r1 working rest) =
      some (pairAfterHelperBeforeJump s
        (pcAfter startPC (pairBeforeJumpTemplate 3 constant))
        returnPC 3 working p0 p1 r0 r1 constant rest) := by
  have hcap (m : Nat) (hm : m ≤ 12) : rest.length + m < 1024 := by
    omega
  let word0 : UInt256 := MachineState.readWord s.memory p0.toNat
  let word1 : UInt256 := MachineState.readWord s.memory p1.toNat
  let f0e : UInt256 :=
    working.c.xor (working.d.land (working.b.xor working.c))
  let f0t : UInt256 :=
    working.c.xor ((working.b.xor working.c).land working.d)
  let q0e : UInt256 := constant.add (working.a.add (word0.add f0e))
  let q0t : UInt256 := constant.add ((working.a.add f0t).add word0)
  have hq0 : q0e = q0t := by
    exact pair_hbase_f3_sum constant working.a working.b working.c working.d
      word0
  let b1e : UInt256 := UInt256.land mask
    (working.e.add
      (UInt256.shiftRight
        ((mask.land q0e).lor
          ((mask.land q0e).shiftLeft (UInt256.ofNat 32)))
        (UInt256.ofNat (32 - r0))))
  let c1t : UInt256 := ScratchLow.rawC10 working.c
  let t0 : UInt256 := UInt256.land
    (working.e.add
      (((q0t.land mask).shiftLeft (UInt256.ofNat r0)).lor
        ((q0t.land mask).shiftRight (UInt256.ofNat (32 - r0)))))
    mask
  have hT0 : b1e = t0 := by
    simp only [b1e, t0]
    rw [hq0]
    rw [pair_hcomm working.e]
    rw [pair_hcomm working.e]
    exact raw_rotate_or_fold q0t working.e r0
      (mask_land_toNat_lt _) hrot0
  let q1c : UInt256 := constant.add
    ((working.e.add
      (working.b.xor (c1t.land (working.b.xor t0)))).add word1)
  have hq1c :
      constant.add
          (working.e.add
            (word1.add (working.b.xor (c1t.land (working.b.xor t0))))) = q1c := by
    simpa [q1c] using pair_hsum constant working.e
      (working.b.xor (c1t.land (working.b.xor t0))) word1
  have hsecondRotC :
      UInt256.land mask
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
          mask :=
    raw_rotate_or_fold q1c working.d r1 (mask_land_toNat_lt _) hrot1
  have hsecondRotC' :
      UInt256.land mask
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
      UInt256.land mask
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
              rw [pair_hcomm]
  have hT0_eval := hT0
  simp only [b1e, t0, q0e, q0t, word0, f0e, f0t] at hT0_eval
  have hT0_eval' := hT0_eval
  simp only [mask] at hT0_eval'
  have hq1c' := hq1c
  simp only [word1, t0, c1t, q0t, word0, f0t, mask,
    ScratchLow.rawC10] at hq1c'
  simp (config := { maxSteps := 3000000 })
    [pairBeforeJumpTemplate, pairFirstBooleanOps, pairSecondBooleanOps,
      pairDup7, pairDup8, pairDup9, pairDup10, pairSwap5, pairSwap6,
      pairSwap7, qrot, mul_op, factor_mul_mask_land,
      factor_mul_mask_land_expanded, cfold, op, push1, push2, push4, dup1, dup2, dup3,
      dup4, dup5, dup6, swap1, swap2, swap3, swap4, mask, c10, c22,
      runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      pairHelperEntry, pairAfterHelperBeforeJump, pairWorking, roundWords,
      pcAfter, ScratchLow.rawRound, StackRound.stackF,
      StackRound.stackSum, StackRound.stackRawRot,
      HMul.hMul, Mul.mul, ScratchLow.rawC10,
      Word.mask32, List.exchange, hrun, hcap, pair_hswap1, pair_hswap2,
      pair_hswap3, pair_hswap4, pair_hswap5, pair_hswap6, pair_hswap7,
      UInt256.succ, Instr.size, Instr.size_push, Instr.size_op,
      Nat.add_assoc, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, Word.land_comm, Word.lor_comm,
      BooleanSelect.xor_comm,
      pair_hadd, pair_hzero, pair_hcomm, pair_hxorcomm]
  constructor
  · simpa [State.activeWordsAfterUInt256] using pair_activeWords s p0 p1
  · constructor
    · rw [hT0_eval']
      rw [pair_hcomm working.d]
      rw [hq1c']
      simpa [mask, q1c, t0, c1t, q0e, q0t, word0, word1, f0e, f0t,
        ScratchLow.rawC10, Word.mask32, Word.land_comm, UInt256.xor,
        HXor.hXor,
        HAnd.hAnd, AndOp.and, EvmSemantics.UInt256.instAndOp,
        HOr.hOr, OrOp.or, EvmSemantics.UInt256.instOrOp,
        BooleanSelect.xor_comm] using hsecondRotC'
    · simpa [q0e, q0t, word0, f0e, f0t, mask, UInt256.xor,
        HXor.hXor, HAnd.hAnd, AndOp.and,
        EvmSemantics.UInt256.instAndOp, HOr.hOr, OrOp.or,
        EvmSemantics.UInt256.instOrOp] using hT0_eval'

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairSelectRoundTrace
