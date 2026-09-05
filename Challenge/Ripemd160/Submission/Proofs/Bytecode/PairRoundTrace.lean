import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# H27 paired-round evaluator trace

The theorem below proves the f0 pair helper on arbitrary 256-bit stack and
memory words.  The stack-capacity premise is strict and accounts for the
maximum twelve values above `rest`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTrace

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

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_f0 (s : State) (startPC p0 p1 returnPC : UInt256)
    (r0 r1 : Nat) (working : EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1012) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32) :
    runInstrSeq (pairBeforeJumpTemplate 0 0)
        (pairHelperEntry s startPC p0 p1 returnPC r0 r1 working rest) =
      some (pairAfterHelperBeforeJump s
        (pcAfter startPC (pairBeforeJumpTemplate 0 0))
        returnPC 0 working p0 p1 r0 r1 0 rest) := by
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
  have hzero (u : UInt256) : u.add (0 : UInt256) = u := by
    apply word_ext
    change (u.val + (0 : UInt256).val).val = u.val.val
    rw [Fin.val_add]
    change (u.val.val + 0) % UInt256.size = u.val.val
    rw [Nat.add_zero, Nat.mod_eq_of_lt u.val.isLt]
  have hcomm (u v : UInt256) : u.add v = v.add u := by
    exact word_add_comm u v
  have hxorcomm (u v : UInt256) : u.xor v = v.xor u := by
    exact BooleanSelect.xor_comm u v
  have word_add_assoc (u v w : UInt256) :
      (u.add v).add w = u.add (v.add w) := by
    apply word_ext
    change ((u.val + v.val) + w.val).val =
      (u.val + (v.val + w.val)).val
    simp [Fin.add_def, Nat.add_assoc]
  have hbase (x : EvmWorking) (word : UInt256) :
      x.a.add (word.add (x.d.xor (x.b.xor x.c))) =
        (x.a.add (x.d.xor (x.b.xor x.c))).add word := by
    rw [hcomm word]
    exact (word_add_assoc x.a (x.d.xor (x.b.xor x.c)) word).symm
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
          simpa [UInt256.size] using hoff
        have hdiv : (off + 32 - 1) / 32 < 2 ^ 256 - 1 := by
          apply (Nat.div_lt_iff_lt_mul (by norm_num)).2
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
  let word0 : UInt256 := MachineState.readWord s.memory p0.toNat
  let word1 : UInt256 := MachineState.readWord s.memory p1.toNat
  let f0 : UInt256 := working.d.xor (working.b.xor working.c)
  let q0 : UInt256 := (working.a.add f0).add word0
  have hq0 : word0.add (working.a.add f0) = q0 := by
    exact hcomm _ _
  have hfirstRot :
      UInt256.land mask
          (UInt256.add
            (UInt256.shiftRight
              ((mask.land q0).lor
                ((mask.land q0).shiftLeft (UInt256.ofNat 32)))
              (UInt256.ofNat (32 - r0))) working.e) =
        UInt256.land
          (UInt256.add
            (((q0.land mask).shiftLeft (UInt256.ofNat r0)).lor
              ((q0.land mask).shiftRight (UInt256.ofNat (32 - r0))))
            working.e)
          mask :=
    raw_rotate_or_fold q0 working.e r0 (mask_land_toNat_lt _) hrot0
  have hT0 :
      UInt256.land mask
          (UInt256.add working.e
            (UInt256.shiftRight
              ((mask.land (word0.add (working.a.add f0))).lor
                ((mask.land (word0.add (working.a.add f0))).shiftLeft
                  (UInt256.ofNat 32)))
              (UInt256.ofNat (32 - r0)))) =
        UInt256.land
          (UInt256.add working.e
            (((q0.land mask).shiftLeft (UInt256.ofNat r0)).lor
              ((q0.land mask).shiftRight (UInt256.ofNat (32 - r0)))))
          mask := by
    calc
      UInt256.land mask
          (UInt256.add working.e
            (UInt256.shiftRight
              ((mask.land (word0.add (working.a.add f0))).lor
                ((mask.land (word0.add (working.a.add f0))).shiftLeft
                  (UInt256.ofNat 32)))
              (UInt256.ofNat (32 - r0)))) =
          UInt256.land mask
            (UInt256.add working.e
              (UInt256.shiftRight
                ((mask.land q0).lor
                  ((mask.land q0).shiftLeft (UInt256.ofNat 32)))
                (UInt256.ofNat (32 - r0)))) := by rw [hq0]
      _ = UInt256.land mask
            (UInt256.add
              (UInt256.shiftRight
                ((mask.land q0).lor
                  ((mask.land q0).shiftLeft (UInt256.ofNat 32)))
                (UInt256.ofNat (32 - r0))) working.e) := by
              rw [hcomm]
      _ = UInt256.land
            (UInt256.add
              (((q0.land mask).shiftLeft (UInt256.ofNat r0)).lor
                ((q0.land mask).shiftRight (UInt256.ofNat (32 - r0))))
              working.e) mask := hfirstRot
      _ = UInt256.land
            (UInt256.add working.e
              (((q0.land mask).shiftLeft (UInt256.ofNat r0)).lor
                ((q0.land mask).shiftRight (UInt256.ofNat (32 - r0)))))
            mask := by rw [hcomm]
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
  let q1c : UInt256 :=
    word1.add (working.e.add ((working.b.xor t0).xor
      (ScratchLow.rawC10 working.c)))
  have hq1c :
      working.e.add (word1.add ((ScratchLow.rawC10 working.c).xor
        (working.b.xor t0))) = q1c := by
    calc
      working.e.add
          (word1.add ((ScratchLow.rawC10 working.c).xor (working.b.xor t0))) =
          working.e.add (word1.add ((working.b.xor t0).xor
            (ScratchLow.rawC10 working.c))) := by
              rw [hxorcomm]
      _ = (working.e.add word1).add
            ((working.b.xor t0).xor (ScratchLow.rawC10 working.c)) := by
              exact (word_add_assoc working.e word1
                ((working.b.xor t0).xor (ScratchLow.rawC10 working.c))).symm
      _ = (word1.add working.e).add
            ((working.b.xor t0).xor (ScratchLow.rawC10 working.c)) := by
              rw [hcomm working.e word1]
      _ = word1.add (working.e.add ((working.b.xor t0).xor
            (ScratchLow.rawC10 working.c))) := by
              exact word_add_assoc word1 working.e
                ((working.b.xor t0).xor (ScratchLow.rawC10 working.c))
      _ = q1c := rfl
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
              ((q1c.land mask).shiftRight (UInt256.ofNat (32 - r1)))) )
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
              rw [hcomm]
  have hmul_mask (q : UInt256) :
      UInt256.mul (UInt256.ofNat (0x100000001 : Nat))
          (UInt256.land (UInt256.ofNat 0xffffffff) q) =
        UInt256.lor (UInt256.land (UInt256.ofNat 0xffffffff) q)
          (UInt256.shiftLeft (UInt256.land (UInt256.ofNat 0xffffffff) q)
            (UInt256.ofNat 32)) := by
    have hmask : UInt256.land (UInt256.ofNat 0xffffffff) q =
        _root_.Challenge.EvmProof.Word.mask32 q := by
      unfold _root_.Challenge.EvmProof.Word.mask32
      exact Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.land_comm _ _
    rw [hmask]
    simpa only [HOr.hOr, OrOp.or, EvmSemantics.UInt256.instOrOp] using
      (RotationMultiply.factor_mul_mask32_eq_or_shift q)
  have hq1c' := hq1c
  simp only [word1, t0, mask, ScratchLow.rawC10] at hq1c'
  simp (config := { maxSteps := 3000000 })
    [pairBeforeJumpTemplate, pairFirstBooleanOps, pairSecondBooleanOps,
      pairDup7, pairDup8, pairDup9, pairDup10, pairSwap5, pairSwap7,
      qrot, cfold, op, push1, push2, push4, dup1, dup2, dup3, dup4,
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
      State.activeWordsAfterUInt256_2,
      hadd, hzero, hcomm, hxorcomm, hbase, hactive0, hactive0mod,
      hmul_mask]
  constructor
  · simpa [UInt256.size] using congrArg UInt256.ofNat hactivePair
  · constructor
    · rw [hT0_eval']
      rw [hcomm working.d]
      rw [hq1c']
      simpa [mask, q1c, t0, q0, word0, word1, f0,
        ScratchLow.rawC10, Word.mask32, UInt256.xor, HXor.hXor,
        HAnd.hAnd, AndOp.and,
        EvmSemantics.UInt256.instAndOp, HOr.hOr, OrOp.or,
        EvmSemantics.UInt256.instOrOp, BooleanSelect.xor_comm] using
        hsecondRotC'
    · constructor
      · simpa [q0, word0, f0, UInt256.xor, HXor.hXor,
          HAnd.hAnd, AndOp.and,
          EvmSemantics.UInt256.instAndOp, HOr.hOr, OrOp.or,
          EvmSemantics.UInt256.instOrOp] using hT0_eval'
      · constructor
        · rfl
        · rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTrace
