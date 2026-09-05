import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRawTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# H30b cached-tail raw trace

This module adapts the old pair trace after its leading `JUMPDEST`.  The
factor is already present as the final suffix word, so the four literal
factor pushes can be replaced by `DUP10`, `DUP9`, `DUP8`, and `DUP7`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCachedTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate

set_option linter.unusedSimpArgs false in
theorem cachedTailF_of_old_raw_f0
    (s : State) (oldPC newPC p0 p1 returnPC : UInt256)
    (r0 r1 : Nat) (working : EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (_hrot0 : r0 ≤ 32) (_hrot1 : r1 ≤ 32)
    (out : State)
    (hraw : runInstrSeq ((pairBeforeJumpTemplate 0 0).drop 1)
      (pairHelperEntry s oldPC p0 p1 returnPC r0 r1 working
        (factor :: rho)) = some out) :
    runInstrSeq (cachedTailFTemplate 0 0)
      (pairHelperEntry s newPC p0 p1 returnPC r0 r1 working
        (factor :: rho)) =
      some { out with pc := pcAfter newPC (cachedTailFTemplate 0 0) } := by
  have hcap (m : Nat) (hm : m ≤ 15) : rho.length + m < 1024 := by
    omega
  have hadd (u v : UInt256) : u + v = u.add v := by
    rfl
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
  have hraw' := hraw
  simp (config := { maxSteps := 3000000 })
    [pairBeforeJumpTemplate, pairFirstBooleanOps, pairSecondBooleanOps,
      pairDup7, pairDup8, pairDup9, pairDup10, pairSwap5, pairSwap7,
      qrot, cfold, op, push1, push2, push4, dup1, dup2, dup3, dup4,
      dup5, dup6, swap1, swap2, swap3, swap4, factor,
      runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      pairHelperEntry, roundWords, List.drop, hrun, hcap,
      State.activeWordsAfterUInt256, hadd, UInt256.succ, Instr.size,
      Instr.size_push, Instr.size_op, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc,
      hswap1, hswap2, hswap3, hswap4, hswap5, hswap6, hswap7] at hraw'
  cases hraw'
  simp (config := { maxSteps := 3000000 })
    [cachedTailFTemplate, cachedQrot10, cachedCfold9, cachedQrot8,
      cachedCfold7, cachedDup10, cachedDup9, cachedDup8, cachedDup7,
      pairFirstBooleanOps, pairSecondBooleanOps,
      pairDup7, pairDup8, pairDup9, pairDup10, pairSwap5, pairSwap7,
      op, push1, push2, push4, dup1, dup2, dup3, dup4,
      dup5, dup6, swap1, swap2, swap3, swap4, factor, mask, c22,
      runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      pairHelperEntry, roundWords, pcAfter, List.drop, hrun, hcap,
      State.activeWordsAfterUInt256, hadd, UInt256.succ, Instr.size,
      Instr.size_push, Instr.size_op, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc,
    hswap1, hswap2, hswap3, hswap4, hswap5, hswap6, hswap7]

set_option linter.unusedSimpArgs false in
private theorem cachedTail_relation (j : Nat) (hj : j < 5)
    (s : State) (oldPC newPC p0 p1 returnPC : UInt256)
    (r0 r1 : Nat) (working : EvmWorking) (constant : UInt256)
    (rho : List UInt256) (hstack : rho.length < 1007)
    (hrun : s.halt = .Running) :
    runInstrSeq (cachedTailFTemplate j constant)
        (pairHelperEntry s newPC p0 p1 returnPC r0 r1 working
          (factor :: rho)) =
      Option.map (fun st => { st with
        pc := pcAfter newPC (cachedTailFTemplate j constant) })
        (runInstrSeq ((pairBeforeJumpTemplate j constant).drop 1)
          (pairHelperEntry s oldPC p0 p1 returnPC r0 r1 working
            (factor :: rho))) := by
  have hcap (m : Nat) (hm : m ≤ 15) : rho.length + m < 1024 := by
    omega
  have hadd (u v : UInt256) : u + v = u.add v := by
    rfl
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
  interval_cases j <;>
    simp (config := { maxSteps := 3000000 })
      [cachedTailFTemplate, cachedQrot10, cachedCfold9, cachedQrot8,
        cachedCfold7, cachedDup10, cachedDup9, cachedDup8, cachedDup7,
        pairBeforeJumpTemplate, pairFirstBooleanOps, pairSecondBooleanOps,
        qrot, cfold, pairDup7, pairDup8,
        pairDup9, pairDup10, pairSwap5, pairSwap7, pairHelperEntry,
        roundWords, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
        List.drop, hrun, hcap, State.activeWordsAfterUInt256, hadd,
        UInt256.succ, Instr.size, Instr.size_push, Instr.size_op,
        List.exchange, Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, pcAfter,
        op, push1, push2, push4, dup1, dup2, dup3, dup4, dup5, dup6,
        swap1, swap2, swap3, swap4, factor, mask, c22,
        hswap1, hswap2, hswap3, hswap4, hswap5, hswap6, hswap7]

set_option linter.unusedSimpArgs false in
theorem cachedTail_of_old_raw
    (j : Nat) (hj : j < 5)
    (s : State) (oldPC newPC p0 p1 returnPC : UInt256)
    (r0 r1 : Nat) (working : EvmWorking) (constant : UInt256)
    (rho : List UInt256) (_hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (_hrot0 : r0 ≤ 32) (_hrot1 : r1 ≤ 32) (out : State)
    (hraw : runInstrSeq ((pairBeforeJumpTemplate j constant).drop 1)
      (pairHelperEntry s oldPC p0 p1 returnPC r0 r1 working
        (factor :: rho)) = some out) :
    runInstrSeq (cachedTailFTemplate j constant)
      (pairHelperEntry s newPC p0 p1 returnPC r0 r1 working
        (factor :: rho)) =
      some { out with pc := pcAfter newPC (cachedTailFTemplate j constant) } := by
  have hrel := cachedTail_relation j hj s oldPC newPC p0 p1 returnPC
    r0 r1 working constant rho hstack hrun
  rw [hraw] at hrel
  simpa using hrel

set_option linter.unusedSimpArgs false in
theorem cachedTail_of_pair_raw
    (j : Nat) (hj : j < 5)
    (s : State) (newPC p0 p1 returnPC : UInt256)
    (r0 r1 : Nat) (working : EvmWorking) (constant : UInt256)
    (rho : List UInt256) (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32) :
    runInstrSeq (cachedTailFTemplate j constant)
      (pairHelperEntry s newPC p0 p1 returnPC r0 r1 working
        (factor :: rho)) =
      some (pairAfterHelperBeforeJump s
        (pcAfter newPC (cachedTailFTemplate j constant))
        returnPC j working p0 p1 r0 r1 constant (factor :: rho)) := by
  have hstack' : (factor :: rho).length < 1012 := by
    simp
    omega
  have hraw := PairRawTrace.runInstrSeq_template j hj s (UInt256.ofNat 0)
    p0 p1 returnPC r0 r1 working constant (factor :: rho) hzero hstack'
    hrun hrot0 hrot1
  have hentry :
      (pairHelperEntry s (UInt256.ofNat 0) p0 p1 returnPC r0 r1 working
        (factor :: rho)).stack.length < 1024 := by
    simp [pairHelperEntry, roundWords, UInt256.succ]
    omega
  have hhead :
      Challenge.EvmProof.Stepper.runInstr (.op .JUMPDEST)
        (pairHelperEntry s (UInt256.ofNat 0) p0 p1 returnPC r0 r1 working
          (factor :: rho)) =
        some (pairHelperEntry s (UInt256.ofNat 1) p0 p1 returnPC r0 r1 working
          (factor :: rho)) := by
    rw [Challenge.EvmProof.Stepper.runInstr, if_pos hentry]
    simp [pairHelperEntry, UInt256.succ]
    exact Challenge.EvmProof.Word.ofNat_add_mod 0 1
  have htail :
      runInstrSeq ((pairBeforeJumpTemplate j constant).drop 1)
        (pairHelperEntry s (UInt256.ofNat 1) p0 p1 returnPC r0 r1 working
          (factor :: rho)) =
        some (pairAfterHelperBeforeJump s
          (pcAfter (UInt256.ofNat 0) (pairBeforeJumpTemplate j constant))
          returnPC j working p0 p1 r0 r1 constant (factor :: rho)) := by
    have hdrop :
        pairBeforeJumpTemplate j constant =
          .op .JUMPDEST :: (pairBeforeJumpTemplate j constant).drop 1 := by
      interval_cases j <;> rfl
    have hpc :
        pcAfter (UInt256.ofNat 0)
            (.op .JUMPDEST :: (pairBeforeJumpTemplate j constant).drop 1) =
          pcAfter (UInt256.ofNat 0) (pairBeforeJumpTemplate j constant) := by
      interval_cases j <;> rfl
    have hraw' := hraw
    rw [hdrop] at hraw'
    simp only [runInstrSeq] at hraw'
    rw [hhead] at hraw'
    rw [hpc] at hraw'
    simp [pairBeforeJumpTemplate, pairHelperEntry, hrun] at hraw'
    simpa [pairBeforeJumpTemplate, pairHelperEntry, List.drop, hrun] using hraw'
  exact cachedTail_of_old_raw j hj s (UInt256.ofNat 1) newPC p0 p1
    returnPC r0 r1 working constant rho hzero hstack hrun hrot0 hrot1 _ htail

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCachedTrace
