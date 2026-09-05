import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairSelectRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairNegatedRoundTrace

set_option warningAsError true
set_option maxRecDepth 30000

/-!
# H24 paired-round raw dispatch

The five raw evaluator proofs stop immediately before the helper `JUMP`.
This file only selects the proof for the helper group.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRawTrace

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairSelectRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairNegatedRoundTrace

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_template (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 returnPC : UInt256)
    (r0 r1 : Nat) (working : Compression.EvmWorking) (constant : UInt256)
    (rest : List UInt256) (hzero : j = 0 → constant = 0)
    (hstack : rest.length < 1012) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32) :
    runInstrSeq (pairBeforeJumpTemplate j constant)
      (pairHelperEntry s startPC p0 p1 returnPC r0 r1 working rest) =
    some (pairAfterHelperBeforeJump s
      (pcAfter startPC (pairBeforeJumpTemplate j constant))
      returnPC j working p0 p1 r0 r1 constant rest) := by
  interval_cases j
  · have hc := hzero rfl
    subst constant
    exact PairRoundTrace.runInstrSeq_f0 s startPC p0 p1 returnPC r0 r1
      working rest hstack hrun hrot0 hrot1
  · exact PairSelectRoundTrace.runInstrSeq_f1 s startPC p0 p1 returnPC r0 r1
      working constant rest hstack hrun hrot0 hrot1
  · exact PairNegatedRoundTrace.runInstrSeq_f2 s startPC p0 p1 returnPC r0 r1
      working constant rest hstack hrun hrot0 hrot1
  · exact PairSelectRoundTrace.runInstrSeq_f3 s startPC p0 p1 returnPC r0 r1
      working constant rest hstack hrun hrot0 hrot1
  · exact PairNegatedRoundTrace.runInstrSeq_f4 s startPC p0 p1 returnPC r0 r1
      working constant rest hstack hrun hrot0 hrot1

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRawTrace
