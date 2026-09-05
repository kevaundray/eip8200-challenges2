import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedSelectRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedNegatedRoundTrace

set_option warningAsError true
set_option maxRecDepth 30000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRawTrace

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StackRoundTrace SharedRoundTemplate SharedRoundTrace

theorem runInstrSeq_template (j : Nat) (hj : j < 5)
    (s : State) (startPC xAddress returnPC : UInt256)
    (rotation : Nat) (working : Compression.EvmWorking) (constant : UInt256)
    (rest : List UInt256) (hzero : j = 0 → constant = 0)
    (hstack : rest.length < 1013) (hrun : s.halt = .Running) (hrot : rotation ≤ 32) :
    runInstrSeq (helperBeforeJumpTemplate j xAddress rotation constant)
      (helperEntry s startPC xAddress rotation returnPC working rest) =
    some (afterHelperBeforeJump s
      (pcAfter startPC (helperBeforeJumpTemplate j xAddress rotation constant))
      returnPC j working xAddress rotation constant rest) := by
  interval_cases j
  · have hc := hzero rfl
    subst constant
    exact SharedRoundTrace.runInstrSeq_f0 s startPC xAddress returnPC rotation working rest hstack hrun hrot
  · exact SharedSelectRoundTrace.runInstrSeq_f1 s startPC xAddress returnPC rotation working constant rest hstack hrun hrot
  · exact SharedNegatedRoundTrace.runInstrSeq_f2 s startPC xAddress returnPC rotation working constant rest hstack hrun hrot
  · exact SharedSelectRoundTrace.runInstrSeq_f3 s startPC xAddress returnPC rotation working constant rest hstack hrun hrot
  · exact SharedNegatedRoundTrace.runInstrSeq_f4 s startPC xAddress returnPC rotation working constant rest hstack hrun hrot

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRawTrace
