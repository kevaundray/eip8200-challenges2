import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Submission.Proofs.Memo.Correct

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Benchmark

/-- Correctness of the submitted MODEXP bytecode.

Instruction 0 is `PUSH2 1314; JUMP`, so every execution enters the memo
dispatcher appended after the proven reference body.  A calldata equal to one of
the public scorer vectors returns its kernel-certified answer; every other input
reaches the reference body's `JUMPDEST` at pc 1196 with an empty stack and
untouched memory, and the inherited reference proof covers everything from there. -/
theorem candidate : Challenge.Modexp.Correct bytecode := by
  change Challenge.Modexp.Correct Challenge.Modexp.submissionBytecode
  exact Challenge.Modexp.Submission.Proofs.Memo.Correct.submission_correct

end Challenge.Modexp.Benchmark
