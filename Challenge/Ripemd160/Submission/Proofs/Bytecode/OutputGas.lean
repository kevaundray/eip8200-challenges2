import Challenge.Ripemd160.Submission.Proofs.Bytecode.Output

set_option warningAsError true

/-!
# RIPEMD-160 output gas facts

The `GasSteps` certificates in `Output` carry the exact executable cost,
including memory expansion.  These facts separately expose the Osaka base
cost of every straight-line segment; together with
`Output.gasSteps_block_cost`, they make both the fixed work and the dynamic
memory component auditable.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.OutputGas

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private def osakaBaseCost : Instr → Nat
  | .push width _ => Gas.baseCost .Osaka (.Push ⟨width⟩)
  | .op op => Gas.baseCost .Osaka op

def pathBaseCost {artifact : Challenge.EvmProof.ProgramArtifact}
    (path : List (Challenge.EvmProof.Stepper.Located artifact .Osaka)) : Nat :=
  (path.map (fun located => osakaBaseCost located.instruction)).sum

@[simp] theorem prelude_base : pathBaseCost OutputTrace.preludePath = 12 := by rfl
@[simp] theorem outerTest_base : pathBaseCost OutputTrace.outerTestPath = 26 := by rfl
@[simp] theorem hAtCall_base : pathBaseCost OutputTrace.hAtCallPath = 22 := by rfl
@[simp] theorem hAt_base : pathBaseCost OutputTrace.hAtPath = 30 := by rfl
@[simp] theorem writeCall_base : pathBaseCost OutputTrace.writeCallPath = 27 := by rfl
@[simp] theorem writeInit_base : pathBaseCost OutputTrace.writeInitPath = 3 := by rfl
@[simp] theorem writeTest_base : pathBaseCost OutputTrace.writeTestPath = 26 := by rfl
@[simp] theorem writeBody_base : pathBaseCost OutputTrace.writeBodyPath = 58 := by rfl
@[simp] theorem writeExit_base : pathBaseCost OutputTrace.writeExitPath = 15 := by rfl
@[simp] theorem outerNext_base : pathBaseCost OutputTrace.outerNextPath = 26 := by rfl
@[simp] theorem finish_base : pathBaseCost OutputTrace.finishPath = 8 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.OutputGas
