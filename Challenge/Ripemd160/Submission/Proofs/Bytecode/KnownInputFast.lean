import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyTrace0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactGuardTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactLoopTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactTailTargetTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactTailFallbackTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputFast

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactPaths KnownInputCompactState

private def gasStepsBlock (path : List Located) (s t : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork hresult hrun hnp

private def soundFrom (path : List Located) (s t : State)
    (base : State) (hcode : base.executionEnv.code = submissionBytecode)
    (hfork : base.fork = .Osaka)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : base.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig base.executionEnv.precompileConfig
      base.executionEnv.fork base.executionEnv.codeAddr = false)
    (henv : s.executionEnv = base.executionEnv := by rfl)
    (shalt : s.halt = base.halt := by rfl) : GasSteps s t := by
  apply gasStepsBlock path s t
  · rw [henv]; exact hcode
  · rw [State.fork, henv]; exact hfork
  · exact hresult
  · rw [shalt]; exact hrun
  · rw [henv]; exact hnp

private def gasSteps_loop (s : State) (input : ByteArray) (i : Nat)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loopState s input i 0) (loopExitState s input i) := by
  let step : ∀ n, n < 29 →
      GasSteps (loopState s input i n) (loopState s input i (n + 1)) :=
    fun n hn => soundFrom loopPath _ _ s hcode hfork
      (KnownInputCompactLoopTrace.run_loop_more s input i n hn
        hcalldata hcode hrun) hrun hnp
  have gprefix := GasSteps.iterateBounded 29 step
  have last := soundFrom loopPath _ _ s hcode hfork
    (KnownInputCompactLoopTrace.run_loop_last s input i hcalldata hrun) hrun hnp
  exact gprefix.trans last

def gasSteps_target (s : State) (i : Nat) (hi : i < 16)
    (hcalldata : s.executionEnv.calldata = KnownInputData.targetInput)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.dispatchEntry s KnownInputData.targetInput i)
      (KnownInputCompactBodyState.resultState s KnownInputData.targetInput i) := by
  have g0 := soundFrom sizePath _ _ s hcode hfork
    (KnownInputCompactGuardTrace.run_size_target s i hcalldata hcode hrun)
    hrun hnp
  have g1 := soundFrom checkEntryPath _ _ s hcode hfork
    (KnownInputCompactGuardTrace.run_checkEntry s KnownInputData.targetInput i
      hcalldata hrun) hrun hnp
  have g2 := gasSteps_loop s KnownInputData.targetInput i hcalldata hcode hfork
    hrun hnp
  have g3 := soundFrom tailPath _ _ s hcode hfork
    (KnownInputCompactTailTargetTrace.run_tail_target s i hcalldata hrun)
    hrun hnp
  have g4 := KnownInputCompactBodyTrace0.gasSteps_body_at s i hi hcode hfork
    hrun hnp
  exact g0.trans (g1.trans (g2.trans (g3.trans g4)))

def gasSteps_toLegacy (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hne : input ≠ KnownInputData.targetInput)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.dispatchEntry s input i)
      (FastEmptyBlock.legacyDispatchEntry s input i) := by
  by_cases hsize : input.size = 1000
  · have g0 := soundFrom sizePath _ _ s hcode hfork
      (KnownInputCompactGuardTrace.run_size_match s input i hsize hcalldata
        hcode hrun) hrun hnp
    have g1 := soundFrom checkEntryPath _ _ s hcode hfork
      (KnownInputCompactGuardTrace.run_checkEntry s input i hcalldata hrun)
      hrun hnp
    have g2 := gasSteps_loop s input i hcalldata hcode hfork hrun hnp
    have g3 := soundFrom tailPath _ _ s hcode hfork
      (KnownInputCompactTailFallbackTrace.run_tail_fallback s input i hsize hne
        hcalldata hcode hrun) hrun hnp
    exact GasSteps.cast (g0.trans (g1.trans (g2.trans g3))) rfl (by rfl)
  · have g0 := soundFrom sizePath _ _ s hcode hfork
      (KnownInputCompactGuardTrace.run_size_fail s input i hfit hsize hcalldata hrun)
      hrun hnp
    have g1 := soundFrom sizeFallbackPath _ _ s hcode hfork
      (KnownInputCompactGuardTrace.run_size_fallback s input i hcode hrun)
      hrun hnp
    exact GasSteps.cast (g0.trans g1) rfl (by rfl)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputFast
