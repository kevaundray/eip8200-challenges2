import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairCallTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCallTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairMultiplyLift

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

/-!
# H24 paired-round helper composition

The paired helper evaluator is supplied as a genuine `GasSteps` argument.
This file composes that trace with the six-push call and the common return
trace.  Boolean dispatch remains outside this interface.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairHelperTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState

structure RoundSite (artifact : ProgramArtifact) (fork : Fork)
    (j : Nat) (p0 p1 : UInt256) (r0 r1 : Nat) (constant : UInt256) where
  returnPC : UInt256
  helperPC : UInt256
  call : PairCallTrace.CallSite artifact fork returnPC p0 p1 helperPC r0 r1
  helper : GenericRoundSite artifact fork (pairBeforeJumpTemplate j constant)
  helper_start : helper.startPC = helperPC
  helperJump : LocatedSite artifact fork
  helper_jump_instr : helperJump.located.instruction = .op .JUMP
  helper_end : helperJump.pc = helper.endPC
  returnSite : LocatedSite artifact fork
  return_instr : returnSite.located.instruction = .op .JUMPDEST
  return_at : returnSite.pc = returnPC
  helper_valid : Decode.isValidJumpDest artifact.code helperPC.toNat = true
  return_valid : Decode.isValidJumpDest artifact.code returnPC.toNat = true

theorem template_advances (j : Nat) (hj : j < 5) (constant : UInt256) :
    ∀ instruction ∈ pairBeforeJumpTemplate j constant,
      PairMultiplyLift.Advances instruction := by
  intro instruction hmem
  interval_cases j <;>
    simp [pairBeforeJumpTemplate, pairFirstBooleanOps, pairSecondBooleanOps,
      pairDup7, pairDup8, pairDup9, pairDup10, pairSwap5, pairSwap7,
      qrot, cfold] at hmem <;>
    simp_all [PairMultiplyLift.Advances, SharedCallTrace.Advances, op, push1, push4, dup2,
      dup3, dup5, dup6, swap1, swap2, swap4] <;>
    aesop (add safe constructors StraightLine)

theorem runLocatedBlock_pair_of_raw {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (hj : j < 5) (p0 p1 : UInt256) (r0 r1 : Nat)
    (constant : UInt256)
    (site : GenericRoundSite artifact fork (pairBeforeJumpTemplate j constant))
    (s : State) (returnPC : UInt256) (working : Compression.EvmWorking)
    (rest : List UInt256)
    (hraw :
      runInstrSeq (pairBeforeJumpTemplate j constant)
        (PairRoundState.pairHelperEntry s site.startPC p0 p1 returnPC
          r0 r1 working rest) =
      some (PairRoundState.pairAfterHelperBeforeJump s
        (pcAfter site.startPC (pairBeforeJumpTemplate j constant))
        returnPC j working p0 p1 r0 r1 constant rest)) :
    Stepper.runLocatedBlock site.path
      (PairRoundState.pairHelperEntry s site.startPC p0 p1 returnPC
        r0 r1 working rest) =
      some (PairRoundState.pairAfterHelperBeforeJump s site.endPC returnPC
        j working p0 p1 r0 r1 constant rest) := by
  have hend : site.endPC = pcAfter site.startPC
      (pairBeforeJumpTemplate j constant) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [PairMultiplyLift.runLocatedBlock_eq_raw site
    (template_advances j hj constant)
    (PairRoundState.pairHelperEntry s site.startPC p0 p1 returnPC
      r0 r1 working rest) rfl]
  rw [hraw, ← hend]

def gasSteps_helper_of_raw {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (hj : j < 5) (p0 p1 : UInt256) (r0 r1 : Nat)
    (constant : UInt256)
    (site : GenericRoundSite artifact fork (pairBeforeJumpTemplate j constant))
    (s : State) (returnPC : UInt256) (working : Compression.EvmWorking)
    (rest : List UInt256)
    (hraw :
      runInstrSeq (pairBeforeJumpTemplate j constant)
        (PairRoundState.pairHelperEntry s site.startPC p0 p1 returnPC
          r0 r1 working rest) =
      some (PairRoundState.pairAfterHelperBeforeJump s
        (pcAfter site.startPC (pairBeforeJumpTemplate j constant))
        returnPC j working p0 p1 r0 r1 constant rest))
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (PairRoundState.pairHelperEntry s site.startPC p0 p1 returnPC
        r0 r1 working rest)
      (PairRoundState.pairAfterHelperBeforeJump s site.endPC returnPC
        j working p0 p1 r0 r1 constant rest) := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_pair_of_raw j hj p0 p1 r0 r1 constant site s returnPC
      working rest hraw
  · exact hrun
  · exact hnp

/-! Compose a genuine pair-call trace, helper trace, and return trace. -/
def gasSteps_pair_of_helper {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (p0 p1 : UInt256) (r0 r1 : Nat) (constant : UInt256)
    (site : RoundSite artifact fork j p0 p1 r0 r1 constant)
    (s : State) (working : Compression.EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1012) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (ghelper : GasSteps
      (PairRoundState.pairHelperEntry s site.helper.startPC p0 p1 site.returnPC
        r0 r1 working rest)
      (PairRoundState.pairAfterHelperBeforeJump s site.helper.endPC site.returnPC
        j working p0 p1 r0 r1 constant rest)) :
    GasSteps
      (roundEntry s site.call.pushes.startPC working.a working.b working.c working.d working.e rest)
      {s with
        pc := site.returnSite.pc.succ
        stack := roundWords
          (PairRoundState.pairWorking s working j p0 p1 r0 r1 constant) ++ rest
        activeWords := s.activeWordsAfterUInt256_2 p0.toNat 32 p1.toNat 32} := by
  have helperValid : Decode.isValidJumpDest s.executionEnv.code site.helperPC.toNat = true := by
    rw [hcode]
    exact site.helper_valid
  have gc := PairCallTrace.gasSteps_call site.returnPC p0 p1 site.helperPC r0 r1
    site.call s working rest hstack hrun helperValid hcode hfork hnp
  have gc' : GasSteps
      (roundEntry s site.call.pushes.startPC working.a working.b working.c working.d working.e rest)
      (PairRoundState.pairHelperEntry s site.helper.startPC p0 p1 site.returnPC
        r0 r1 working rest) := by
    apply gc.cast rfl
    rw [site.helper_start]
  let t : State :=
    {s with activeWords := s.activeWordsAfterUInt256_2 p0.toNat 32 p1.toNat 32}
  let words : List UInt256 := roundWords
      (PairRoundState.pairWorking s working j p0 p1 r0 r1 constant) ++ rest
  have wordsBound : words.length < 1023 := by
    simp [words, roundWords]
    omega
  have returnValid : Decode.isValidJumpDest t.executionEnv.code site.returnSite.pc.toNat = true := by
    change Decode.isValidJumpDest s.executionEnv.code site.returnSite.pc.toNat = true
    rw [hcode, site.return_at]
    exact site.return_valid
  have gr := SharedCallTrace.gasSteps_return site.helperJump site.returnSite
    site.helper_jump_instr site.return_instr t words wordsBound hrun returnValid hcode hfork hnp
  have before :
      PairRoundState.pairAfterHelperBeforeJump s site.helper.endPC site.returnPC
        j working p0 p1 r0 r1 constant rest =
      {t with pc := site.helperJump.pc, stack := site.returnSite.pc :: words} := by
    rw [site.helper_end, site.return_at]
    rfl
  have after :
      {t with pc := site.returnSite.pc.succ, stack := words} =
      {s with
        pc := site.returnSite.pc.succ
        stack := roundWords
          (PairRoundState.pairWorking s working j p0 p1 r0 r1 constant) ++ rest
        activeWords := s.activeWordsAfterUInt256_2 p0.toNat 32 p1.toNat 32} := by
    rfl
  exact gc'.trans (ghelper.trans (gr.cast before.symm after))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairHelperTrace
