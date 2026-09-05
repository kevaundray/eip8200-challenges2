import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCallTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCallTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairMultiplyLift

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-!
# H30b four-round helper composition

The helper site is generic in the artifact and fork.  Its raw body is the
existing quad evaluator; this module lifts that result through the located
site and composes the quad call, helper, and return traces.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCallTrace

structure RoundSite (artifact : ProgramArtifact) (fork : Fork)
    (j : Nat) (p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256) where
  returnPC : UInt256
  helperPC : UInt256
  call : QuadCallTrace.CallSite artifact fork
    returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3
  helper : GenericRoundSite artifact fork
    (quadBeforeJumpTemplate j constant)
  helper_start : helper.startPC = helperPC
  helperJump : LocatedSite artifact fork
  helper_jump_instr : helperJump.located.instruction = .op .JUMP
  helper_end : helperJump.pc = helper.endPC
  returnSite : LocatedSite artifact fork
  return_instr : returnSite.located.instruction = .op .JUMPDEST
  return_at : returnSite.pc = returnPC
  helper_valid : Decode.isValidJumpDest artifact.code helperPC.toNat = true
  return_valid : Decode.isValidJumpDest artifact.code returnPC.toNat = true

set_option linter.unusedSimpArgs false in
theorem template_advances (j : Nat) (hj : j < 5) (constant : UInt256) :
    ∀ instruction ∈ quadBeforeJumpTemplate j constant,
      PairMultiplyLift.Advances instruction := by
  intro instruction hmem
  interval_cases j <;>
    simp [quadBeforeJumpTemplate, firstFTemplate, cachedTailFTemplate,
      firstBoolean, secondBoolean, d, w,
      pairFirstBooleanOps, pairSecondBooleanOps,
      pairDup7, pairDup8, pairDup9, pairDup10, pairSwap5, pairSwap7,
      cachedQrot10, cachedCfold9, cachedQrot8, cachedCfold7,
      cachedDup10, cachedDup9, cachedDup8, cachedDup7] at hmem <;>
    simp_all [PairMultiplyLift.Advances, SharedCallTrace.Advances,
      op, push1, push4, dup1, dup2, dup3, dup4, dup5, dup6,
      swap1, swap2, swap3, swap4] <;>
    aesop (add safe constructors StraightLine)

theorem runLocatedBlock_quad_of_raw {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (hj : j < 5)
    (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256)
    (site : GenericRoundSite artifact fork
      (quadBeforeJumpTemplate j constant))
    (s : State) (returnPC : UInt256)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hraw :
      runInstrSeq (quadBeforeJumpTemplate j constant)
        (QuadRoundState.quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC
          r0 r1 r2 r3 working rho) =
      some (QuadRoundState.quadAfterHelperBeforeJump s
        (pcAfter site.startPC (quadBeforeJumpTemplate j constant))
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho)) :
    Stepper.runLocatedBlock site.path
      (QuadRoundState.quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working rho) =
      some (QuadRoundState.quadAfterHelperBeforeJump s site.endPC returnPC
        j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
  have hend : site.endPC = pcAfter site.startPC
      (quadBeforeJumpTemplate j constant) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [PairMultiplyLift.runLocatedBlock_eq_raw site
    (template_advances j hj constant)
    (QuadRoundState.quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC
      r0 r1 r2 r3 working rho) rfl]
  rw [hraw, ← hend]

def gasSteps_helper_of_raw {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (hj : j < 5)
    (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256)
    (site : GenericRoundSite artifact fork
      (quadBeforeJumpTemplate j constant))
    (s : State) (returnPC : UInt256)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hraw :
      runInstrSeq (quadBeforeJumpTemplate j constant)
        (QuadRoundState.quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC
          r0 r1 r2 r3 working rho) =
      some (QuadRoundState.quadAfterHelperBeforeJump s
        (pcAfter site.startPC (quadBeforeJumpTemplate j constant))
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho))
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (QuadRoundState.quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working rho)
      (QuadRoundState.quadAfterHelperBeforeJump s site.endPC returnPC
        j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_quad_of_raw j hj p0 p1 p2 p3 r0 r1 r2 r3
      constant site s returnPC working rho hraw
  · exact hrun
  · exact hnp

/-! Compose the genuine quad call, helper, and return traces. -/
def gasSteps_quad_of_helper {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256)
    (site : RoundSite artifact fork j p0 p1 p2 p3 r0 r1 r2 r3 constant)
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (ghelper : GasSteps
      (QuadRoundState.quadHelperEntry s site.helper.startPC
        p0 p1 p2 p3 site.returnPC r0 r1 r2 r3 working rho)
      (QuadRoundState.quadAfterHelperBeforeJump s site.helper.endPC
        site.returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho)) :
    GasSteps
      (roundEntry s site.call.pushes.startPC working.a working.b working.c
        working.d working.e (QuadRoundTemplate.factor :: rho))
      {s with
        pc := site.returnSite.pc.succ
        stack := roundWords
          (QuadRoundState.quadWorking s working j p0 p1 p2 p3
            r0 r1 r2 r3 constant) ++ [QuadRoundTemplate.factor] ++ rho
        activeWords :=
          (QuadRoundState.quadActiveWordsAfterUInt256_4 s
            p0.toNat p1.toNat p2.toNat p3.toNat)} := by
  have helperValid : Decode.isValidJumpDest s.executionEnv.code
      site.helperPC.toNat = true := by
    rw [hcode]
    exact site.helper_valid
  have gc := QuadCallTrace.gasSteps_call
    site.returnPC p0 p1 p2 p3 site.helperPC r0 r1 r2 r3
    site.call s working rho hstack hrun helperValid hcode hfork hnp
  have gc' : GasSteps
      (roundEntry s site.call.pushes.startPC working.a working.b working.c
        working.d working.e (QuadRoundTemplate.factor :: rho))
      (QuadRoundState.quadHelperEntry s site.helper.startPC
        p0 p1 p2 p3 site.returnPC r0 r1 r2 r3 working rho) := by
    apply gc.cast rfl
    rw [site.helper_start]
  let t : State :=
    {s with activeWords :=
      (QuadRoundState.quadActiveWordsAfterUInt256_4 s
        p0.toNat p1.toNat p2.toNat p3.toNat)}
  let words : List UInt256 := roundWords
      (QuadRoundState.quadWorking s working j p0 p1 p2 p3
        r0 r1 r2 r3 constant) ++ [QuadRoundTemplate.factor] ++ rho
  have wordsBound : words.length < 1023 := by
    simp [words, roundWords]
    omega
  have returnValid : Decode.isValidJumpDest t.executionEnv.code
      site.returnSite.pc.toNat = true := by
    change Decode.isValidJumpDest s.executionEnv.code site.returnSite.pc.toNat = true
    rw [hcode, site.return_at]
    exact site.return_valid
  have gr := SharedCallTrace.gasSteps_return site.helperJump site.returnSite
    site.helper_jump_instr site.return_instr t words wordsBound hrun returnValid
      hcode hfork hnp
  have before :
      QuadRoundState.quadAfterHelperBeforeJump s site.helper.endPC
        site.returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho =
      {t with pc := site.helperJump.pc, stack := site.returnSite.pc :: words} := by
    rw [site.helper_end, site.return_at]
    rfl
  have after :
      {t with pc := site.returnSite.pc.succ, stack := words} =
      {s with
        pc := site.returnSite.pc.succ
        stack := roundWords
          (QuadRoundState.quadWorking s working j p0 p1 p2 p3
            r0 r1 r2 r3 constant) ++ [QuadRoundTemplate.factor] ++ rho
        activeWords := QuadRoundState.quadActiveWordsAfterUInt256_4 s
          p0.toNat p1.toNat p2.toNat p3.toNat} := by
    rfl
  exact gc'.trans (ghelper.trans (gr.cast before.symm after))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace
