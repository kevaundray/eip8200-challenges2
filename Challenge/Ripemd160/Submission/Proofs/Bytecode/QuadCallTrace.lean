import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCallTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

/-!
# H30b four-round call trace

This module proves the ten-push quad wrapper and its helper jump.  The fixed
factor remains below the wrapper arguments and is exposed only through the
quad helper-entry state.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCallTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate

/-- Instructions push `s3, p3, s2, p2, s1, p1, s0, return-PC, p0,
helper-PC`.  The resulting top-first stack has the quad helper-entry shape. -/
def quadCallPushes (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat) : List Instr :=
  [push1 (UInt256.ofNat (32 - r3)), push2 p3,
    push1 (UInt256.ofNat (32 - r2)), push2 p2,
    push1 (UInt256.ofNat (32 - r1)), push2 p1,
    push1 (UInt256.ofNat (32 - r0)), push2 returnPC,
    push2 p0, push2 helperPC]

/-- State after the quad wrapper has pushed its ten values. -/
def quadCallPushed (s : State) (pc returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (rho : List UInt256) : State :=
  { s with
    pc := pc
    stack := [helperPC, p0, returnPC, UInt256.ofNat (32 - r0), p1,
      UInt256.ofNat (32 - r1), p2, UInt256.ofNat (32 - r2), p3,
      UInt256.ofNat (32 - r3)] ++ roundWords working ++
      [QuadRoundTemplate.factor] ++ rho }

theorem quadCallPushes_advances (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat) :
    ∀ instruction ∈ quadCallPushes returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3,
      SharedCallTrace.Advances instruction := by
  intro instruction hmem
  simp only [quadCallPushes, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact Or.inl (StraightLine.push _ _)

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_quadCallPushes (s : State)
    (pc returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (rho : List UInt256) (hstack : rho.length < 1007)
    (hrun : s.halt = .Running) :
    runInstrSeq (quadCallPushes returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3)
      (roundEntry s pc working.a working.b working.c working.d working.e
        (QuadRoundTemplate.factor :: rho)) =
    some (quadCallPushed s
      (pcAfter pc (quadCallPushes returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3))
      returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3 working rho) := by
  have hcap (n : Nat) (hn : n ≤ 16) : rho.length + n < 1024 := by
    omega
  simp (discharger := omega)
    [quadCallPushes, quadCallPushed, roundEntry, runInstrSeq,
      Stepper.runInstr, pcAfter, push1, push2, hrun, hcap,
      Nat.add_assoc, Instr.size_push, roundWords,
      QuadRoundTemplate.factor]

theorem runLocatedBlock_quadCallPushes {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat)
    (site : GenericRoundSite artifact fork
      (quadCallPushes returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3))
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock site.path
      (roundEntry s site.startPC working.a working.b working.c working.d
        working.e (QuadRoundTemplate.factor :: rho)) =
      some (quadCallPushed s site.endPC returnPC p0 p1 p2 p3 helperPC
        r0 r1 r2 r3 working rho) := by
  have hend : site.endPC = pcAfter site.startPC
      (quadCallPushes returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [SharedCallTrace.runLocatedBlock_eq_raw site
    (quadCallPushes_advances _ _ _ _ _ _ _ _ _ _)
    (roundEntry s site.startPC working.a working.b working.c working.d
      working.e (QuadRoundTemplate.factor :: rho)) rfl]
  rw [runInstrSeq_quadCallPushes s site.startPC returnPC p0 p1 p2 p3 helperPC
    r0 r1 r2 r3 working rho hstack hrun, ← hend]

structure CallSite (artifact : ProgramArtifact) (fork : Fork)
    (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat) where
  pushes : GenericRoundSite artifact fork
    (quadCallPushes returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3)
  jump : LocatedSite artifact fork
  jump_instr : jump.located.instruction = .op .JUMP
  jump_pc : jump.pc = pushes.endPC

def CallSite.path {artifact : ProgramArtifact} {fork : Fork}
    {returnPC p0 p1 p2 p3 helperPC : UInt256}
    {r0 r1 r2 r3 : Nat}
    (site : CallSite artifact fork returnPC p0 p1 p2 p3 helperPC
      r0 r1 r2 r3) : List (Stepper.Located artifact fork) :=
  site.pushes.path ++ [site.jump.located]

theorem runLocatedBlock_call {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat)
    (site : CallSite artifact fork returnPC p0 p1 p2 p3 helperPC
      r0 r1 r2 r3)
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code helperPC.toNat = true) :
    Stepper.runLocatedBlock site.path
      (roundEntry s site.pushes.startPC working.a working.b working.c
        working.d working.e (QuadRoundTemplate.factor :: rho)) =
      some (QuadRoundState.quadHelperEntry s helperPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working rho) := by
  apply Stepper.runLocatedBlock_append site.pushes.path [site.jump.located] _
    (quadCallPushed s site.pushes.endPC returnPC p0 p1 p2 p3 helperPC
      r0 r1 r2 r3 working rho)
  · exact runLocatedBlock_quadCallPushes returnPC p0 p1 p2 p3 helperPC
      r0 r1 r2 r3 site.pushes s working rho hstack hrun
  · exact hrun
  · have hcap :
        ([p0, returnPC, UInt256.ofNat (32 - r0), p1,
          UInt256.ofNat (32 - r1), p2, UInt256.ofNat (32 - r2), p3,
          UInt256.ofNat (32 - r3)] ++ roundWords working ++
          [QuadRoundTemplate.factor] ++ rho).length < 1023 := by
      simp [roundWords]
      omega
    have h := SharedCallTrace.runLocated_jump site.jump site.jump_instr s
      helperPC
      ([p0, returnPC, UInt256.ofNat (32 - r0), p1,
        UInt256.ofNat (32 - r1), p2, UInt256.ofNat (32 - r2), p3,
        UInt256.ofNat (32 - r3)] ++ roundWords working ++
        [QuadRoundTemplate.factor] ++ rho) hcap hvalid
    have hlocated : Stepper.runLocated site.jump.located
        (quadCallPushed s site.pushes.endPC returnPC p0 p1 p2 p3 helperPC
          r0 r1 r2 r3 working rho) =
        some (QuadRoundState.quadHelperEntry s helperPC p0 p1 p2 p3 returnPC
          r0 r1 r2 r3 working rho) := by
      simpa [quadCallPushed, QuadRoundState.quadHelperEntry, roundWords,
        site.jump_pc, QuadRoundTemplate.factor] using h
    simp only [Stepper.runLocatedBlock, hlocated]

def gasSteps_call {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat)
    (site : CallSite artifact fork returnPC p0 p1 p2 p3 helperPC
      r0 r1 r2 r3)
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code helperPC.toNat = true)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (roundEntry s site.pushes.startPC working.a working.b working.c
        working.d working.e (QuadRoundTemplate.factor :: rho))
      (QuadRoundState.quadHelperEntry s helperPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working rho) := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_call returnPC p0 p1 p2 p3 helperPC
      r0 r1 r2 r3 site s working rho hstack hrun hvalid
  · exact hrun
  · exact hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCallTrace
