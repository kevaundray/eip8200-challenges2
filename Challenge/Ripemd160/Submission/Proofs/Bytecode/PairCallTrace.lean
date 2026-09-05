import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCallTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

/-!
# H24 paired-round call trace

This file proves the six-push call prefix and its helper jump.  The pair
helper body is supplied separately as a genuine `GasSteps` trace.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairCallTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState

abbrev pairCallPushes (returnPC p0 p1 helperPC : UInt256) (r0 r1 : Nat) : List Instr :=
  PairRoundState.pairCallPushes returnPC p0 p1 helperPC r0 r1

theorem pairCallPushes_advances (returnPC p0 p1 helperPC : UInt256)
    (r0 r1 : Nat) :
    ∀ instruction ∈ pairCallPushes returnPC p0 p1 helperPC r0 r1,
      SharedCallTrace.Advances instruction := by
  intro instruction hmem
  simp only [pairCallPushes, PairRoundState.pairCallPushes, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact Or.inl (StraightLine.push _ _)

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_pairCallPushes (s : State)
    (pc returnPC p0 p1 helperPC : UInt256) (r0 r1 : Nat)
    (working : Compression.EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1012) (hrun : s.halt = .Running) :
    runInstrSeq (pairCallPushes returnPC p0 p1 helperPC r0 r1)
      (roundEntry s pc working.a working.b working.c working.d working.e rest) =
    some (PairRoundState.pairCallPushed s
      (pcAfter pc (pairCallPushes returnPC p0 p1 helperPC r0 r1))
      returnPC p0 p1 helperPC r0 r1 working rest) := by
  have hcap (n : Nat) (hn : n ≤ 11) : rest.length + n < 1024 := by
    omega
  simp (discharger := omega)
    [pairCallPushes, PairRoundState.pairCallPushes,
      PairRoundState.pairCallPushed, roundEntry, runInstrSeq,
      Stepper.runInstr, pcAfter, push1, push2, hrun, hcap,
      Nat.add_assoc, Instr.size_push, roundWords]

theorem runLocatedBlock_pairCallPushes {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 helperPC : UInt256) (r0 r1 : Nat)
    (site : GenericRoundSite artifact fork
      (pairCallPushes returnPC p0 p1 helperPC r0 r1))
    (s : State) (working : Compression.EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1012) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock site.path
      (roundEntry s site.startPC working.a working.b working.c working.d working.e rest) =
      some (PairRoundState.pairCallPushed s site.endPC
        returnPC p0 p1 helperPC r0 r1 working rest) := by
  have hend : site.endPC = pcAfter site.startPC
      (pairCallPushes returnPC p0 p1 helperPC r0 r1) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [SharedCallTrace.runLocatedBlock_eq_raw site
    (pairCallPushes_advances _ _ _ _ _ _)
    (roundEntry s site.startPC working.a working.b working.c working.d working.e rest) rfl]
  rw [runInstrSeq_pairCallPushes s site.startPC returnPC p0 p1 helperPC r0 r1
    working rest hstack hrun, ← hend]

structure CallSite (artifact : ProgramArtifact) (fork : Fork)
    (returnPC p0 p1 helperPC : UInt256) (r0 r1 : Nat) where
  pushes : GenericRoundSite artifact fork
    (pairCallPushes returnPC p0 p1 helperPC r0 r1)
  jump : LocatedSite artifact fork
  jump_instr : jump.located.instruction = .op .JUMP
  jump_pc : jump.pc = pushes.endPC

def CallSite.path {artifact : ProgramArtifact} {fork : Fork}
    {returnPC p0 p1 helperPC : UInt256} {r0 r1 : Nat}
    (site : CallSite artifact fork returnPC p0 p1 helperPC r0 r1) :
    List (Stepper.Located artifact fork) :=
  site.pushes.path ++ [site.jump.located]

theorem runLocatedBlock_call {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 helperPC : UInt256) (r0 r1 : Nat)
    (site : CallSite artifact fork returnPC p0 p1 helperPC r0 r1)
    (s : State) (working : Compression.EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1012) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code helperPC.toNat = true) :
    Stepper.runLocatedBlock site.path
      (roundEntry s site.pushes.startPC working.a working.b working.c working.d working.e rest) =
      some (PairRoundState.pairHelperEntry s helperPC p0 p1 returnPC
        r0 r1 working rest) := by
  apply Stepper.runLocatedBlock_append site.pushes.path [site.jump.located] _
    (PairRoundState.pairCallPushed s site.pushes.endPC returnPC p0 p1 helperPC
      r0 r1 working rest)
  · exact runLocatedBlock_pairCallPushes returnPC p0 p1 helperPC r0 r1 site.pushes
      s working rest hstack hrun
  · exact hrun
  · have hcap :
        ([p0, returnPC, UInt256.ofNat (32 - r0), p1,
          UInt256.ofNat (32 - r1)] ++ roundWords working ++ rest).length < 1023 := by
      simp [roundWords]
      omega
    have h := SharedCallTrace.runLocated_jump site.jump site.jump_instr s helperPC
      ([p0, returnPC, UInt256.ofNat (32 - r0), p1,
        UInt256.ofNat (32 - r1)] ++ roundWords working ++ rest) hcap hvalid
    have hlocated : Stepper.runLocated site.jump.located
        (PairRoundState.pairCallPushed s site.pushes.endPC returnPC p0 p1 helperPC
          r0 r1 working rest) =
        some (PairRoundState.pairHelperEntry s helperPC p0 p1 returnPC
          r0 r1 working rest) := by
      simpa [PairRoundState.pairCallPushed, PairRoundState.pairHelperEntry,
        roundWords, site.jump_pc] using h
    simp only [Stepper.runLocatedBlock, hlocated]

def gasSteps_call {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 helperPC : UInt256) (r0 r1 : Nat)
    (site : CallSite artifact fork returnPC p0 p1 helperPC r0 r1)
    (s : State) (working : Compression.EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1012) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code helperPC.toNat = true)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (roundEntry s site.pushes.startPC working.a working.b working.c working.d working.e rest)
      (PairRoundState.pairHelperEntry s helperPC p0 p1 returnPC
        r0 r1 working rest) := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_call returnPC p0 p1 helperPC r0 r1 site s working rest
      hstack hrun hvalid
  · exact hrun
  · exact hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairCallTrace
