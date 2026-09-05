import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCallTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRawTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedHelperTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace SharedRoundTemplate

theorem template_advances (j : Nat) (hj : j < 5) (xAddress : UInt256)
    (rotation : Nat) (constant : UInt256) :
    ∀ instruction ∈ helperBeforeJumpTemplate j xAddress rotation constant,
      SharedCallTrace.Advances instruction := by
  intro instruction hmem
  interval_cases j <;>
    simp [helperBeforeJumpTemplate, booleanOps] at hmem <;>
    simp_all [SharedCallTrace.Advances, op, push1, push4, dup1,
      dup5, dup6, dup7, dup8, swap1, swap2, swap3, swap4, swap5] <;>
    aesop (add safe constructors StraightLine)

theorem runLocatedBlock_f0 {artifact : ProgramArtifact} {fork : Fork}
    (xAddress : UInt256) (rotation : Nat)
    (site : GenericRoundSite artifact fork (helperBeforeJumpTemplate 0 xAddress rotation 0))
    (s : State) (returnPC : UInt256) (working : Compression.EvmWorking)
    (rest : List UInt256) (hstack : rest.length < 1013)
    (hrun : s.halt = .Running) (hrot : rotation ≤ 32) :
    Stepper.runLocatedBlock site.path
      (SharedRoundTrace.helperEntry s site.startPC xAddress rotation returnPC working rest) =
    some (SharedRoundTrace.afterHelperBeforeJump s site.endPC returnPC 0
      working xAddress rotation 0 rest) := by
  have hend : site.endPC = pcAfter site.startPC (helperBeforeJumpTemplate 0 xAddress rotation 0) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [SharedCallTrace.runLocatedBlock_eq_raw site
    (template_advances 0 (by decide) _ _ _)
    (SharedRoundTrace.helperEntry s site.startPC xAddress rotation returnPC working rest) rfl]
  rw [SharedRoundTrace.runInstrSeq_f0 s site.startPC xAddress returnPC rotation working rest
    hstack hrun hrot, ← hend]

def gasSteps_f0 {artifact : ProgramArtifact} {fork : Fork}
    (xAddress : UInt256) (rotation : Nat)
    (site : GenericRoundSite artifact fork (helperBeforeJumpTemplate 0 xAddress rotation 0))
    (s : State) (returnPC : UInt256) (working : Compression.EvmWorking)
    (rest : List UInt256) (hstack : rest.length < 1013)
    (hrun : s.halt = .Running) (hrot : rotation ≤ 32)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (SharedRoundTrace.helperEntry s site.startPC xAddress rotation returnPC working rest)
      (SharedRoundTrace.afterHelperBeforeJump s site.endPC returnPC 0 working xAddress rotation 0 rest) := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_f0 xAddress rotation site s returnPC working rest hstack hrun hrot
  · exact hrun
  · exact hnp

structure RoundSite (artifact : ProgramArtifact) (fork : Fork)
    (j : Nat) (xAddress : UInt256) (rotation : Nat) (constant : UInt256) where
  returnPC : UInt256
  helperPC : UInt256
  call : SharedCallTrace.CallSite artifact fork returnPC xAddress helperPC rotation
  helper : GenericRoundSite artifact fork (helperBeforeJumpTemplate j xAddress rotation constant)
  helper_start : helper.startPC = helperPC
  helperJump : LocatedSite artifact fork
  helper_jump_instr : helperJump.located.instruction = .op .JUMP
  helper_end : helperJump.pc = helper.endPC
  returnSite : LocatedSite artifact fork
  return_instr : returnSite.located.instruction = .op .JUMPDEST
  return_at : returnSite.pc = returnPC
  helper_valid : Decode.isValidJumpDest artifact.code helperPC.toNat = true
  return_valid : Decode.isValidJumpDest artifact.code returnPC.toNat = true

/-- Compose three genuine traces: call, helper body, and return. -/
def gasSteps_round_of_helper {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (xAddress : UInt256) (rotation : Nat) (constant : UInt256)
    (site : RoundSite artifact fork j xAddress rotation constant)
    (s : State) (working : Compression.EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1013) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (ghelper : GasSteps
      (SharedRoundTrace.helperEntry s site.helper.startPC xAddress rotation site.returnPC working rest)
      (SharedRoundTrace.afterHelperBeforeJump s site.helper.endPC site.returnPC j
        working xAddress rotation constant rest)) :
    GasSteps (roundEntry s site.call.pushes.startPC working.a working.b working.c working.d working.e rest)
      (roundReturned s site.returnSite.pc.succ j working.a working.b working.c working.d working.e
        xAddress rotation constant rest) := by
  have helperValid : Decode.isValidJumpDest s.executionEnv.code site.helperPC.toNat = true := by
    rw [hcode]
    exact site.helper_valid
  have gc := SharedCallTrace.gasSteps_call site.returnPC xAddress site.helperPC rotation
    site.call s working.a working.b working.c working.d working.e rest (by omega) hrun
    helperValid hcode hfork hnp
  have gc' : GasSteps
      (roundEntry s site.call.pushes.startPC working.a working.b working.c working.d working.e rest)
      (SharedRoundTrace.helperEntry s site.helper.startPC xAddress rotation site.returnPC working rest) := by
    apply gc.cast rfl
    rw [site.helper_start]
    rfl
  let t : State := {s with activeWords := s.activeWordsAfterUInt256 xAddress.toNat 32}
  let words := roundWords (StackRound.stackRound working j
    (MachineState.readWord s.memory xAddress.toNat) rotation constant) ++ rest
  have wordsBound : words.length < 1023 := by
    simp [words, roundWords]
    omega
  have returnValid : Decode.isValidJumpDest t.executionEnv.code site.returnSite.pc.toNat = true := by
    change Decode.isValidJumpDest s.executionEnv.code site.returnSite.pc.toNat = true
    rw [hcode, site.return_at]
    exact site.return_valid
  have gr := SharedCallTrace.gasSteps_return site.helperJump site.returnSite
    site.helper_jump_instr site.return_instr t words wordsBound hrun returnValid hcode hfork hnp
  have before : SharedRoundTrace.afterHelperBeforeJump s site.helper.endPC site.returnPC j
      working xAddress rotation constant rest =
      {t with pc := site.helperJump.pc, stack := site.returnSite.pc :: words} := by
    rw [site.helper_end, site.return_at]
    rfl
  have after : {t with pc := site.returnSite.pc.succ, stack := words} =
      roundReturned s site.returnSite.pc.succ j working.a working.b working.c working.d working.e
        xAddress rotation constant rest := by
    rfl
  exact gc'.trans (ghelper.trans (gr.cast before.symm after))

def gasSteps_round_f0 {artifact : ProgramArtifact} {fork : Fork}
    (xAddress : UInt256) (rotation : Nat)
    (site : RoundSite artifact fork 0 xAddress rotation 0)
    (s : State) (working : Compression.EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1013) (hrun : s.halt = .Running) (hrot : rotation ≤ 32)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (roundEntry s site.call.pushes.startPC working.a working.b working.c working.d working.e rest)
      (roundReturned s site.returnSite.pc.succ 0 working.a working.b working.c working.d working.e
        xAddress rotation 0 rest) :=
  gasSteps_round_of_helper 0 xAddress rotation 0 site s working rest hstack hrun hcode hfork hnp
    (gasSteps_f0 xAddress rotation site.helper s site.returnPC working rest hstack hrun hrot hcode hfork hnp)

theorem runLocatedBlock_helper {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (hj : j < 5) (xAddress : UInt256) (rotation : Nat) (constant : UInt256)
    (hzero : j = 0 → constant = 0)
    (site : GenericRoundSite artifact fork (helperBeforeJumpTemplate j xAddress rotation constant))
    (s : State) (returnPC : UInt256) (working : Compression.EvmWorking)
    (rest : List UInt256) (hstack : rest.length < 1013)
    (hrun : s.halt = .Running) (hrot : rotation ≤ 32) :
    Stepper.runLocatedBlock site.path
      (SharedRoundTrace.helperEntry s site.startPC xAddress rotation returnPC working rest) =
    some (SharedRoundTrace.afterHelperBeforeJump s site.endPC returnPC j
      working xAddress rotation constant rest) := by
  have hend : site.endPC = pcAfter site.startPC
      (helperBeforeJumpTemplate j xAddress rotation constant) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [SharedCallTrace.runLocatedBlock_eq_raw site (template_advances j hj _ _ _)
    (SharedRoundTrace.helperEntry s site.startPC xAddress rotation returnPC working rest) rfl]
  rw [SharedRawTrace.runInstrSeq_template j hj s site.startPC xAddress returnPC rotation
    working constant rest hzero hstack hrun hrot, ← hend]

def gasSteps_helper {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (hj : j < 5) (xAddress : UInt256) (rotation : Nat) (constant : UInt256)
    (hzero : j = 0 → constant = 0)
    (site : GenericRoundSite artifact fork (helperBeforeJumpTemplate j xAddress rotation constant))
    (s : State) (returnPC : UInt256) (working : Compression.EvmWorking)
    (rest : List UInt256) (hstack : rest.length < 1013)
    (hrun : s.halt = .Running) (hrot : rotation ≤ 32)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (SharedRoundTrace.helperEntry s site.startPC xAddress rotation returnPC working rest)
      (SharedRoundTrace.afterHelperBeforeJump s site.endPC returnPC j working xAddress rotation constant rest) := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_helper j hj xAddress rotation constant hzero site s returnPC working rest hstack hrun hrot
  · exact hrun
  · exact hnp

def gasSteps_round {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (hj : j < 5) (xAddress : UInt256) (rotation : Nat) (constant : UInt256)
    (hzero : j = 0 → constant = 0)
    (site : RoundSite artifact fork j xAddress rotation constant)
    (s : State) (working : Compression.EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1013) (hrun : s.halt = .Running) (hrot : rotation ≤ 32)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (roundEntry s site.call.pushes.startPC working.a working.b working.c working.d working.e rest)
      (roundReturned s site.returnSite.pc.succ j working.a working.b working.c working.d working.e
        xAddress rotation constant rest) :=
  gasSteps_round_of_helper j xAddress rotation constant site s working rest hstack hrun hcode hfork hnp
    (gasSteps_helper j hj xAddress rotation constant hzero site.helper s site.returnPC working rest
      hstack hrun hrot hcode hfork hnp)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedHelperTrace
