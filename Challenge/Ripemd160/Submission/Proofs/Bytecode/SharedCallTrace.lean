import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCallTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace

/-- The two additional straight-line operations used by H12 helpers. -/
theorem runInstr_pc_extra {instruction : Instr} {s t : State}
    (hform : instruction = .op .SUB ∨ instruction = .op .JUMPDEST)
    (hresult : Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  rcases hform with rfl | rfl
  · by_cases hcap : s.stack.length < 1024
    · rw [Stepper.runInstr, if_pos hcap] at hresult
      cases hs : s.stack with
      | nil => simp [hs] at hresult
      | cons a tail =>
          cases ht : tail with
          | nil => simp [hs, ht] at hresult
          | cons b rest =>
              simp [hs, ht] at hresult
              subst t
              rfl
    · simp [Stepper.runInstr, hcap] at hresult
  · by_cases hcap : s.stack.length < 1024
    · simp [Stepper.runInstr, hcap] at hresult
      subst t
      rfl
    · simp [Stepper.runInstr, hcap] at hresult

def Advances (instruction : Instr) : Prop :=
  StraightLine instruction ∨ instruction = .op .SUB ∨ instruction = .op .JUMPDEST

theorem runInstr_pc_of_advances {instruction : Instr} {s t : State}
    (hform : Advances instruction)
    (hresult : Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  rcases hform with hstraight | hextra
  · exact runInstr_pc_of_straight hstraight hresult
  · exact runInstr_pc_extra hextra hresult

theorem runLocatedBlock_eq_raw {artifact : ProgramArtifact} {fork : Fork}
    {template : List Instr} (site : GenericRoundSite artifact fork template)
    (hform : ∀ instruction ∈ template, Advances instruction)
    (s : State) (hpc : s.pc = site.startPC) :
    Stepper.runLocatedBlock site.path s = runInstrSeq template s := by
  apply runLocatedBlock_eq_runInstrSeq_site site s hpc
  intro located hmem u v hresult
  apply runInstr_pc_of_advances _ hresult
  apply hform
  rw [← site.instruction_eq]
  exact List.mem_map_of_mem hmem

def callPushes (returnPC xAddress helperPC : UInt256) (rotation : Nat) : List Instr :=
  [push1 (UInt256.ofNat (32 - rotation)), push2 returnPC, push2 xAddress, push2 helperPC]

def callPushed (s : State) (pc returnPC xAddress helperPC : UInt256)
    (rotation : Nat) (a b c d e : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := pc
    stack := [helperPC, xAddress, returnPC, UInt256.ofNat (32 - rotation), a, b, c, d, e] ++ rest }

def helperEntry (s : State) (helperPC returnPC xAddress : UInt256)
    (rotation : Nat) (a b c d e : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := helperPC
    stack := [xAddress, returnPC, UInt256.ofNat (32 - rotation), a, b, c, d, e] ++ rest }

theorem callPushes_advances (returnPC xAddress helperPC : UInt256) (rotation : Nat) :
    ∀ instruction ∈ callPushes returnPC xAddress helperPC rotation, Advances instruction := by
  intro instruction hmem
  simp only [callPushes, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  all_goals exact Or.inl (StraightLine.push _ _)

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_callPushes (s : State) (pc returnPC xAddress helperPC : UInt256)
    (rotation : Nat) (a b c d e : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1015) (hrun : s.halt = .Running) :
    runInstrSeq (callPushes returnPC xAddress helperPC rotation)
      (roundEntry s pc a b c d e rest) =
    some (callPushed s (pcAfter pc (callPushes returnPC xAddress helperPC rotation))
      returnPC xAddress helperPC rotation a b c d e rest) := by
  have hcap (n : Nat) (hn : n ≤ 9) : rest.length + n < 1024 := by omega
  simp (discharger := omega) [callPushes, callPushed, roundEntry, runInstrSeq,
    Stepper.runInstr, pcAfter, push1, push2, hrun, hcap, Nat.add_assoc,
    Instr.size_push]

theorem runLocatedBlock_callPushes {artifact : ProgramArtifact} {fork : Fork}
    (returnPC xAddress helperPC : UInt256) (rotation : Nat)
    (site : GenericRoundSite artifact fork (callPushes returnPC xAddress helperPC rotation))
    (s : State) (a b c d e : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1015) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock site.path (roundEntry s site.startPC a b c d e rest) =
      some (callPushed s site.endPC returnPC xAddress helperPC rotation a b c d e rest) := by
  have hend : site.endPC = pcAfter site.startPC
      (callPushes returnPC xAddress helperPC rotation) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [runLocatedBlock_eq_raw site (callPushes_advances _ _ _ _)
    (roundEntry s site.startPC a b c d e rest) rfl]
  rw [runInstrSeq_callPushes s site.startPC returnPC xAddress helperPC rotation
    a b c d e rest hstack hrun, ← hend]

theorem runLocated_jump {artifact : ProgramArtifact} {fork : Fork}
    (site : LocatedSite artifact fork) (hinstr : site.located.instruction = .op .JUMP)
    (s : State) (dest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1023)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true) :
    Stepper.runLocated site.located {s with pc := site.pc, stack := dest :: rest} =
      some {s with pc := dest, stack := rest} := by
  simp [Stepper.runLocated, site.pc_eq, hinstr, Stepper.runInstr, hstack, hvalid]

theorem runLocated_jumpdest {artifact : ProgramArtifact} {fork : Fork}
    (site : LocatedSite artifact fork) (hinstr : site.located.instruction = .op .JUMPDEST)
    (s : State) (hstack : s.stack.length < 1024) :
    Stepper.runLocated site.located {s with pc := site.pc} =
      some {s with pc := site.pc.succ} := by
  simp [Stepper.runLocated, site.pc_eq, hinstr, Stepper.runInstr, hstack]

structure CallSite (artifact : ProgramArtifact) (fork : Fork)
    (returnPC xAddress helperPC : UInt256) (rotation : Nat) where
  pushes : GenericRoundSite artifact fork (callPushes returnPC xAddress helperPC rotation)
  jump : LocatedSite artifact fork
  jump_instr : jump.located.instruction = .op .JUMP
  jump_pc : jump.pc = pushes.endPC

def CallSite.path {artifact : ProgramArtifact} {fork : Fork}
    {returnPC xAddress helperPC : UInt256} {rotation : Nat}
    (site : CallSite artifact fork returnPC xAddress helperPC rotation) :
    List (Stepper.Located artifact fork) :=
  site.pushes.path ++ [site.jump.located]

theorem runLocatedBlock_call {artifact : ProgramArtifact} {fork : Fork}
    (returnPC xAddress helperPC : UInt256) (rotation : Nat)
    (site : CallSite artifact fork returnPC xAddress helperPC rotation)
    (s : State) (a b c d e : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1015) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code helperPC.toNat = true) :
    Stepper.runLocatedBlock site.path
      (roundEntry s site.pushes.startPC a b c d e rest) =
      some (helperEntry s helperPC returnPC xAddress rotation a b c d e rest) := by
  apply Stepper.runLocatedBlock_append site.pushes.path [site.jump.located]
    _ (callPushed s site.pushes.endPC returnPC xAddress helperPC rotation a b c d e rest)
  · exact runLocatedBlock_callPushes _ _ _ _ _ _ _ _ _ _ _ _ hstack hrun
  · exact hrun
  · have hcap : ([xAddress, returnPC, UInt256.ofNat (32 - rotation), a, b, c, d, e] ++ rest).length < 1023 := by
      simp; omega
    have h := runLocated_jump site.jump site.jump_instr s helperPC
      ([xAddress, returnPC, UInt256.ofNat (32 - rotation), a, b, c, d, e] ++ rest) hcap hvalid
    have hlocated : Stepper.runLocated site.jump.located
        (callPushed s site.pushes.endPC returnPC xAddress helperPC rotation a b c d e rest) =
        some (helperEntry s helperPC returnPC xAddress rotation a b c d e rest) := by
      simpa [callPushed, helperEntry, site.jump_pc] using h
    simp only [Stepper.runLocatedBlock, hlocated]

def gasSteps_call {artifact : ProgramArtifact} {fork : Fork}
    (returnPC xAddress helperPC : UInt256) (rotation : Nat)
    (site : CallSite artifact fork returnPC xAddress helperPC rotation)
    (s : State) (a b c d e : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1015) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code helperPC.toNat = true)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (roundEntry s site.pushes.startPC a b c d e rest)
      (helperEntry s helperPC returnPC xAddress rotation a b c d e rest) := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_call _ _ _ _ _ _ _ _ _ _ _ _ hstack hrun hvalid
  · exact hrun
  · exact hnp

def returnPath {artifact : ProgramArtifact} {fork : Fork}
    (jump target : LocatedSite artifact fork) : List (Stepper.Located artifact fork) :=
  [jump.located, target.located]

theorem runLocatedBlock_return {artifact : ProgramArtifact} {fork : Fork}
    (jump target : LocatedSite artifact fork)
    (hjump : jump.located.instruction = .op .JUMP)
    (htarget : target.located.instruction = .op .JUMPDEST)
    (s : State) (rest : List UInt256) (hstack : rest.length < 1023)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code target.pc.toNat = true) :
    Stepper.runLocatedBlock (returnPath jump target)
      {s with pc := jump.pc, stack := target.pc :: rest} =
      some {s with pc := target.pc.succ, stack := rest} := by
  have hj := runLocated_jump jump hjump s target.pc rest hstack hvalid
  have hd := runLocated_jumpdest target htarget {s with stack := rest} (by simpa using (show rest.length < 1024 by omega))
  apply Stepper.runLocatedBlock_append [jump.located] [target.located]
    _ {s with pc := target.pc, stack := rest}
  · simp only [Stepper.runLocatedBlock]
    rw [hj]
  · exact hrun
  · simp only [Stepper.runLocatedBlock]
    rw [show Stepper.runLocated target.located {s with pc := target.pc, stack := rest} =
      some {s with pc := target.pc.succ, stack := rest} from hd]

def gasSteps_return {artifact : ProgramArtifact} {fork : Fork}
    (jump target : LocatedSite artifact fork)
    (hjump : jump.located.instruction = .op .JUMP)
    (htarget : target.located.instruction = .op .JUMPDEST)
    (s : State) (rest : List UInt256) (hstack : rest.length < 1023)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code target.pc.toNat = true)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := jump.pc, stack := target.pc :: rest}
      {s with pc := target.pc.succ, stack := rest} := by
  apply Stepper.runLocatedBlock_sound artifact fork (returnPath jump target)
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_return jump target hjump htarget s rest hstack hrun hvalid
  · exact hrun
  · exact hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCallTrace
