import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleActiveWords

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLoadTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace

def loadTemplate : List Instr :=
  [push1 (UInt256.ofNat 160), op .MLOAD,
   push1 (UInt256.ofNat 128), op .MLOAD,
   push1 (UInt256.ofNat 96), op .MLOAD,
   push1 (UInt256.ofNat 64), op .MLOAD,
   push1 (UInt256.ofNat 32), op .MLOAD]

def hashWords (s : State) : List UInt256 :=
  let h := StackMemory.hashAt s.memory
  [h.h0, h.h1, h.h2, h.h3, h.h4]

def loadEntry (s : State) (pc : UInt256) (rest : List UInt256) : State :=
  {s with pc := pc, stack := rest}

def loadReturned (s : State) (pc : UInt256) (rest : List UInt256) : State :=
  {s with pc := pc, stack := hashWords s ++ rest}

theorem loadTemplate_straight : ∀ instruction ∈ loadTemplate, StraightLine instruction := by
  intro instruction hmem
  simp only [loadTemplate, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_load (s : State) (pc : UInt256) (rest : List UInt256)
    (hactive : 66 ≤ s.activeWords.toNat) (hstack : rest.length < 1019)
    (hrun : s.halt = .Running) :
    runInstrSeq loadTemplate (loadEntry s pc rest) =
      some (loadReturned s (pcAfter pc loadTemplate) rest) := by
  have hcap (n : Nat) (hn : n ≤ 5) : rest.length + n < 1024 := by omega
  have hc0 : rest.length < 1024 := by omega
  have h32 : s.activeWordsAfterUInt256 32 32 = s.activeWords := by
    apply ScheduleActiveWords.activeWordsAfterUInt256_eq
    omega
  have h64 : s.activeWordsAfterUInt256 64 32 = s.activeWords := by
    apply ScheduleActiveWords.activeWordsAfterUInt256_eq
    omega
  have h96 : s.activeWordsAfterUInt256 96 32 = s.activeWords := by
    apply ScheduleActiveWords.activeWordsAfterUInt256_eq
    omega
  have h128 : s.activeWordsAfterUInt256 128 32 = s.activeWords := by
    apply ScheduleActiveWords.activeWordsAfterUInt256_eq
    omega
  have h160 : s.activeWordsAfterUInt256 160 32 = s.activeWords := by
    apply ScheduleActiveWords.activeWordsAfterUInt256_eq
    omega
  simp only [State.activeWordsAfterUInt256] at h32 h64 h96 h128 h160
  simp (discharger := omega) [loadTemplate, loadEntry, loadReturned, hashWords, StackMemory.hashAt,
    runInstrSeq, Stepper.runInstr, pcAfter, push1, op, hcap, hrun,
    hc0, h32, h64, h96, h128, h160, UInt256.succ, Instr.size_push, Instr.size_op,
    State.activeWordsAfterUInt256, Nat.add_assoc]
  rfl

theorem runLocatedBlock_load {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork loadTemplate)
    (s : State) (rest : List UInt256)
    (hactive : 66 ≤ s.activeWords.toNat) (hstack : rest.length < 1019)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock site.path (loadEntry s site.startPC rest) =
      some (loadReturned s site.endPC rest) := by
  have hend : site.endPC = pcAfter site.startPC loadTemplate := by
    calc
      site.endPC = pcAfter site.startPC
          (site.sites.map (fun q => q.located.instruction)) :=
        endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
          site.head_eq site.end_eq site.contiguous
      _ = pcAfter site.startPC loadTemplate := by rw [site.instruction_eq]
  have hadvance : ∀ located, located ∈ site.sites → ∀ {u v : State},
      Stepper.runInstr located.located.instruction u = some v →
        v.pc = u.pc + UInt256.ofNat located.located.instruction.size := by
    intro located hmem u v hresult
    have hstraight : StraightLine located.located.instruction := by
      apply loadTemplate_straight
      rw [← site.instruction_eq]
      exact List.mem_map_of_mem hmem
    exact runInstr_pc_of_straight hstraight hresult
  rw [runLocatedBlock_eq_runInstrSeq_site site
    (loadEntry s site.startPC rest) rfl hadvance]
  rw [runInstrSeq_load s site.startPC rest hactive hstack hrun, ← hend]

def gasSteps_load {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork loadTemplate)
    (s : State) (rest : List UInt256)
    (hactive : 66 ≤ s.activeWords.toNat) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loadEntry s site.startPC rest) (loadReturned s site.endPC rest) := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_load site s rest hactive hstack hrun
  · exact hrun
  · exact hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLoadTrace
