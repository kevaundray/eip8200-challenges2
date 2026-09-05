import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedHelperTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 200000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundCertificates

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundData StackRoundTemplate StackRoundTrace SharedRoundTemplate

/-- Change only a site's template equality, leaving its computational fields unchanged. -/
def castTemplate {artifact : ProgramArtifact} {fork : Fork} {first second : List Instr}
    (site : GenericRoundSite artifact fork first) (h : first = second) :
    GenericRoundSite artifact fork second where
  startPC := site.startPC
  endPC := site.endPC
  sites := site.sites
  head_eq := site.head_eq
  end_eq := site.end_eq
  instruction_eq := site.instruction_eq.trans h
  contiguous := site.contiguous

theorem castTemplate_start {artifact : ProgramArtifact} {fork : Fork} {first second : List Instr}
    (site : GenericRoundSite artifact fork first) (h : first = second) :
    (castTemplate site h).startPC = site.startPC := rfl

theorem castTemplate_end {artifact : ProgramArtifact} {fork : Fork} {first second : List Instr}
    (site : GenericRoundSite artifact fork first) (h : first = second) :
    (castTemplate site h).endPC = site.endPC := rfl

def leftRoundSite (i : Fin 80) :
    SharedHelperTrace.RoundSite Artifact.submissionArtifact .Osaka
      (i.val / 16) (leftAddress i.val) (leftRotation i.val) (leftConstant i.val) where
  returnPC := leftReturnPC i.val
  helperPC := leftHelperPC i.val
  call := SharedSites.leftCallSite i
  helper := castTemplate
    (SharedSites.leftHelperSite ⟨i.val / 16, by omega⟩ (leftAddress i.val) (leftRotation i.val))
    (by rw [SharedSites.leftConstant_group i])
  helper_start := by
    rw [castTemplate_start]
    exact SharedSites.leftHelperSite_start_eq
      ⟨i.val / 16, by omega⟩ (leftAddress i.val) (leftRotation i.val)
  helperJump := SharedSites.leftHelperJump ⟨i.val / 16, by omega⟩
  helper_jump_instr := rfl
  helper_end := by
    rw [castTemplate_end]
    exact SharedSites.leftHelperSite_end_eq
      ⟨i.val / 16, by omega⟩ (leftAddress i.val) (leftRotation i.val)
  returnSite := SharedSites.leftReturnSite i
  return_instr := rfl
  return_at := SharedSites.leftReturnSite_at i
  helper_valid := SharedSites.leftHelper_valid ⟨i.val / 16, by omega⟩
  return_valid := SharedSites.leftReturn_valid i

def rightRoundSite (i : Fin 80) :
    SharedHelperTrace.RoundSite Artifact.submissionArtifact .Osaka
      (4 - i.val / 16) (rightAddress i.val) (rightRotation i.val) (rightConstant i.val) where
  returnPC := rightReturnPC i.val
  helperPC := rightHelperPC i.val
  call := SharedSites.rightCallSite i
  helper := castTemplate
    (SharedSites.rightHelperSite ⟨i.val / 16, by omega⟩ (rightAddress i.val) (rightRotation i.val))
    (by rw [SharedSites.rightConstant_group i])
  helper_start := by
    rw [castTemplate_start]
    exact SharedSites.rightHelperSite_start_eq
      ⟨i.val / 16, by omega⟩ (rightAddress i.val) (rightRotation i.val)
  helperJump := SharedSites.rightHelperJump ⟨i.val / 16, by omega⟩
  helper_jump_instr := rfl
  helper_end := by
    rw [castTemplate_end]
    exact SharedSites.rightHelperSite_end_eq
      ⟨i.val / 16, by omega⟩ (rightAddress i.val) (rightRotation i.val)
  returnSite := SharedSites.rightReturnSite i
  return_instr := rfl
  return_at := SharedSites.rightReturnSite_at i
  helper_valid := SharedSites.rightHelper_valid ⟨i.val / 16, by omega⟩
  return_valid := SharedSites.rightReturn_valid i

theorem leftRoundSite_start (i : Fin 80) :
    (leftRoundSite i).call.pushes.startPC = StackSites.leftPC i.val :=
  SharedSites.leftCallSite_start_eq i

theorem rightRoundSite_start (i : Fin 80) :
    (rightRoundSite i).call.pushes.startPC = StackSites.rightPC i.val :=
  SharedSites.rightCallSite_start_eq i

theorem leftRoundSite_end (i : Fin 80) :
    (leftRoundSite i).returnSite.pc.succ = StackSites.leftPC (i.val + 1) :=
  (SharedSites.leftReturnSite_succ_next i).trans (SharedSites.leftNextPC_eq_stackPC i)

theorem rightRoundSite_end (i : Fin 80) :
    (rightRoundSite i).returnSite.pc.succ = StackSites.rightPC (i.val + 1) :=
  (SharedSites.rightReturnSite_succ_next i).trans (SharedSites.rightNextPC_eq_stackPC i)

theorem leftRotation_le32 (i : Fin 80) : leftRotation i.val ≤ 32 := by
  fin_cases i <;> decide

theorem rightRotation_le32 (i : Fin 80) : rightRotation i.val ≤ 32 := by
  fin_cases i <;> decide

def gasSteps_leftRound (s : State) (working : Compression.EvmWorking)
    (rest : List UInt256) (i : Fin 80) (hstack : rest.length < 1013)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (roundEntry s (StackSites.leftPC i.val) working.a working.b working.c working.d working.e rest)
      (roundReturned s (StackSites.leftPC (i.val + 1)) (i.val / 16)
        working.a working.b working.c working.d working.e
        (leftAddress i.val) (leftRotation i.val) (leftConstant i.val) rest) := by
  have hz : i.val / 16 = 0 → leftConstant i.val = 0 := by
    intro h
    simp only [leftConstant, h]
    rfl
  have g := SharedHelperTrace.gasSteps_round (i.val / 16) (by omega)
    (leftAddress i.val) (leftRotation i.val) (leftConstant i.val) hz (leftRoundSite i)
    s working rest hstack hrun (leftRotation_le32 i) hcode hfork hnp
  simpa only [leftRoundSite_start, leftRoundSite_end] using g

def gasSteps_rightRound (s : State) (working : Compression.EvmWorking)
    (rest : List UInt256) (i : Fin 80) (hstack : rest.length < 1013)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (roundEntry s (StackSites.rightPC i.val) working.a working.b working.c working.d working.e rest)
      (roundReturned s (StackSites.rightPC (i.val + 1)) (4 - i.val / 16)
        working.a working.b working.c working.d working.e
        (rightAddress i.val) (rightRotation i.val) (rightConstant i.val) rest) := by
  have hz : 4 - i.val / 16 = 0 → rightConstant i.val = 0 := by
    intro h
    have hg : i.val / 16 = 4 := by omega
    simp only [rightConstant, hg]
    rfl
  have g := SharedHelperTrace.gasSteps_round (4 - i.val / 16) (by omega)
    (rightAddress i.val) (rightRotation i.val) (rightConstant i.val) hz (rightRoundSite i)
    s working rest hstack hrun (rightRotation_le32 i) hcode hfork hnp
  simpa only [rightRoundSite_start, rightRoundSite_end] using g

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundCertificates
