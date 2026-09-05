import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCallTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairMultiplyLift

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace

theorem runInstr_pc_mul {s t : State}
    (hresult : Stepper.runInstr (.op .MUL) s = some t) :
    t.pc = s.pc + UInt256.ofNat (Instr.op .MUL).size := by
  by_cases hcap : s.stack.length < 1024
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

def Advances (instruction : Instr) : Prop :=
  SharedCallTrace.Advances instruction ∨ instruction = .op .MUL

theorem runInstr_pc_of_advances {instruction : Instr} {s t : State}
    (hform : Advances instruction)
    (hresult : Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  rcases hform with hshared | hmul
  · exact SharedCallTrace.runInstr_pc_of_advances hshared hresult
  · subst instruction
    exact runInstr_pc_mul hresult

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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairMultiplyLift
