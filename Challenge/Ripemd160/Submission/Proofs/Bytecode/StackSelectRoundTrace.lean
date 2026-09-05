import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# H10 direct traces for the selecting round forms

This file owns only the `f1` and `f3` templates.  It uses the generic
`GenericRoundSite` bridge from `StackRoundTrace`; no concrete artifact lookup
is reduced here.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSelectRoundTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

private theorem maskedRotateAdd (q e r r' : UInt256) :
    UInt256.land mask
        (UInt256.add
          (((mask.land q).shiftLeft r).lor
            ((mask.land q).shiftRight r')) e) =
      UInt256.land
        (UInt256.add
          (((q.land mask).shiftLeft r).lor
            ((q.land mask).shiftRight r')) e) mask := by
  rw [Word.land_comm mask q]
  exact Word.land_comm _ _

/-! ## Direct f1 evaluator trace -/

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_f1 (s : State) (startPC : UInt256)
    (a b c d e xAddress : UInt256) (rotation : Nat) (constant : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015)
    (hrun : s.halt = .Running) :
    runInstrSeq (f1Template xAddress rotation constant)
        (roundEntry s startPC a b c d e rest) =
      some (roundReturned s
        (pcAfter startPC (f1Template xAddress rotation constant))
        1 a b c d e xAddress rotation constant rest) := by
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by
    omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  have hswap2 (u v w : UInt256) (rho : List UInt256) :
      (u :: v :: w :: rho).exchange 0 2 = some (w :: v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u w [v] rho
  have hswap3 (u v w z : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: rho).exchange 0 3 =
        some (z :: v :: w :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u z [v, w] rho
  have hswap4 (u v w z q : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: rho).exchange 0 4 =
        some (q :: v :: w :: z :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u q [v, w, z] rho
  have hadd (u v : UInt256) : u + v = u.add v := by
    rfl
  have hzero (u : UInt256) : u.add (0 : UInt256) = u := by
    apply Word.word_ext
    change (u.val + (0 : UInt256).val).val = u.val.val
    rw [Fin.val_add]
    change (u.val.val + 0) % UInt256.size = u.val.val
    rw [Nat.add_zero, Nat.mod_eq_of_lt u.val.isLt]
  have hcomm (u v : UInt256) : u.add v = v.add u := by
    exact Word.word_add_comm u v
  have hxorcomm (u v : UInt256) : u.xor v = v.xor u := by
    exact BooleanSelect.xor_comm u v
  have hbase : constant.add
      ((MachineState.readWord s.memory xAddress.toNat).add
        ((d.xor (b.land (c.xor d))).add a)) =
      (((d.xor ((c.xor d).land b)).add a).add
        (MachineState.readWord s.memory xAddress.toNat)).add constant := by
    rw [hcomm constant, hcomm (MachineState.readWord s.memory xAddress.toNat)]
    rw [Word.land_comm b (c.xor d)]
  simp (config := { maxSteps := 2000000 })
    [f1Template, op, push1, push2, push4, dup1, dup2, dup3, dup4, dup5,
      dup6, swap1, swap2, swap3, swap4, mask, c10, c22,
      runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      roundEntry, roundReturned, roundWords, roundResult, roundWorking,
      roundWord, pcAfter, StackRound.stackRound, StackRound.stackF,
      StackRound.stackSum, StackRound.stackRawRot, StackRound.stackC10,
      Word.mask32, List.exchange, hrun, hcap, hswap1, hswap2, hswap3,
      hswap4, UInt256.succ, Instr.size, Instr.size_push, Instr.size_op,
      Nat.add_assoc, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, Word.land_comm, Word.lor_comm,
      BooleanSelect.xor_comm, State.activeWordsAfterUInt256, hadd, hzero,
      hxorcomm]
  constructor
  · rw [hbase, hcomm e]
    exact maskedRotateAdd _ _ _ _
  · exact Word.land_comm _ _

theorem runLocatedBlock_f1
    {artifact : ProgramArtifact} {fork : Fork}
    (xAddress : UInt256) (rotation : Nat) (constant : UInt256)
    (site : GenericRoundSite artifact fork
      (f1Template xAddress rotation constant))
    (s : State) (a b c d e : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock site.path
        (roundEntry s site.startPC a b c d e rest) =
      some (roundReturned s site.endPC
        1 a b c d e xAddress rotation constant rest) := by
  have hpc : site.endPC =
      pcAfter site.startPC (f1Template xAddress rotation constant) := by
    calc
      site.endPC = pcAfter site.startPC
          (site.sites.map (fun q => q.located.instruction)) :=
        endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
          site.head_eq site.end_eq site.contiguous
      _ = pcAfter site.startPC
          (f1Template xAddress rotation constant) := by
        rw [site.instruction_eq]
  have hadvance : ∀ located, located ∈ site.sites →
      ∀ {u v : State},
        Challenge.EvmProof.Stepper.runInstr located.located.instruction u = some v →
          v.pc = u.pc + UInt256.ofNat located.located.instruction.size := by
    intro located hmem u v hresult
    have hstraight : StraightLine located.located.instruction := by
      apply f1Template_straight
      rw [← site.instruction_eq]
      exact List.mem_map_of_mem hmem
    exact runInstr_pc_of_straight hstraight hresult
  calc
    Challenge.EvmProof.Stepper.runLocatedBlock site.path
        (roundEntry s site.startPC a b c d e rest) =
        runInstrSeq (f1Template xAddress rotation constant)
          (roundEntry s site.startPC a b c d e rest) :=
      runLocatedBlock_eq_runInstrSeq_site site
        (roundEntry s site.startPC a b c d e rest) rfl hadvance
    _ = some (roundReturned s
        (pcAfter site.startPC (f1Template xAddress rotation constant))
        1 a b c d e xAddress rotation constant rest) :=
      runInstrSeq_f1 s site.startPC a b c d e xAddress rotation constant rest
        hstack hrun
    _ = some (roundReturned s site.endPC
        1 a b c d e xAddress rotation constant rest) := by
      rw [hpc]

def gasSteps_f1
    {artifact : ProgramArtifact} {fork : Fork}
    (xAddress : UInt256) (rotation : Nat) (constant : UInt256)
    (site : GenericRoundSite artifact fork
      (f1Template xAddress rotation constant))
    (s : State) (a b c d e : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015)
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (roundEntry s site.startPC a b c d e rest)
      (roundReturned s site.endPC
        1 a b c d e xAddress rotation constant rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound artifact fork site.path
  · simpa [roundEntry] using hcode
  · simpa [roundEntry] using hfork
  · exact runLocatedBlock_f1 xAddress rotation constant site s a b c d e rest
      hstack hrun
  · simpa [roundEntry] using hrun
  · simpa [roundEntry] using hnp

/-! ## Direct f3 evaluator trace -/

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_f3 (s : State) (startPC : UInt256)
    (a b c d e xAddress : UInt256) (rotation : Nat) (constant : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015)
    (hrun : s.halt = .Running) :
    runInstrSeq (f3Template xAddress rotation constant)
        (roundEntry s startPC a b c d e rest) =
      some (roundReturned s
        (pcAfter startPC (f3Template xAddress rotation constant))
        3 a b c d e xAddress rotation constant rest) := by
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by
    omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  have hswap2 (u v w : UInt256) (rho : List UInt256) :
      (u :: v :: w :: rho).exchange 0 2 = some (w :: v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u w [v] rho
  have hswap3 (u v w z : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: rho).exchange 0 3 =
        some (z :: v :: w :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u z [v, w] rho
  have hswap4 (u v w z q : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: rho).exchange 0 4 =
        some (q :: v :: w :: z :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u q [v, w, z] rho
  have hadd (u v : UInt256) : u + v = u.add v := by
    rfl
  have hzero (u : UInt256) : u.add (0 : UInt256) = u := by
    apply Word.word_ext
    change (u.val + (0 : UInt256).val).val = u.val.val
    rw [Fin.val_add]
    change (u.val.val + 0) % UInt256.size = u.val.val
    rw [Nat.add_zero, Nat.mod_eq_of_lt u.val.isLt]
  have hcomm (u v : UInt256) : u.add v = v.add u := by
    exact Word.word_add_comm u v
  have hxorcomm (u v : UInt256) : u.xor v = v.xor u := by
    exact BooleanSelect.xor_comm u v
  have hbase : constant.add
      ((MachineState.readWord s.memory xAddress.toNat).add
        ((c.xor (d.land (b.xor c))).add a)) =
      (((c.xor ((b.xor c).land d)).add a).add
        (MachineState.readWord s.memory xAddress.toNat)).add constant := by
    rw [hcomm constant, hcomm (MachineState.readWord s.memory xAddress.toNat)]
    rw [Word.land_comm d (b.xor c)]
  simp (config := { maxSteps := 2000000 })
    [f3Template, op, push1, push2, push4, dup1, dup2, dup3, dup4, dup5,
      dup6, swap1, swap2, swap3, swap4, mask, c10, c22,
      runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      roundEntry, roundReturned, roundWords, roundResult, roundWorking,
      roundWord, pcAfter, StackRound.stackRound, StackRound.stackF,
      StackRound.stackSum, StackRound.stackRawRot, StackRound.stackC10,
      Word.mask32, List.exchange, hrun, hcap, hswap1, hswap2, hswap3,
      hswap4, UInt256.succ, Instr.size, Instr.size_push, Instr.size_op,
      Nat.add_assoc, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, Word.land_comm, Word.lor_comm,
      BooleanSelect.xor_comm, State.activeWordsAfterUInt256, hadd, hzero,
      hxorcomm]
  constructor
  · rw [hbase, hcomm e]
    exact maskedRotateAdd _ _ _ _
  · exact Word.land_comm _ _

theorem runLocatedBlock_f3
    {artifact : ProgramArtifact} {fork : Fork}
    (xAddress : UInt256) (rotation : Nat) (constant : UInt256)
    (site : GenericRoundSite artifact fork
      (f3Template xAddress rotation constant))
    (s : State) (a b c d e : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock site.path
        (roundEntry s site.startPC a b c d e rest) =
      some (roundReturned s site.endPC
        3 a b c d e xAddress rotation constant rest) := by
  have hpc : site.endPC =
      pcAfter site.startPC (f3Template xAddress rotation constant) := by
    calc
      site.endPC = pcAfter site.startPC
          (site.sites.map (fun q => q.located.instruction)) :=
        endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
          site.head_eq site.end_eq site.contiguous
      _ = pcAfter site.startPC
          (f3Template xAddress rotation constant) := by
        rw [site.instruction_eq]
  have hadvance : ∀ located, located ∈ site.sites →
      ∀ {u v : State},
        Challenge.EvmProof.Stepper.runInstr located.located.instruction u = some v →
          v.pc = u.pc + UInt256.ofNat located.located.instruction.size := by
    intro located hmem u v hresult
    have hstraight : StraightLine located.located.instruction := by
      apply f3Template_straight
      rw [← site.instruction_eq]
      exact List.mem_map_of_mem hmem
    exact runInstr_pc_of_straight hstraight hresult
  calc
    Challenge.EvmProof.Stepper.runLocatedBlock site.path
        (roundEntry s site.startPC a b c d e rest) =
        runInstrSeq (f3Template xAddress rotation constant)
          (roundEntry s site.startPC a b c d e rest) :=
      runLocatedBlock_eq_runInstrSeq_site site
        (roundEntry s site.startPC a b c d e rest) rfl hadvance
    _ = some (roundReturned s
        (pcAfter site.startPC (f3Template xAddress rotation constant))
        3 a b c d e xAddress rotation constant rest) :=
      runInstrSeq_f3 s site.startPC a b c d e xAddress rotation constant rest
        hstack hrun
    _ = some (roundReturned s site.endPC
        3 a b c d e xAddress rotation constant rest) := by
      rw [hpc]

def gasSteps_f3
    {artifact : ProgramArtifact} {fork : Fork}
    (xAddress : UInt256) (rotation : Nat) (constant : UInt256)
    (site : GenericRoundSite artifact fork
      (f3Template xAddress rotation constant))
    (s : State) (a b c d e : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015)
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (roundEntry s site.startPC a b c d e rest)
      (roundReturned s site.endPC
        3 a b c d e xAddress rotation constant rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound artifact fork site.path
  · simpa [roundEntry] using hcode
  · simpa [roundEntry] using hfork
  · exact runLocatedBlock_f3 xAddress rotation constant site s a b c d e rest
      hstack hrun
  · simpa [roundEntry] using hrun
  · simpa [roundEntry] using hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSelectRoundTrace
