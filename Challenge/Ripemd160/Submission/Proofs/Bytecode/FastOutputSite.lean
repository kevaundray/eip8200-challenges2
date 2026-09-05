import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-!
# H31 fast-output site

The first 49 instructions of the fast-output helper are a straight-line
certificate.  The final `RETURN` is kept as a separate located site because it
does not advance the program counter.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputSite

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open StackRoundTemplate

private theorem advances_straight {instruction : Instr}
    (h : StraightLine instruction) : DenseScheduleLift.Advances instruction := by
  exact Or.inl (Or.inl h)

private theorem advances_jumpdest :
    DenseScheduleLift.Advances (.op .JUMPDEST) := by
  exact Or.inl (Or.inr (Or.inr rfl))

private theorem advances_mstore :
    DenseScheduleLift.Advances (.op .MSTORE) := by
  exact Or.inr rfl

private theorem advances_append {first second : List Instr}
    (hfirst : ∀ instruction ∈ first, DenseScheduleLift.Advances instruction)
    (hsecond : ∀ instruction ∈ second, DenseScheduleLift.Advances instruction) :
    ∀ instruction ∈ first ++ second, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · exact hfirst instruction hmem
  · exact hsecond instruction hmem

private theorem fastLoad0_advances :
    ∀ instruction ∈ FastOutputTemplate.fastLoad0,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [FastOutputTemplate.fastLoad0, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  all_goals exact advances_straight (by constructor)

private theorem fastPackStep_advances (address : Nat) :
    ∀ instruction ∈ FastOutputTemplate.fastPackStep address,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [FastOutputTemplate.fastPackStep, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  all_goals exact advances_straight (by constructor)

private theorem fastPackTemplate_advances :
    ∀ instruction ∈ FastOutputTemplate.fastPackTemplate,
      DenseScheduleLift.Advances instruction := by
  unfold FastOutputTemplate.fastPackTemplate
  apply advances_append
  · apply advances_append
    · apply advances_append
      · apply advances_append
        · apply advances_append
          · intro instruction hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with rfl
            exact advances_jumpdest
          · exact fastLoad0_advances
        · exact fastPackStep_advances 64
      · exact fastPackStep_advances 96
    · exact fastPackStep_advances 128
  · exact fastPackStep_advances 160

private theorem fastEndianStage8_advances :
    ∀ instruction ∈ FastOutputTemplate.fastEndianStage8,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [FastOutputTemplate.fastEndianStage8, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact advances_straight (by constructor)

private theorem fastEndianStage16_advances :
    ∀ instruction ∈ FastOutputTemplate.fastEndianStage16,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [FastOutputTemplate.fastEndianStage16, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact advances_straight (by constructor)

private theorem fastStoreAndSetup_advances :
    ∀ instruction ∈ FastOutputTemplate.fastStoreAndSetup,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [FastOutputTemplate.fastStoreAndSetup, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact advances_straight (by constructor)
  · exact advances_mstore
  · exact advances_straight (by constructor)
  · exact advances_straight (by constructor)

private theorem fastOutputBeforeReturn_advances :
    ∀ instruction ∈ FastOutputTemplate.fastOutputBeforeReturnTemplate,
      DenseScheduleLift.Advances instruction := by
  unfold FastOutputTemplate.fastOutputBeforeReturnTemplate
  apply advances_append fastPackTemplate_advances
  apply advances_append fastEndianStage8_advances
  apply advances_append fastEndianStage16_advances
  exact fastStoreAndSetup_advances

private theorem fastOutput_slice :
    (Artifact.submissionArtifact.instructions.drop 2742).take
        FastOutputTemplate.fastOutputBeforeReturnTemplate.length =
      FastOutputTemplate.fastOutputBeforeReturnTemplate := by
  rfl

def fastOutputSite :
    GenericRoundSite Artifact.submissionArtifact .Osaka
      FastOutputTemplate.fastOutputBeforeReturnTemplate :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact.submissionArtifact) (fork := .Osaka)
    FastOutputTemplate.fastOutputBeforeReturnTemplate 2742
    fastOutput_slice
    (by
      change 2742 + FastOutputTemplate.fastOutputBeforeReturnTemplate.length ≤
        Artifact.submissionInstructions.length
      rw [FastOutputTemplate.fastOutputBeforeReturnTemplate_length,
        Artifact.referenceInstructions_count]
      decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := FastOutputTemplate.fastOutputBeforeReturnTemplate) (by decide))
    (by decide)

@[simp] theorem fastOutputSite_startPC :
    fastOutputSite.startPC = UInt256.ofNat 0x11e4 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2742) =
    UInt256.ofNat 0x11e4
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem fastOutputSite_endPC :
    fastOutputSite.endPC = UInt256.ofNat 0x129d := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2791) =
    UInt256.ofNat 0x129d
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem fastOutputSite_end_eq_pcAfter :
    fastOutputSite.endPC =
      StackRoundTrace.pcAfter fastOutputSite.startPC
        FastOutputTemplate.fastOutputBeforeReturnTemplate := by
  have h := StackRoundTrace.endPC_eq_pcAfter_sites fastOutputSite.sites
    fastOutputSite.startPC fastOutputSite.endPC fastOutputSite.head_eq
    fastOutputSite.end_eq fastOutputSite.contiguous
  rwa [fastOutputSite.instruction_eq] at h

private theorem pc_toNat_instructionPC (index : Nat) :
    (UInt256.ofNat (Artifact.submissionArtifact.instructionPC index)).toNat =
      Artifact.submissionArtifact.instructionPC index := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt
    (Artifact.submissionArtifact.instructionPC_le_code_size index)
    QuadLayout.code_bound

def fastOutputReturn : LocatedSite Artifact.submissionArtifact .Osaka where
  located :=
    { index := 2791
      instruction := .op .RETURN
      atIndex := by rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2791)
  pc_eq := pc_toNat_instructionPC 2791

def fastOutputReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [fastOutputReturn.located]

@[simp] theorem fastOutputReturn_pc :
    fastOutputReturn.pc = UInt256.ofNat 0x129d := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2791) =
    UInt256.ofNat 0x129d
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem fastOutputReturn_site_end :
    fastOutputReturn.pc = fastOutputSite.endPC := by
  calc
    fastOutputReturn.pc = UInt256.ofNat 0x129d := fastOutputReturn_pc
    _ = fastOutputSite.endPC := fastOutputSite_endPC.symm

private theorem runLocatedBlock_singleton
    {artifact : ProgramArtifact} {fork : Fork}
    (located : Challenge.EvmProof.Stepper.Located artifact fork) (s : State) :
    Challenge.EvmProof.Stepper.runLocatedBlock [located] s =
      Challenge.EvmProof.Stepper.runLocated located s := by
  cases h : Challenge.EvmProof.Stepper.runLocated located s with
  | none => simp [Challenge.EvmProof.Stepper.runLocatedBlock, h]
  | some t => simp [Challenge.EvmProof.Stepper.runLocatedBlock, h]

private theorem fastOutputReturn_pc_eq_state
    (s : State) (rest : List UInt256) :
    (FastOutputTrace.fastOutputBeforeReturnState s (UInt256.ofNat 0x11e4) rest).pc =
      fastOutputReturn.pc := by
  calc
    (FastOutputTrace.fastOutputBeforeReturnState s (UInt256.ofNat 0x11e4) rest).pc =
        StackRoundTrace.pcAfter (UInt256.ofNat 0x11e4)
          FastOutputTemplate.fastOutputBeforeReturnTemplate := by rfl
    _ = StackRoundTrace.pcAfter fastOutputSite.startPC
          FastOutputTemplate.fastOutputBeforeReturnTemplate := by
      rw [fastOutputSite_startPC]
    _ = fastOutputSite.endPC := fastOutputSite_end_eq_pcAfter.symm
    _ = fastOutputReturn.pc := fastOutputReturn_site_end.symm

private theorem runFastOutputReturn
    (s : State) (rest : List UInt256)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fastOutputReturnPath
      (FastOutputTrace.fastOutputBeforeReturnState s (UInt256.ofNat 0x11e4) rest) =
      some (FastOutputTrace.fastOutputReturned s (UInt256.ofNat 0x11e4) rest) := by
  let t := FastOutputTrace.fastOutputBeforeReturnState s
    (UInt256.ofNat 0x11e4) rest
  have hrun_t : t.halt = .Running := by
    simpa [t, FastOutputTrace.fastOutputBeforeReturnState] using hrun
  have hpc_t : t.pc = fastOutputReturn.pc := by
    simpa [t] using fastOutputReturn_pc_eq_state s rest
  have hret_raw :
      StackRoundTrace.runInstrSeq FastOutputTemplate.fastOutputReturnTemplate t =
        some (FastOutputTrace.afterFastReturn t t.pc rest) := by
    have h := FastOutputTrace.runInstrSeq_fastReturn t t.pc rest hstack hrun_t
    simpa [t, FastOutputTrace.fastOutputBeforeReturnState] using h
  have hpre_raw :
      StackRoundTrace.runInstrSeq FastOutputTemplate.fastOutputBeforeReturnTemplate
          {s with pc := UInt256.ofNat 0x11e4, stack := rest} = some t := by
    simpa [t] using
      (FastOutputTrace.runInstrSeq_fastOutput_beforeReturn s
        (UInt256.ofNat 0x11e4) rest hstack hrun)
  have hfull_raw :
      StackRoundTrace.runInstrSeq FastOutputTemplate.fastOutputTemplate
          {s with pc := UInt256.ofNat 0x11e4, stack := rest} =
        some (FastOutputTrace.afterFastReturn t t.pc rest) := by
    have h := DenseScheduleTrace.runInstrSeq_append_running hpre_raw
      (by simpa [t, FastOutputTrace.fastOutputBeforeReturnState] using hrun)
      hret_raw
    simpa [FastOutputTemplate.fastOutputTemplate] using h
  have hfull_trace := FastOutputTrace.runInstrSeq_fastOutput s
    (UInt256.ofNat 0x11e4) rest hstack hrun
  have hstate :
      FastOutputTrace.afterFastReturn t t.pc rest =
      FastOutputTrace.fastOutputReturned s (UInt256.ofNat 0x11e4) rest :=
    Option.some.inj (hfull_raw.symm.trans hfull_trace)
  have hrun_instr :
      Stepper.runInstr (.op .RETURN) t =
        some (FastOutputTrace.afterFastReturn t t.pc rest) := by
    change (match Stepper.runInstr (.op .RETURN) t with
      | none => none
      | some next => some next) =
        some (FastOutputTrace.afterFastReturn t t.pc rest) at hret_raw
    cases h : Stepper.runInstr (.op .RETURN) t with
    | none =>
        simp [h] at hret_raw
    | some next =>
        have hnext : next = FastOutputTrace.afterFastReturn t t.pc rest := by
          simpa [h] using hret_raw
        subst next
        rfl
  have hpc_nat : t.pc.toNat = Artifact.submissionArtifact.instructionPC 2791 := by
    calc
      t.pc.toNat = fastOutputReturn.pc.toNat := by rw [hpc_t]
      _ = Artifact.submissionArtifact.instructionPC fastOutputReturn.located.index :=
        fastOutputReturn.pc_eq
      _ = Artifact.submissionArtifact.instructionPC 2791 := by rfl
  have hlocated :
      Stepper.runLocated fastOutputReturn.located t =
        some (FastOutputTrace.afterFastReturn t t.pc rest) := by
    simpa [Stepper.runLocated, fastOutputReturn, hpc_nat] using hrun_instr
  have hblock :
      Stepper.runLocatedBlock fastOutputReturnPath t =
        some (FastOutputTrace.afterFastReturn t t.pc rest) := by
    change Stepper.runLocatedBlock [fastOutputReturn.located] t = _
    rw [runLocatedBlock_singleton]
    exact hlocated
  rw [hstate] at hblock
  simpa [t] using hblock

def gasSteps_fastOutput
    (s : State) (rest : List UInt256)
    (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
      GasSteps
      {s with pc := UInt256.ofNat 0x11e4, stack := rest}
      (FastOutputTrace.fastOutputReturned s (UInt256.ofNat 0x11e4) rest) := by
  let entry : State := {s with pc := UInt256.ofNat 0x11e4, stack := rest}
  let middle : State := FastOutputTrace.fastOutputBeforeReturnState s
    (UInt256.ofNat 0x11e4) rest
  have hentry_code : entry.executionEnv.code = Artifact.submissionArtifact.code := by
    simpa [entry] using hcode
  have hentry_fork : entry.fork = .Osaka := by
    simpa [entry, State.fork] using hfork
  have hentry_run : entry.halt = .Running := by
    simpa [entry] using hrun
  have hentry_np :
      Precompile.isPrecompileWithConfig entry.executionEnv.precompileConfig
        entry.executionEnv.fork entry.executionEnv.codeAddr = false := by
    simpa [entry] using hnp
  have hentry_pc : entry.pc = fastOutputSite.startPC := by
    simp [entry]
  have hraw :
      StackRoundTrace.runInstrSeq FastOutputTemplate.fastOutputBeforeReturnTemplate entry =
        some middle := by
    simpa [entry, middle] using
      (FastOutputTrace.runInstrSeq_fastOutput_beforeReturn s
        (UInt256.ofNat 0x11e4) rest hstack hrun)
  have hpre : GasSteps entry middle :=
    DenseScheduleLift.gasSteps_of_raw fastOutputSite entry middle
      hentry_code hentry_fork hentry_run hentry_np hentry_pc
      fastOutputBeforeReturn_advances hraw
  have hmiddle_code : middle.executionEnv.code = Artifact.submissionArtifact.code := by
    simpa [middle, FastOutputTrace.fastOutputBeforeReturnState] using hcode
  have hmiddle_fork : middle.fork = .Osaka := by
    simpa [middle, FastOutputTrace.fastOutputBeforeReturnState, State.fork] using hfork
  have hmiddle_run : middle.halt = .Running := by
    simpa [middle, FastOutputTrace.fastOutputBeforeReturnState] using hrun
  have hmiddle_np :
      Precompile.isPrecompileWithConfig middle.executionEnv.precompileConfig
        middle.executionEnv.fork middle.executionEnv.codeAddr = false := by
    simpa [middle, FastOutputTrace.fastOutputBeforeReturnState] using hnp
  have hreturn : GasSteps middle
      (FastOutputTrace.fastOutputReturned s (UInt256.ofNat 0x11e4) rest) := by
    apply Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      fastOutputReturnPath
    · exact hmiddle_code
    · exact hmiddle_fork
    · simpa [middle] using runFastOutputReturn s rest hstack hrun
    · exact hmiddle_run
    · exact hmiddle_np
  simpa [entry, middle] using hpre.trans hreturn

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputSite
