import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactCodecopy
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyPaths

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyTrace0

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactPaths KnownInputCompactState KnownInputState
open KnownInputCompactBodyPaths KnownInputCompactBodyState

private abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

theorem run_pre (s : State)
    (hrun : s.halt = .Running) :
    run prePath (KnownInputCompactState.bodyEntry s KnownInputData.targetInput 0) =
      some (preCopyState s KnownInputData.targetInput 0) := by
  have hcalc : UInt256.ofNat 4958 + UInt256.ofNat 21 *
      UInt256.shiftRight (UInt256.ofNat 0) (UInt256.ofNat 6) =
        UInt256.ofNat 4958 := by decide
  simp (config := { maxSteps := 1000000 })
    [prePath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
      KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      KnownInputCompactState.bodyEntry, preCopyState, tableSource,
      DriverTrace.blockOffsetWord, DriverTrace.blockOffset,
      hrun, hcalc, List.exchange, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_post (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run postPath (copiedState s KnownInputData.targetInput 0) =
      some (KnownInputCompactBodyState.resultState s KnownInputData.targetInput 0) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [postPath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
      KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      copiedState, tableSource, KnownInputCompactBodyState.resultState,
      KnownInputCompactBodyState.resultMemory,
      KnownInputCompactBodyState.resultActiveWords,
      tableMemory, storeLoaded, load4, activeAfter, KnownInputState.writeWord,
      hcode, hrun, hdest, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofUInt32]

private def soundFrom (path : List Located) (a b base : State)
    (hcode : base.executionEnv.code = submissionBytecode)
    (hfork : base.fork = .Osaka)
    (hresult : run path a = some b)
    (hrun : base.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig base.executionEnv.precompileConfig
      base.executionEnv.fork base.executionEnv.codeAddr = false)
    (henv : a.executionEnv = base.executionEnv := by rfl)
    (shalt : a.halt = base.halt := by rfl) : GasSteps a b := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path
  · rw [henv]; exact hcode
  · rw [State.fork, henv]; exact hfork
  · exact hresult
  · rw [shalt]; exact hrun
  · rw [henv]; exact hnp

def gasSteps_body (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (KnownInputCompactState.bodyEntry s KnownInputData.targetInput 0)
      (KnownInputCompactBodyState.resultState s KnownInputData.targetInput 0) := by
  have g0 := soundFrom prePath _ _ s hcode hfork (run_pre s hrun) hrun hnp
  have g1 := KnownInputCompactCodecopy.gasSteps_codecopy s
    KnownInputData.targetInput 0 (by decide) hcode hrun hnp
  have g2 := soundFrom postPath _ _ s hcode hfork
    (run_post s hcode hrun) hrun hnp
  exact g0.trans (g1.trans g2)

theorem run_pre_at (s : State) (i : Nat) (hi : i < 16)
    (hrun : s.halt = .Running) :
    run prePath (KnownInputCompactState.bodyEntry s KnownInputData.targetInput i) =
      some (preCopyState s KnownInputData.targetInput i) := by
  interval_cases i <;>
    simp (config := { maxSteps := 1000000 })
      [prePath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
        KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
        KnownInputCompactState.bodyEntry, preCopyState, tableSource,
        DriverTrace.blockOffsetWord, DriverTrace.blockOffset,
        hrun, List.exchange, State.activeWordsAfterUInt256,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod,
        Challenge.EvmProof.Word.word_toNat_ofNat]
  all_goals decide

theorem run_post_at (s : State) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    run postPath (copiedState s KnownInputData.targetInput i) =
      some (KnownInputCompactBodyState.resultState s KnownInputData.targetInput i) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [postPath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
      KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      copiedState, tableSource, KnownInputCompactBodyState.resultState,
      KnownInputCompactBodyState.resultMemory,
      KnownInputCompactBodyState.resultActiveWords,
      tableMemory, storeLoaded, load4, activeAfter, KnownInputState.writeWord,
      hcode, hrun, hdest, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofUInt32]

def gasSteps_body_at (s : State) (i : Nat) (hi : i < 16)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (KnownInputCompactState.bodyEntry s KnownInputData.targetInput i)
      (KnownInputCompactBodyState.resultState s KnownInputData.targetInput i) := by
  have g0 := soundFrom prePath _ _ s hcode hfork
    (run_pre_at s i hi hrun) hrun hnp
  have g1 := KnownInputCompactCodecopy.gasSteps_codecopy s
    KnownInputData.targetInput i hi hcode hrun hnp
  have g2 := soundFrom postPath _ _ s hcode hfork
    (run_post_at s i hcode hrun) hrun hnp
  exact g0.trans (g1.trans g2)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyTrace0
