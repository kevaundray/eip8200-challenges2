import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLoadSeams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLane
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open StackBlockModel StackEndpoint QuadLane StackLoadSeams

private theorem returnPC : Artifact.submissionArtifact.instructionPC 717 = 0x436 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

noncomputable def gasSteps_legacyBlock (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.compressEntry s input i)
      (DriverTrace.compressReturned (resultState s input i) input i) := by
  let q := scheduledState s input i
  let word := blockWords input i
  let w := initialWorking q
  let rest := StackFrame.frameRest input i
  let left := StackCompression.leftRounds word 80 w
  let right := StackCompression.rightRounds word 80 w
  let rightRest := StackFrame.savedLeft left ++ rest
  have qactive : 66 ≤ q.activeWords.toNat := by
    rw [scheduledState_activeWords s input hfit i hi]
    omega
  have qwords : QuadSemantic.DenseWordsAt q word :=
    scheduled_words_memory s input i h ctx hfit hi
  have qenv : q.executionEnv = s.executionEnv := by
    simp only [q, scheduledState, withActiveWords_executionEnv,
      withMemory_executionEnv, Schedule.loopState_executionEnv]
  have qcode : q.executionEnv.code = submissionBytecode := by rw [qenv]; exact hcode
  have qfork : q.fork = .Osaka := by rw [State.fork, qenv]; exact hfork
  have qrun : q.halt = .Running := by
    simp only [q, scheduledState, withActiveWords_halt, withMemory_halt,
      Schedule.loopState_halt, hrun]
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := by rw [qenv]; exact hnp
  have restBound : rest.length < 1007 := by
    simp [rest, StackFrame.frameRest, driverRest]
  have rightRestBound : rightRest.length < 1007 := by
    simp [rightRest, StackFrame.savedLeft, rest, StackFrame.frameRest, driverRest]
  have gframe := StackFrame.gasSteps_frame s input i hfit hi hcode hfork hrun hnp
  have gload1 := StackLoadTrace.gasSteps_load StackFrame.loadSite987 q
    (QuadRoundTemplate.factor :: rest) qactive
    (by simp [rest, StackFrame.frameRest, driverRest]) qcode qfork qrun qnp
  have gload1' : GasSteps (StackFrame.frameLoadEntry s input i)
      (stateAt q (QuadLayout.leftPC 0) w rest) := by
    exact gload1.cast (firstLoad_entry s input i)
      (firstLoad_returned q (QuadRoundTemplate.factor :: rest))
  have gleft := gasSteps_left80 q word w rest qwords qactive restBound qcode qfork qrun qnp
  have groute := StackFrame.gasSteps_route q left rest restBound qcode qfork qrun qnp
  have groute' : GasSteps (stateAt q (QuadLayout.leftPC 20) left rest)
      (StackFrame.routeReturned q left rest) :=
    groute.cast (routeEntry_atLanePC q left rest) rfl
  have gload2 := StackLoadTrace.gasSteps_load StackFrame.loadSite1238 q
    (QuadRoundTemplate.factor :: rightRest) qactive
    (by simp [rightRest, StackFrame.savedLeft, rest, StackFrame.frameRest, driverRest])
    qcode qfork qrun qnp
  have gload2' : GasSteps (StackFrame.routeReturned q left rest)
      (stateAt q (QuadLayout.rightPC 0) w rightRest) := by
    exact gload2.cast (secondLoad_entry q left rest)
      (secondLoad_returned q (QuadRoundTemplate.factor :: rightRest))
  have gright := gasSteps_right80 q word w rightRest qwords qactive rightRestBound
    qcode qfork qrun qnp
  have hvalid : Decode.isValidJumpDest q.executionEnv.code
      (UInt256.ofNat 0x436).toNat = true := by
    have hdest := Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
    rw [returnPC] at hdest
    change Decode.isValidJumpDest q.executionEnv.code 0x436 = true
    rw [qcode]
    exact hdest
  have gtail := QuadTailSite.actualTailGasSteps q left right (UInt256.ofNat 0x436)
    (driverRest input i) qactive (by simp [driverRest]) qcode qfork qrun qnp hvalid
  have tailSeam : stateAt q (QuadLayout.rightPC 20) right rightRest =
      QuadTailTemplate.tailEntry q left right (UInt256.ofNat 0x436) (driverRest input i) := by
    exact (tailEntry_atLanePC q left right (UInt256.ofNat 0x436) (driverRest input i)).symm
  have hleft : left = leftWorking s input i := by
    exact congrArg (StackCompression.leftRounds (blockWords input i) 80)
      (initialWorking_scheduled s input i)
  have hright : right = rightWorking s input i := by
    exact congrArg (StackCompression.rightRounds (blockWords input i) 80)
      (initialWorking_scheduled s input i)
  have tailEnd : QuadTailTemplate.finalResult q left right (UInt256.ofNat 0x436)
      (driverRest input i) =
      DriverTrace.compressReturned (resultState s input i) input i := by
    change StackTail.tailResult q left right (UInt256.ofNat 0x436)
      (driverRest input i) = _
    exact (congrArg₂ (fun l r => StackTail.tailResult q l r (UInt256.ofNat 0x436)
      (driverRest input i)) hleft hright).trans
      ((tailResult_eq_resultState s input i).trans (resultState_returned s input i))
  exact gframe.trans (gload1'.trans (gleft.trans (groute'.trans (gload2'.trans
    (gright.trans (gtail.cast tailSeam.symm tailEnd))))))

def nextState (s : State) (input : ByteArray) (i : Nat) : State :=
  if input.size = 0 then FastEmptyBlock.resultState s input i
  else resultState s input i

@[simp] theorem nextState_executionEnv (s : State) (input : ByteArray) (i : Nat) :
    (nextState s input i).executionEnv = s.executionEnv := by
  unfold nextState
  split <;> simp

@[simp] theorem nextState_halt (s : State) (input : ByteArray) (i : Nat) :
    (nextState s input i).halt = s.halt := by
  unfold nextState
  split <;> simp

@[simp] theorem nextState_callStack (s : State) (input : ByteArray) (i : Nat) :
    (nextState s input i).callStack = s.callStack := by
  unfold nextState
  split <;> simp

theorem nextState_word_above (s : State) (input : ByteArray) (i address : Nat)
    (haddress : 0x4a0 ≤ address) :
    StackRunBridge.wordAt (nextState s input i) address =
      StackRunBridge.wordAt s address := by
  unfold nextState
  split
  · exact FastEmptyBlock.resultState_word_above s input i address haddress
  · exact resultState_word_above s input i address haddress

private theorem input_eq_empty (input : ByteArray) (hempty : input.size = 0) :
    input = ByteArray.empty := by
  apply ByteArray.ext
  apply Array.ext
  · simpa using hempty
  · intro i hi
    simp [hempty] at hi

theorem nextState_hash (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (ctx : StackRunBridge.BlockContext s input i h)
    (hmodel : CompressionCorrect.hashArray h =
      CompressionSeamBridge.hashAfter input i) :
    StackRunBridge.hashAt32 (nextState s input i) =
      StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
          (Padding.paddedMessage input) (DriverTrace.blockOffset i)) := by
  unfold nextState
  by_cases hempty : input.size = 0
  · rw [if_pos hempty]
    have hinput := input_eq_empty input hempty
    subst input
    have hi0 : i = 0 := by
      simp [DriverTrace.blockCount, Padding.paddedLength] at hi
      omega
    subst i
    change StackMemory.hashAt (FastEmptyBlock.resultState s ByteArray.empty 0).memory = _
    rw [FastEmptyBlock.resultState_hashAt, hmodel]
    change FastEmptyBlock.emptyHash =
      StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock Crypto.Ripemd160.H0
          (Padding.paddedMessage ByteArray.empty) 0)
    rw [FastEmptyBlock.compress_empty]
    rfl
  · rw [if_neg hempty]
    exact resultState_hash s input i h ctx

noncomputable def gasSteps_block (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (ctx : StackRunBridge.BlockContext s input i h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.dispatchEntry s input i)
      (DriverTrace.compressReturned (nextState s input i) input i) := by
  by_cases hempty : input.size = 0
  · have gempty := FastEmptyBlock.gasSteps_empty s input i hempty
      ctx.calldata hcode hfork hrun hnp
    exact GasSteps.cast gempty (by rfl) (by
      simp [nextState, hempty, DriverTrace.compressReturned,
        FastEmptyBlock.resultState])
  · have gdispatch := FastEmptyBlock.gasSteps_nonempty s input i hfit
      (Nat.pos_of_ne_zero hempty) ctx.calldata hcode hfork hrun hnp
    have glegacy := gasSteps_legacyBlock s input i h hfit hi ctx hcode hfork
      hrun hnp
    exact GasSteps.cast (gdispatch.trans glegacy) (by rfl) (by
      simp [nextState, hempty])

noncomputable def kernel : StackRunBridge.BlockKernel where
  nextState := nextState
  executionEnv := nextState_executionEnv
  halt := nextState_halt
  callStack := nextState_callStack
  wordAbove := nextState_word_above
  hashResult := fun s input i h hfit hi ctx hmodel =>
    nextState_hash s input i h hfit hi ctx hmodel
  gasSteps := gasSteps_block

theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 0x3ee)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) :=
  StackRunBridge.correct_of_block_kernel kernel input hfit entryPrefix

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
