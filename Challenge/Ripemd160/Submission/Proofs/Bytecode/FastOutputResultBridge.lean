import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionInterface
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputMath
import Challenge.Ripemd160.Submission.Proofs.Bytecode.GasCost

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputResultBridge

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open DirectCorrect

def driverRest (input : ByteArray) : List UInt256 :=
  [DriverTrace.blockOffsetWord (DriverTrace.blockCount input), Padding.paddedWord input]

def outputState (s : State) (input : ByteArray) : State :=
  FastOutputTrace.fastOutputReturned s (UInt256.ofNat 0x11e4) (driverRest input)

def outputBytes (s : State) : ByteArray :=
  MachineState.readPadded (FastOutputTrace.outputMemory s) 0 32

private theorem packed_stage_eq_template (value : UInt256)
    (shift : Nat) (mask : UInt256) :
    UInt256.lor
        (UInt256.land (DenseScheduleMemory.DensePacked.shr value shift) mask)
        (DenseScheduleMemory.DensePacked.shl (UInt256.land value mask) shift) =
      DenseScheduleTemplate.packedStage value shift mask := by
  unfold DenseScheduleMemory.DensePacked.shr DenseScheduleMemory.DensePacked.shl
    DenseScheduleTemplate.packedStage
  exact Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.lor_comm _ _

private theorem packed_eq_template (value : UInt256) :
    DenseScheduleMemory.DensePacked.packed value =
      DenseScheduleTemplate.packedWord value := by
  have hm8 : DenseScheduleMemory.DensePacked.mask8 = DenseScheduleTemplate.mask8 := rfl
  have hm16 : DenseScheduleMemory.DensePacked.mask16 = DenseScheduleTemplate.mask16 := rfl
  unfold DenseScheduleMemory.DensePacked.packed
  rw [hm8, hm16, packed_stage_eq_template, packed_stage_eq_template]
  rfl

private theorem outputBytes_eq_serialized (s : State) :
    outputBytes s = Data.Bytes.natToBytesPadded (FastOutputTrace.outputWord s).toNat 32 := by
  unfold outputBytes FastOutputTrace.outputMemory
  have h := Memory.readPadded_writeBytes_same s.memory
    (Data.Bytes.natToBytesPadded (FastOutputTrace.outputWord s).toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using h

private theorem outputBytes_eq_packed (s : State) (h0 h1 h2 h3 h4 : UInt32)
    (hw0 : FastOutputTrace.inputWord s 0 = Word.ofUInt32 h0)
    (hw1 : FastOutputTrace.inputWord s 1 = Word.ofUInt32 h1)
    (hw2 : FastOutputTrace.inputWord s 2 = Word.ofUInt32 h2)
    (hw3 : FastOutputTrace.inputWord s 3 = Word.ofUInt32 h3)
    (hw4 : FastOutputTrace.inputWord s 4 = Word.ofUInt32 h4) :
    outputBytes s = PackedOutputMath.packedOutput h0 h1 h2 h3 h4 := by
  rw [outputBytes_eq_serialized]
  unfold FastOutputTrace.outputWord
  rw [hw0, hw1, hw2, hw3, hw4]
  have hpack : FastOutputTemplate.packWords (Word.ofUInt32 h0) (Word.ofUInt32 h1)
      (Word.ofUInt32 h2) (Word.ofUInt32 h3) (Word.ofUInt32 h4) =
      PackedOutputMath.pack5 h0 h1 h2 h3 h4 := by rfl
  rw [hpack]
  change Data.Bytes.natToBytesPadded
      (DenseScheduleTemplate.packedWord (PackedOutputMath.pack5 h0 h1 h2 h3 h4)).toNat 32 = _
  rw [← packed_eq_template]
  rfl

private theorem outputBytes_eq_emitDigest (s : State) (H : Array UInt32)
    (hwords : ∀ i : Fin 5, OutputTrace.hWord s i = Word.ofUInt32 H[i.val]!) :
    outputBytes s = ByteArray.mk (Array.replicate 12 0) ++ SpecBridge.emitDigest H := by
  have hw (i : Fin 5) : FastOutputTrace.inputWord s i = Word.ofUInt32 H[i.val]! :=
    hwords i
  rw [outputBytes_eq_packed s H[0]! H[1]! H[2]! H[3]! H[4]!
    (hw ⟨0, by decide⟩) (hw ⟨1, by decide⟩) (hw ⟨2, by decide⟩)
    (hw ⟨3, by decide⟩) (hw ⟨4, by decide⟩)]
  rw [PackedOutputMath.packedOutput_eq_prefix_emitDigest]
  rfl

private theorem spec_eq (input : ByteArray) :
    spec input = ByteArray.mk (Array.replicate 12 0) ++ Crypto.Ripemd160.hash input := by
  unfold spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

private theorem outputBytes_eq_spec (input : ByteArray) (seam : CompressionSeam input) :
    outputBytes (seam.states (DriverTrace.blockCount input)) = spec input := by
  let H := SpecBridge.absorbBlocks Crypto.Ripemd160.H0 (Padding.paddedMessage input) 0
    (DriverTrace.blockCount input)
  rw [outputBytes_eq_emitDigest _ H seam.finalWords]
  rw [spec_eq, ← HashSpecBridge.paddedHash_eq_hash input]
  rfl

noncomputable def fullTrace (input : ByteArray) (hfit : CalldataFits input)
    (seam : CompressionSeam input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 0x3ee)) :
    GasSteps (initialState submissionBytecode input 0)
      (outputState (seam.states (DriverTrace.blockCount input)) input) := by
  let final := seam.states (DriverTrace.blockCount input)
  have gout := FastOutputSite.gasSteps_fastOutput final (driverRest input)
    (by simp [driverRest]) (seam.code _ (by omega)) (seam.fork _ (by omega))
    (seam.running _ (by omega)) (seam.noPrecompile _ (by omega))
  exact (PaddingTrace.gasSteps_pad input hfit entryPrefix).trans
    ((DirectCorrect.gasSteps_driver input hfit seam).trans
      (by simpa only [DriverTrace.afterExit, outputState, driverRest, final] using gout))

/-- The output proof needs only the existing compression seam. -/
theorem correct_of_compression_trace
    (seam : ∀ input : ByteArray, CalldataFits input → CompressionSeam input)
    (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 0x3ee)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := fullTrace input hfit (seam input hfit) entryPrefix
  let final := (seam input hfit).states (DriverTrace.blockCount input)
  have hcall : (outputState final input).callStack = [] :=
    (seam input hfit).callStack _ (by omega)
  have hreturned : (outputState final input).halt = .Returned := by rfl
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := Challenge.EvmProof.eval_of_steps (trace.trace gas hgas) (by
    change (withGas (outputState final input) (gas - trace.cost)).isDone = true
    simp [withGas, State.isDone, State.isHalted, State.isRunning, hcall, hreturned])
  rw [State.toResult_returned _ (by rfl)] at heval
  change Eval (withGas (initialState submissionBytecode input 0) gas)
    (.returned (outputBytes final)) at heval
  rw [outputBytes_eq_spec input (seam input hfit)] at heval
  simpa [GasCost.withGas_initialState_zero] using heval

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputResultBridge
