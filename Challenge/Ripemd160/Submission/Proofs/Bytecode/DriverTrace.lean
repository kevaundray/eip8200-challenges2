import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddedBlockBridge

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-!
# Certified post-padding block driver

The reference bytecode at instruction indices 768--790 walks the padded
message in 64-byte blocks.  This file certifies the loop mechanics while
leaving the compression call as an explicit `GasSteps` seam.  Consequently
the driver can be composed with a compression proof without depending on its
internal state representation.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def setupPath : List Located :=
  [⟨702, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨703, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩]

def conditionPath : List Located :=
  [⟨704, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨705, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨706, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨707, .op .EQ, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨708, .push ⟨2, by decide⟩ (UInt256.ofNat 0x11e4), by rfl, by decide⟩,
   ⟨709, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def callPath : List Located :=
  [⟨710, .push ⟨2, by decide⟩ (UInt256.ofNat 0x436), by rfl, by decide⟩,
   ⟨711, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨712, .push ⟨2, by decide⟩ (UInt256.ofNat Padding.messageOffset),
      by rfl, by decide⟩,
   ⟨713, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨714, .push ⟨2, by decide⟩ (UInt256.ofNat 0x129e), by rfl, by decide⟩,
   ⟨715, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def incrementPath : List Located :=
  [⟨717, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨718, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨719, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨720, .push ⟨2, by decide⟩ (UInt256.ofNat 0x421), by rfl, by decide⟩,
   ⟨721, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem pc768 : Artifact.submissionArtifact.instructionPC 702 = 0x41f := by decide
@[simp] private theorem pc769 : Artifact.submissionArtifact.instructionPC 703 = 0x420 := by decide
@[simp] private theorem pc770 : Artifact.submissionArtifact.instructionPC 704 = 0x421 := by decide
@[simp] private theorem pc771 : Artifact.submissionArtifact.instructionPC 705 = 0x422 := by decide
@[simp] private theorem pc772 : Artifact.submissionArtifact.instructionPC 706 = 0x423 := by decide
@[simp] private theorem pc773 : Artifact.submissionArtifact.instructionPC 707 = 0x424 := by decide
@[simp] private theorem pc774 : Artifact.submissionArtifact.instructionPC 708 = 0x425 := by decide
@[simp] private theorem pc775 : Artifact.submissionArtifact.instructionPC 709 = 0x428 := by decide
@[simp] private theorem pc776 : Artifact.submissionArtifact.instructionPC 710 = 0x429 := by decide
@[simp] private theorem pc777 : Artifact.submissionArtifact.instructionPC 711 = 0x42c := by decide
@[simp] private theorem pc778 : Artifact.submissionArtifact.instructionPC 712 = 0x42d := by decide
@[simp] private theorem pc779 : Artifact.submissionArtifact.instructionPC 713 = 0x430 := by decide
@[simp] private theorem pc780 : Artifact.submissionArtifact.instructionPC 714 = 0x431 := by decide
@[simp] private theorem pc781 : Artifact.submissionArtifact.instructionPC 715 = 0x434 := by decide
@[simp] private theorem pc782 : Artifact.submissionArtifact.instructionPC 716 = 0x435 := by decide
@[simp] private theorem pc783 : Artifact.submissionArtifact.instructionPC 717 = 0x436 := by decide
@[simp] private theorem pc784 : Artifact.submissionArtifact.instructionPC 718 = 0x437 := by decide
@[simp] private theorem pc785 : Artifact.submissionArtifact.instructionPC 719 = 0x439 := by decide
@[simp] private theorem pc786 : Artifact.submissionArtifact.instructionPC 720 = 0x43a := by decide
@[simp] private theorem pc787 : Artifact.submissionArtifact.instructionPC 721 = 0x43d := by decide
@[simp] private theorem pc788 : Artifact.submissionArtifact.instructionPC 722 = 0x43e := by decide
@[simp] private theorem pc789 : Artifact.submissionArtifact.instructionPC 723 = 0x43f := by decide
@[simp] private theorem pc790 : Artifact.submissionArtifact.instructionPC 724 = 0x440 := by decide

def blockCount (input : ByteArray) : Nat :=
  Padding.paddedLength input.size / 64

def blockOffset (i : Nat) : Nat := i * 64

def blockOffsetWord (i : Nat) : UInt256 := UInt256.ofNat (blockOffset i)

def messageOffsetWord (i : Nat) : UInt256 :=
  UInt256.ofNat (Padding.messageOffset + blockOffset i)

def setupEntry (s : State) (input : ByteArray) : State :=
  { s with
    pc := UInt256.ofNat 0x41f
    stack := [Padding.paddedWord input] }

def loopAt (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x421
    stack := [blockOffsetWord i, Padding.paddedWord input] }

def afterCondition (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x429
    stack := [blockOffsetWord i, Padding.paddedWord input] }

/-- State at the appended empty-input dispatcher. Its stack matches the
ordinary compression entry stack. -/
def dispatchEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x129e
    stack := [messageOffsetWord i, UInt256.ofNat 0x436,
      blockOffsetWord i, Padding.paddedWord input] }

/-- State at the compression entry point. The helper receives the concrete
padded-message pointer, its return destination, and the driver invariant
stack underneath. -/
def compressEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x519
    stack := [messageOffsetWord i, UInt256.ofNat 0x436,
      blockOffsetWord i, Padding.paddedWord input] }

/-- Normalize an arbitrary post-compression state to the driver's return seam. -/
def compressReturned (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x436
    stack := [blockOffsetWord i, Padding.paddedWord input] }

def afterIteration (s : State) (input : ByteArray) (i : Nat) : State :=
  loopAt s input (i + 1)

def afterExit (s : State) (input : ByteArray) : State :=
  { s with
    pc := UInt256.ofNat 0x11e4
    stack := [blockOffsetWord (blockCount input), Padding.paddedWord input] }

theorem paddedLength_eq_blockCount (input : ByteArray) :
    Padding.paddedLength input.size = blockCount input * 64 := by
  exact Padding.paddedLength_eq_blocks input.size

private theorem paddedLength_lt_uint256 (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) :
    Padding.paddedLength input.size < 2 ^ 256 := by
  have hlt := Padding.paddedLength_lt input.size
  unfold Challenge.Ripemd160.CalldataFits at hfit
  norm_num at hfit ⊢
  omega

private theorem blockOffset_lt_uint256 (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i ≤ blockCount input) : blockOffset i < 2 ^ 256 := by
  have hpadded := paddedLength_lt_uint256 input hfit
  have heq := paddedLength_eq_blockCount input
  unfold blockOffset
  omega

private theorem messageOffset_lt_uint256 (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input) :
    Padding.messageOffset + blockOffset i < 2 ^ 256 := by
  have hpad := Padding.paddedLength_lt input.size
  have hoff : blockOffset i < Padding.paddedLength input.size := by
    rw [paddedLength_eq_blockCount input]
    unfold blockOffset
    omega
  unfold Challenge.Ripemd160.CalldataFits at hfit
  norm_num [Padding.messageOffset] at hfit ⊢
  omega

private theorem offset_ne_total (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input) :
    UInt256.eq (blockOffsetWord i) (Padding.paddedWord input) = 0 := by
  have hoff := blockOffset_lt_uint256 input hfit i (Nat.le_of_lt hi)
  have hpad := paddedLength_lt_uint256 input hfit
  have hnat : blockOffset i ≠ Padding.paddedLength input.size := by
    rw [paddedLength_eq_blockCount input]
    unfold blockOffset
    omega
  rw [Padding.paddedWord_eq input hfit]
  unfold UInt256.eq blockOffsetWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hpad]
  simp only [if_neg hnat]
  rfl

private theorem offset_eq_total (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) :
    UInt256.eq (blockOffsetWord (blockCount input))
      (Padding.paddedWord input) = UInt256.ofNat 1 := by
  have hoff := blockOffset_lt_uint256 input hfit (blockCount input) (by omega)
  have hpad := paddedLength_lt_uint256 input hfit
  have heq : blockOffset (blockCount input) =
      Padding.paddedLength input.size := by
    rw [paddedLength_eq_blockCount input]
    rfl
  rw [Padding.paddedWord_eq input hfit]
  unfold UInt256.eq blockOffsetWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hpad, heq]
  simp only [if_pos rfl]
  rfl

/-- The driver's concrete pointer selects block `i` of the padded message. -/
theorem padReturned_messageBlockAt (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input) :
    ScheduleCorrect.MessageBlockAt (PaddingTrace.padReturned input).memory
      (messageOffsetWord i) (Padding.paddedMessage input) (blockOffset i) := by
  simpa [messageOffsetWord, blockOffset, blockCount] using
    PaddedBlockBridge.padReturned_blockIndexAt input hfit i hi

/-- The same block pointer is separated from the sixteen schedule slots. -/
theorem padReturned_blockSeparated (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input) :
    ∀ k, k < 16 →
      0x4a0 ≤ (Schedule.loadOffsetWord (messageOffsetWord i) k).toNat := by
  simpa [messageOffsetWord, blockOffset, blockCount] using
    PaddedBlockBridge.padReturned_blockIndexSeparated input hfit i hi

theorem run_setup (s : State) (input : ByteArray)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupPath (setupEntry s input) =
      some (loopAt s input 0) := by
  simp [setupPath, setupEntry, loopAt, blockOffsetWord, blockOffset,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hrun]

theorem run_condition_continue (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock conditionPath (loopAt s input i) =
      some (afterCondition s input i) := by
  have heq := offset_ne_total input hfit i hi
  have hfalse : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [conditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopAt, afterCondition, hrun, heq, hfalse]

theorem run_condition_exit (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock conditionPath
      (loopAt s input (blockCount input)) = some (afterExit s input) := by
  have heq := offset_eq_total input hfit
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have honeNat : UInt256.toNat (1 : UInt256) = 1 := by decide
  have hdest : Decode.isValidJumpDest submissionBytecode 0x11e4 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2742 (by rfl)
  simp [conditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopAt, afterExit, hrun, hcode, heq,
    htrue, honeNat, UInt256.isTrue, hdest]

theorem run_call (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock callPath
      (afterCondition s input i) = some (dispatchEntry s input i) := by
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (messageOffset_lt_uint256 input hfit i hi)
  have hdest : Decode.isValidJumpDest submissionBytecode 0x129e = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2792 (by rfl)
  simp [callPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterCondition, dispatchEntry, messageOffsetWord, blockOffsetWord,
    hcode, hrun, hadd, hdest]

theorem run_increment (s : State) (input : ByteArray) (i : Nat)
    (hoff : blockOffset (i + 1) < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock incrementPath
      (compressReturned s input i) = some (afterIteration s input i) := by
  have haddBound : i * 64 + 64 < 2 ^ 256 := by
    simpa [blockOffset, Nat.add_mul] using hoff
  have hadd : blockOffsetWord i + UInt256.ofNat 64 =
      blockOffsetWord (i + 1) := by
    simpa [blockOffsetWord, blockOffset, Nat.add_mul] using
      Challenge.EvmProof.Word.ofNat_add_ofNat
        (a := i * 64) (b := 64) haddBound
  have hadd2 : UInt256.ofNat 64 + blockOffsetWord i =
      blockOffsetWord (i + 1) := by
    rw [show UInt256.ofNat 64 + blockOffsetWord i =
      blockOffsetWord i + UInt256.ofNat 64 from
        Challenge.EvmProof.Word.word_add_comm _ _]
    exact hadd
  have hdest : Decode.isValidJumpDest submissionBytecode 0x421 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 704 (by rfl)
  simp [incrementPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    compressReturned, afterIteration, loopAt,
    hcode, hrun, hadd2, hdest]

private def gasStepsBlock (path : List Located) (s t : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork hresult hrun hnp

def gasSteps_setup (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (setupEntry s input) (loopAt s input 0) :=
  gasStepsBlock setupPath _ _ hcode hfork (run_setup s input hrun) hrun hnp

def gasSteps_condition_continue (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopAt s input i) (afterCondition s input i) :=
  gasStepsBlock conditionPath _ _ hcode hfork
    (run_condition_continue s input hfit i hi hrun) hrun hnp

def gasSteps_condition_exit (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopAt s input (blockCount input))
      (afterExit s input) :=
  gasStepsBlock conditionPath _ _ hcode hfork
    (run_condition_exit s input hfit hcode hrun) hrun hnp

def gasSteps_call (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (afterCondition s input i)
      (dispatchEntry s input i) :=
  gasStepsBlock callPath _ _ hcode hfork
    (run_call s input hfit i hi hcode hrun) hrun hnp

def gasSteps_increment (s : State) (input : ByteArray) (i : Nat)
    (hoff : blockOffset (i + 1) < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (compressReturned s input i)
      (afterIteration s input i) :=
  gasStepsBlock incrementPath _ _ hcode hfork
    (run_increment s input i hoff hcode hrun) hrun hnp

/-- One complete driver iteration, parameterized by the compression proof. -/
def gasSteps_iteration_of_compress (s next : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input)
    (hcodeS : s.executionEnv.code = submissionBytecode)
    (hforkS : s.fork = .Osaka) (hrunS : s.halt = .Running)
    (hnpS : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hcodeNext : next.executionEnv.code = submissionBytecode)
    (hforkNext : next.fork = .Osaka) (hrunNext : next.halt = .Running)
    (hnpNext : Precompile.isPrecompileWithConfig next.executionEnv.precompileConfig next.executionEnv.fork
      next.executionEnv.codeAddr = false)
    (hcompress : Challenge.EvmProof.GasSteps (dispatchEntry s input i)
      (compressReturned next input i)) :
    Challenge.EvmProof.GasSteps (loopAt s input i)
      (afterIteration next input i) := by
  have hoff := blockOffset_lt_uint256 input hfit (i + 1) (by omega)
  exact (gasSteps_condition_continue s input hfit i hi hcodeS
      hforkS hrunS hnpS).trans
    ((gasSteps_call s input hfit i hi hcodeS hforkS hrunS hnpS).trans
      (hcompress.trans
        (gasSteps_increment next input i hoff hcodeNext hforkNext
          hrunNext hnpNext)))

/-- Iterate the driver over all padded blocks, given a state invariant family
and one compression certificate at each block. -/
def gasSteps_loop_of_compress (states : Nat → State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input)
    (hcode : ∀ i, i ≤ blockCount input →
      (states i).executionEnv.code = submissionBytecode)
    (hfork : ∀ i, i ≤ blockCount input → (states i).fork = .Osaka)
    (hrun : ∀ i, i ≤ blockCount input → (states i).halt = .Running)
    (hnp : ∀ i, i ≤ blockCount input →
      Precompile.isPrecompileWithConfig (states i).executionEnv.precompileConfig (states i).executionEnv.fork
        (states i).executionEnv.codeAddr = false)
    (hcompress : ∀ i, i < blockCount input →
      Challenge.EvmProof.GasSteps (dispatchEntry (states i) input i)
        (compressReturned (states (i + 1)) input i)) :
    Challenge.EvmProof.GasSteps (loopAt (states 0) input 0)
      (loopAt (states (blockCount input)) input (blockCount input)) := by
  apply Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => loopAt (states i) input i) (count := blockCount input)
  intro i hi
  simpa [afterIteration] using
    gasSteps_iteration_of_compress (states i) (states (i + 1)) input hfit i hi
      (hcode i (by omega)) (hfork i (by omega)) (hrun i (by omega))
      (hnp i (by omega)) (hcode (i + 1) (by omega))
      (hfork (i + 1) (by omega)) (hrun (i + 1) (by omega))
      (hnp (i + 1) (by omega)) (hcompress i hi)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace
