import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRunBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleActiveWords

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

/-!
# H10 block endpoint model

This names the endpoint used by the round and tail traces. The mathematical
message words are linked to the actual schedule slots below. No machine trace
or unconditional correctness theorem is asserted here.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackBlockModel

open Challenge.Ripemd160
open EvmSemantics EvmSemantics.EVM

def driverRest (input : ByteArray) (i : Nat) : List UInt256 :=
  [DriverTrace.blockOffsetWord i, Padding.paddedWord input]

def scheduleRest (input : ByteArray) (i : Nat) : List UInt256 :=
  [UInt256.ofNat 0x436] ++ driverRest input i

def withMemory (s : State) (memory : ByteArray) : State :=
  {s with memory := memory}

@[simp] theorem withMemory_memory (s : State) (memory : ByteArray) :
    (withMemory s memory).memory = memory := by rfl
@[simp] theorem withMemory_activeWords (s : State) (memory : ByteArray) :
    (withMemory s memory).activeWords = s.activeWords := by rfl
@[simp] theorem withMemory_executionEnv (s : State) (memory : ByteArray) :
    (withMemory s memory).executionEnv = s.executionEnv := by rfl
@[simp] theorem withMemory_halt (s : State) (memory : ByteArray) :
    (withMemory s memory).halt = s.halt := by rfl
@[simp] theorem withMemory_callStack (s : State) (memory : ByteArray) :
    (withMemory s memory).callStack = s.callStack := by rfl
@[simp] theorem withMemory_pc (s : State) (memory : ByteArray) :
    (withMemory s memory).pc = s.pc := by rfl
@[simp] theorem withMemory_stack (s : State) (memory : ByteArray) :
    (withMemory s memory).stack = s.stack := by rfl

def withActiveWords (s : State) (activeWords : UInt256) : State :=
  {s with activeWords := activeWords}

@[simp] theorem withActiveWords_memory (s : State) (activeWords : UInt256) :
    (withActiveWords s activeWords).memory = s.memory := by rfl
@[simp] theorem withActiveWords_activeWords (s : State) (activeWords : UInt256) :
    (withActiveWords s activeWords).activeWords = activeWords := by rfl
@[simp] theorem withActiveWords_executionEnv (s : State) (activeWords : UInt256) :
    (withActiveWords s activeWords).executionEnv = s.executionEnv := by rfl
@[simp] theorem withActiveWords_halt (s : State) (activeWords : UInt256) :
    (withActiveWords s activeWords).halt = s.halt := by rfl
@[simp] theorem withActiveWords_callStack (s : State) (activeWords : UInt256) :
    (withActiveWords s activeWords).callStack = s.callStack := by rfl

def scheduledState (s : State) (input : ByteArray) (i : Nat) : State :=
  withActiveWords
    (withMemory
      (Schedule.loopState s (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x523)
        (scheduleRest input i) 16)
      (DenseScheduleTemplate.denseExpectedMemory s (DriverTrace.messageOffsetWord i)))
    (DenseScheduleTemplate.denseExpectedActiveWords s
      (DriverTrace.messageOffsetWord i))

def blockWords (input : ByteArray) (i : Nat) : Nat → UInt32 :=
  fun k => (CompressionCorrect.schedule (Padding.paddedMessage input)
    (DriverTrace.blockOffset i))[k]!

theorem blockWords_eq_readLE32 (input : ByteArray) (i k : Nat) (hk : k < 16) :
    blockWords input i k = Crypto.Ripemd160.readLE32 (Padding.paddedMessage input)
      (DriverTrace.blockOffset i + k * 4) := by
  interval_cases k <;> simp [blockWords, CompressionCorrect.schedule, List.range']

def resultHash (s : State) (input : ByteArray) (i : Nat) : Compression.EvmHashState :=
  StackCompression.compress (blockWords input i) (StackMemory.hashAt s.memory)

def resultState (s : State) (input : ByteArray) (i : Nat) : State :=
  {scheduledState s input i with
    pc := UInt256.ofNat 0x436
    stack := driverRest input i
    memory := StackMemory.storeHash (scheduledState s input i).memory (resultHash s input i)}

@[simp] theorem resultState_executionEnv (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).executionEnv = s.executionEnv := by
  simp only [resultState, scheduledState, withActiveWords_executionEnv,
    withMemory_executionEnv,
    Schedule.loopState_executionEnv]

@[simp] theorem resultState_halt (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).halt = s.halt := by
  simp only [resultState, scheduledState, withActiveWords_halt, withMemory_halt,
    Schedule.loopState_halt]

private theorem scheduleLoop_callStack (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (Schedule.loopState s messageOffset returnDest rest n).callStack = s.callStack := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Schedule.loopState, Schedule.afterIteration, Schedule.afterStore,
      Schedule.afterRead, ih]

@[simp] theorem resultState_callStack (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).callStack = s.callStack := by
  simp only [resultState, scheduledState, withActiveWords_callStack,
    withMemory_callStack, scheduleLoop_callStack]

theorem scheduleLoop_word_outsideX (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (n address : Nat) (hn : n ≤ 16)
    (houtside : address + 32 ≤ 0x2a0 ∨ 0x4a0 ≤ address) :
    MachineState.readWord (Schedule.loopState s messageOffset returnDest rest n).memory
        address = MachineState.readWord s.memory address := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Schedule.loopState, ScheduleCorrect.afterIteration_memory]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
        rw [ScheduleCorrect.xSlotWord_toNat n (by omega)]
        rcases houtside with hbefore | hafter
        · left
          omega
        · right
          omega

private theorem denseWordBytes_size (value : UInt256) :
    (DenseScheduleTemplate.wordBytes value).size = 32 := by
  simp [DenseScheduleTemplate.wordBytes, Data.Bytes.natToBytesPadded,
    ByteArray.size]

private theorem denseStoreOffset_zero :
    DenseScheduleTemplate.denseStoreOffset 0 = 672 := by
  norm_num [DenseScheduleTemplate.denseStoreOffset,
    DenseScheduleTemplate.denseStoreAddress,
    Challenge.EvmProof.Word.word_toNat_ofNat]

private theorem denseStoreOffset_one :
    DenseScheduleTemplate.denseStoreOffset 1 = 704 := by
  norm_num [DenseScheduleTemplate.denseStoreOffset,
    DenseScheduleTemplate.denseStoreAddress,
    Challenge.EvmProof.Word.word_toNat_ofNat]

private theorem denseExpectedMemory_readWord_outside (s : State)
    (messageOffset : UInt256) (address : Nat)
    (houtside : address + 32 ≤ 672 ∨ 736 ≤ address) :
    MachineState.readWord
        (DenseScheduleTemplate.denseExpectedMemory s messageOffset) address =
      MachineState.readWord s.memory address := by
  rw [DenseScheduleTemplate.denseExpectedMemory, denseStoreOffset_zero,
    denseStoreOffset_one]
  unfold DenseScheduleTemplate.writeDenseWord
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ address 672 (by
    rcases houtside with hbefore | hafter
    · exact Or.inl hbefore
    · exact Or.inr (by rw [denseWordBytes_size]; omega)),
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ address 704 (by
      rcases houtside with hbefore | hafter
      · exact Or.inl (by omega)
      · exact Or.inr (by rw [denseWordBytes_size]; omega))]

private theorem densePacked_stage_eq_template (value : UInt256)
    (shift : Nat) (mask : UInt256) :
    UInt256.lor
        (UInt256.land
          (DenseScheduleMemory.DensePacked.shr value shift) mask)
        (DenseScheduleMemory.DensePacked.shl
          (UInt256.land value mask) shift) =
      DenseScheduleTemplate.packedStage value shift mask := by
  unfold DenseScheduleMemory.DensePacked.shr
    DenseScheduleMemory.DensePacked.shl
    DenseScheduleTemplate.packedStage
  exact Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.lor_comm _ _

private theorem densePacked_packedWord_eq_template (value : UInt256) :
    DenseScheduleMemory.DensePacked.packed value =
      DenseScheduleTemplate.packedWord value := by
  have hmask8 : DenseScheduleMemory.DensePacked.mask8 =
      DenseScheduleTemplate.mask8 := by
    rfl
  have hmask16 : DenseScheduleMemory.DensePacked.mask16 =
      DenseScheduleTemplate.mask16 := by
    rfl
  unfold DenseScheduleMemory.DensePacked.packed
  rw [hmask8, hmask16, densePacked_stage_eq_template,
    densePacked_stage_eq_template]
  rfl

private theorem denseExpectedMemory_eq_denseMemory (s : State) (p : Nat)
    (hbound : p + 64 < 2 ^ 256) :
    DenseScheduleTemplate.denseExpectedMemory s (UInt256.ofNat p) =
      DenseScheduleMemory.denseMemory s.memory p := by
  have hp : p < 2 ^ 256 := by omega
  have hp32 : p + 32 < 2 ^ 256 := by omega
  have hmessage : (UInt256.ofNat p).toNat = p := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hp]
  have hmessage32 :
      (UInt256.ofNat p + UInt256.ofNat 32).toNat = p + 32 := by
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat hp32,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hp32]
  rw [DenseScheduleTemplate.denseExpectedMemory, denseStoreOffset_zero,
    denseStoreOffset_one]
  simp only [DenseScheduleTemplate.writeDenseWord,
    DenseScheduleTemplate.wordBytes, DenseScheduleTemplate.packedInput0,
    DenseScheduleTemplate.packedInput1, DenseScheduleTemplate.inputWord0,
    DenseScheduleTemplate.inputWord1, hmessage, hmessage32,
    DenseScheduleMemory.denseMemory, DenseScheduleMemory.writePacked,
    DenseScheduleMemory.packedBytes]
  rw [densePacked_packedWord_eq_template,
    densePacked_packedWord_eq_template]
  exact DenseScheduleMemory.writePacked_comm_672_704 _ _ _

private theorem denseExpectedMemory_word_low32 (s : State) (p k : Nat)
    (hk : k < 16) (hbound : p + 64 < 2 ^ 256) :
    Challenge.EvmProof.Word.toUInt32
        (MachineState.readWord
          (DenseScheduleTemplate.denseExpectedMemory s (UInt256.ofNat p))
          (644 + 4 * k)) =
      Challenge.EvmProof.Word.toUInt32
        (ScheduleCorrect.expectedWord s.memory (UInt256.ofNat p) k) := by
  rw [denseExpectedMemory_eq_denseMemory s p hbound]
  simpa [DenseScheduleMemory.naturalp] using
    (DenseScheduleMemory.denseMemory_readWord_low32 s.memory p k hk hbound)

theorem resultState_word_above (s : State) (input : ByteArray) (i address : Nat)
    (haddress : 0x4a0 ≤ address) :
    StackRunBridge.wordAt (resultState s input i) address =
      StackRunBridge.wordAt s address := by
  unfold StackRunBridge.wordAt resultState
  rw [StackMemory.readWord_storeHash_ge_4a0 _ _ address haddress]
  simpa [scheduledState] using
    denseExpectedMemory_readWord_outside s (DriverTrace.messageOffsetWord i)
      address (Or.inr (by omega))

theorem scheduledState_hash (s : State) (input : ByteArray) (i : Nat) :
    StackMemory.hashAt (scheduledState s input i).memory = StackMemory.hashAt s.memory := by
  simp only [StackMemory.hashAt, scheduledState, withActiveWords_memory,
    withMemory_memory]
  rw [denseExpectedMemory_readWord_outside s _ 32 (Or.inl (by omega)),
    denseExpectedMemory_readWord_outside s _ 64 (Or.inl (by omega)),
    denseExpectedMemory_readWord_outside s _ 96 (Or.inl (by omega)),
    denseExpectedMemory_readWord_outside s _ 128 (Or.inl (by omega)),
    denseExpectedMemory_readWord_outside s _ 160 (Or.inl (by omega))]

theorem scheduledState_activeWords (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < DriverTrace.blockCount input) :
    (scheduledState s input i).activeWords.toNat = max s.activeWords.toNat (66 + 2 * i) := by
  rw [scheduledState, withActiveWords_activeWords]
  exact DenseScheduleActiveWords.expectedActiveWords_toNat s input hfit i hi

theorem scheduledState_words (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (ctx : StackRunBridge.BlockContext s input i h)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input)
    (k : Nat) (hk : k < 16) :
    Challenge.EvmProof.Word.toUInt32
        (MachineState.readWord (scheduledState s input i).memory (644 + 4 * k)) =
      blockWords input i k := by
  let p := Padding.messageOffset + 64 * i
  have hpadded := Padding.paddedLength_lt input.size
  have hsize : input.size < 2 ^ 64 := by
    simpa [CalldataFits] using hfit
  have hblocks : Padding.paddedLength input.size =
      (Padding.paddedLength input.size / 64) * 64 := by
    simpa [DriverTrace.blockCount] using
      (DriverTrace.paddedLength_eq_blockCount input)
  have hi' : i < Padding.paddedLength input.size / 64 := by
    simpa [DriverTrace.blockCount] using hi
  have hipadded : 64 * i + 64 ≤ Padding.paddedLength input.size := by
    omega
  have hbound : p + 64 < 2 ^ 256 := by
    norm_num [p, Padding.messageOffset] at hsize ⊢
    omega
  have hmessage : DriverTrace.messageOffsetWord i = UInt256.ofNat p := by
    simp [DriverTrace.messageOffsetWord, DriverTrace.blockOffset, p,
      Nat.mul_comm]
  have hblock : ScheduleCorrect.expectedWord s.memory (UInt256.ofNat p) k =
      Challenge.EvmProof.Word.ofUInt32
        (Crypto.Ripemd160.readLE32 (Padding.paddedMessage input)
          (DriverTrace.blockOffset i + k * 4)) := by
    simpa [hmessage] using ctx.messageBlock k hk
  calc
    Challenge.EvmProof.Word.toUInt32
        (MachineState.readWord (scheduledState s input i).memory (644 + 4 * k)) =
        Challenge.EvmProof.Word.toUInt32
          (ScheduleCorrect.expectedWord s.memory (UInt256.ofNat p) k) := by
      change Challenge.EvmProof.Word.toUInt32
          (MachineState.readWord
            (DenseScheduleTemplate.denseExpectedMemory s
              (DriverTrace.messageOffsetWord i)) (644 + 4 * k)) = _
      rw [hmessage]
      exact denseExpectedMemory_word_low32 s p k hk hbound
    _ = blockWords input i k := by
      rw [hblock, Challenge.EvmProof.Word.toUInt32_ofUInt32]
      exact (blockWords_eq_readLE32 input i k hk).symm

theorem resultState_hash (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (ctx : StackRunBridge.BlockContext s input i h) :
    StackRunBridge.hashAt32 (resultState s input i) =
      StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
          (Padding.paddedMessage input) (DriverTrace.blockOffset i)) := by
  change StackMemory.hashAt (StackMemory.storeHash (scheduledState s input i).memory
    (resultHash s input i)) = _
  rw [StackMemory.hashAt_storeHash]
  unfold resultHash
  have hhash : StackMemory.hashAt s.memory = Compression.embedHash h := ctx.hash
  rw [hhash, StackCompression.compress_embed]
  rw [← CompressionCorrect.compressModel_eq_compressBlock
    (Padding.paddedMessage input) (DriverTrace.blockOffset i) h]
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackBlockModel
