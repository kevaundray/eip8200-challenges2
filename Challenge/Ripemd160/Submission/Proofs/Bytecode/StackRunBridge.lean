import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputResultBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionSeamBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddedBlockBridge

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-!
# Generic outer compression-run bridge

This module carries the pure chaining invariant across a generic block kernel.
The kernel is the only bytecode-specific compression premise.  In particular,
this file does not assert that any concrete H10 endpoint has been verified.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRunBridge

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

def wordAt (s : State) (address : Nat) : UInt256 :=
  MachineState.readWord s.memory address

def hashAt32 (s : State) : Compression.EvmHashState :=
  { h0 := wordAt s 32
    h1 := wordAt s 64
    h2 := wordAt s 96
    h3 := wordAt s 128
    h4 := wordAt s 160 }

def embedHashArray (a : Array UInt32) : Compression.EvmHashState :=
  { h0 := Word.ofUInt32 a[0]!
    h1 := Word.ofUInt32 a[1]!
    h2 := Word.ofUInt32 a[2]!
    h3 := Word.ofUInt32 a[3]!
    h4 := Word.ofUInt32 a[4]! }

/-- Incoming-memory facts for one concrete compression call. -/
structure BlockContext (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) where
  calldata : s.executionEnv.calldata = input
  messageBlock : ScheduleCorrect.MessageBlockAt s.memory
    (DriverTrace.messageOffsetWord i) (Padding.paddedMessage input)
    (DriverTrace.blockOffset i)
  separated : ∀ k, k < 16 →
    0x4a0 ≤ (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord i) k).toNat
  hash : hashAt32 s = Compression.embedHash h

/-- A genuine compression endpoint and its exact one-block certificate. -/
structure BlockKernel where
  nextState : State → ByteArray → Nat → State
  executionEnv : ∀ s input i, (nextState s input i).executionEnv = s.executionEnv
  halt : ∀ s input i, (nextState s input i).halt = s.halt
  callStack : ∀ s input i, (nextState s input i).callStack = s.callStack
  wordAbove : ∀ s input i address, 0x4a0 ≤ address →
    wordAt (nextState s input i) address = wordAt s address
  hashResult : ∀ (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (_hfit : CalldataFits input)
    (_hi : i < DriverTrace.blockCount input) (_ctx : BlockContext s input i h)
    (_hmodel : CompressionCorrect.hashArray h =
      CompressionSeamBridge.hashAfter input i),
    hashAt32 (nextState s input i) =
      embedHashArray
        (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
          (Padding.paddedMessage input) (DriverTrace.blockOffset i))
  gasSteps : ∀ (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (_hfit : CalldataFits input)
    (_hi : i < DriverTrace.blockCount input) (_ctx : BlockContext s input i h)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (_hfork : s.fork = .Osaka) (_hrun : s.halt = .Running)
    (_hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false),
    GasSteps (DriverTrace.dispatchEntry s input i)
      (DriverTrace.compressReturned (nextState s input i) input i)

def states (kernel : BlockKernel) (input : ByteArray) : Nat → State
  | 0 => PaddingTrace.padReturned input
  | n + 1 => kernel.nextState (states kernel input n) input n

@[simp] theorem states_zero (kernel : BlockKernel) (input : ByteArray) :
    states kernel input 0 = PaddingTrace.padReturned input := by
  rfl

@[simp] theorem states_succ (kernel : BlockKernel) (input : ByteArray) (n : Nat) :
    states kernel input (n + 1) = kernel.nextState (states kernel input n) input n := by
  rfl

theorem states_executionEnv (kernel : BlockKernel) (input : ByteArray) (n : Nat) :
    (states kernel input n).executionEnv =
      (PaddingTrace.padReturned input).executionEnv := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [states, BlockKernel.executionEnv, ih]

theorem states_halt (kernel : BlockKernel) (input : ByteArray) (n : Nat) :
    (states kernel input n).halt = .Running := by
  induction n with
  | zero => exact PaddingTrace.padReturned_halt input
  | succ n ih =>
      rw [states, BlockKernel.halt, ih]

theorem states_calldata (kernel : BlockKernel) (input : ByteArray) (n : Nat) :
    (states kernel input n).executionEnv.calldata = input := by
  rw [states_executionEnv kernel input n]
  rfl

theorem states_callStack (kernel : BlockKernel) (input : ByteArray) (n : Nat) :
    (states kernel input n).callStack = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [states, BlockKernel.callStack, ih]

theorem states_word_above (kernel : BlockKernel) (input : ByteArray)
    (n address : Nat) (haddress : 0x4a0 ≤ address) :
    wordAt (states kernel input n) address =
      wordAt (PaddingTrace.padReturned input) address := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [states]
      exact (BlockKernel.wordAbove kernel (states kernel input n) input n address
        haddress).trans ih

theorem states_code (kernel : BlockKernel) (input : ByteArray) (n : Nat) :
    (states kernel input n).executionEnv.code = submissionBytecode := by
  rw [states_executionEnv kernel input n]
  exact PaddingTrace.padReturned_code input

theorem states_fork (kernel : BlockKernel) (input : ByteArray) (n : Nat) :
    (states kernel input n).fork = .Osaka := by
  change (states kernel input n).executionEnv.fork = .Osaka
  rw [states_executionEnv kernel input n]
  exact PaddingTrace.padReturned_fork input

theorem states_noPrecompile (kernel : BlockKernel) (input : ByteArray) (n : Nat) :
    Precompile.isPrecompileWithConfig (states kernel input n).executionEnv.precompileConfig
      (states kernel input n).executionEnv.fork (states kernel input n).executionEnv.codeAddr = false := by
  rw [states_executionEnv kernel input n]
  exact PaddingTrace.padReturned_noPrecompile input

theorem states_initial (kernel : BlockKernel) (input : ByteArray) :
    DriverTrace.setupEntry (states kernel input 0) input = PaddingTrace.padReturned input := by
  have hpc := PaddingTrace.padReturned_pc input
  have hstack := PaddingTrace.padReturned_stack input
  change DriverTrace.setupEntry (PaddingTrace.padReturned input) input =
    PaddingTrace.padReturned input
  unfold DriverTrace.setupEntry
  rw [← hpc, ← hstack]

def initialHashState : Compression.HashState :=
  { h0 := Crypto.Ripemd160.H0[0]!
    h1 := Crypto.Ripemd160.H0[1]!
    h2 := Crypto.Ripemd160.H0[2]!
    h3 := Crypto.Ripemd160.H0[3]!
    h4 := Crypto.Ripemd160.H0[4]! }

def hashStateAfter (input : ByteArray) : Nat → Compression.HashState
  | 0 => initialHashState
  | n + 1 => CompressionCorrect.compressModel
      (fun i =>
        (CompressionCorrect.schedule (Padding.paddedMessage input)
          (DriverTrace.blockOffset n))[i]!)
      (hashStateAfter input n)

theorem hashAfter_succ (input : ByteArray) (n : Nat) :
    CompressionSeamBridge.hashAfter input (n + 1) =
      Crypto.Ripemd160.compressBlock
        (CompressionSeamBridge.hashAfter input n)
        (Padding.paddedMessage input) (n * 64) := by
  unfold CompressionSeamBridge.hashAfter
  simpa using SpecBridge.absorbBlocks_succ Crypto.Ripemd160.H0
    (Padding.paddedMessage input) 0 n

theorem hashArray_hashStateAfter (input : ByteArray) (n : Nat) :
    CompressionCorrect.hashArray (hashStateAfter input n) =
      CompressionSeamBridge.hashAfter input n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [hashStateAfter, DriverTrace.blockOffset,
        CompressionCorrect.compressModel_eq_compressBlock,
        ih, hashAfter_succ]

private theorem padReturned_word_below (input : ByteArray)
    (hfit : CalldataFits input) (address : Nat)
    (haddress : address + 32 ≤ Padding.messageOffset) :
    wordAt (PaddingTrace.padReturned input) address =
      wordAt (Main.initializedState input) address := by
  unfold wordAt
  rw [PaddingTrace.padReturned_memory input hfit]
  unfold Padding.paddedMemory Padding.sentinelMemory Padding.copiedMemory
  have hpadded := Padding.input_and_footer_fit input.size
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · rfl
  all_goals
    left
    simp [Padding.messageOffset] at haddress ⊢
    omega

private theorem initialHashWords (kernel : BlockKernel) (input : ByteArray)
    (hfit : CalldataFits input) :
    CompressionSeamBridge.HashWordsAt input 0 (states kernel input 0) := by
  intro i
  change OutputTrace.hWord (PaddingTrace.padReturned input) i = _
  have hh := InitializationCorrect.initializedState_hash input i i.isLt
  unfold OutputTrace.hWord
  rw [show MachineState.readWord (PaddingTrace.padReturned input).memory
        (OutputTrace.hOffset i) =
      MachineState.readWord (Main.initializedState input).memory
        (OutputTrace.hOffset i) by
    exact padReturned_word_below input hfit _ (by
      unfold OutputTrace.hOffset Padding.messageOffset
      omega)]
  simpa [CompressionSeamBridge.hashAfter, SpecBridge.absorbBlocks,
    OutputTrace.hOffset, InitializationCorrect.slotWord, Nat.mul_comm] using hh

private theorem blockSeparated (input : ByteArray) (hfit : CalldataFits input)
    (n : Nat) (hn : n < DriverTrace.blockCount input) :
    ∀ k, k < 16 →
      0x4a0 ≤ (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord n) k).toNat := by
  simpa [DriverTrace.messageOffsetWord, DriverTrace.blockOffset,
    DriverTrace.blockCount] using
    PaddedBlockBridge.padReturned_blockIndexSeparated input hfit n (by
      simpa [DriverTrace.blockCount] using hn)

private theorem messageBlockAt (kernel : BlockKernel) (input : ByteArray)
    (hfit : CalldataFits input) (n : Nat)
    (hn : n < DriverTrace.blockCount input) :
    ScheduleCorrect.MessageBlockAt (states kernel input n).memory
      (DriverTrace.messageOffsetWord n) (Padding.paddedMessage input)
      (DriverTrace.blockOffset n) := by
  have hbase : ScheduleCorrect.MessageBlockAt
      (PaddingTrace.padReturned input).memory
      (DriverTrace.messageOffsetWord n) (Padding.paddedMessage input)
      (DriverTrace.blockOffset n) := by
    simpa [DriverTrace.messageOffsetWord, DriverTrace.blockOffset,
      DriverTrace.blockCount] using
      PaddedBlockBridge.padReturned_blockIndexAt input hfit n (by
        simpa [DriverTrace.blockCount] using hn)
  have hsep := blockSeparated input hfit n hn
  intro k hk
  unfold ScheduleCorrect.expectedWord Schedule.readLEWord
  rw [show MachineState.readWord (states kernel input n).memory
          (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord n) k).toNat =
        MachineState.readWord (PaddingTrace.padReturned input).memory
          (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord n) k).toNat by
    exact states_word_above kernel input n _ (hsep k hk)]
  exact hbase k hk

private theorem hashAt32_of_hashWords
    (hw : CompressionSeamBridge.HashWordsAt input n s) :
    hashAt32 s = Compression.embedHash (hashStateAfter input n) := by
  unfold hashAt32 Compression.embedHash
  rw [show wordAt s 32 = OutputTrace.hWord s 0 by rfl,
    show wordAt s 64 = OutputTrace.hWord s 1 by rfl,
    show wordAt s 96 = OutputTrace.hWord s 2 by rfl,
    show wordAt s 128 = OutputTrace.hWord s 3 by rfl,
    show wordAt s 160 = OutputTrace.hWord s 4 by rfl,
    hw ⟨0, by omega⟩, hw ⟨1, by omega⟩, hw ⟨2, by omega⟩,
    hw ⟨3, by omega⟩, hw ⟨4, by omega⟩]
  rw [← hashArray_hashStateAfter input n]
  rfl

private theorem hashWords_succ (kernel : BlockKernel) (input : ByteArray)
    (hfit : CalldataFits input) (n : Nat)
    (hn : n < DriverTrace.blockCount input)
    (hw : CompressionSeamBridge.HashWordsAt input n (states kernel input n)) :
    CompressionSeamBridge.HashWordsAt input (n + 1)
      (states kernel input (n + 1)) := by
  let h := hashStateAfter input n
  let ctx : BlockContext (states kernel input n) input n h := {
    calldata := states_calldata kernel input n
    messageBlock := messageBlockAt kernel input hfit n hn
    separated := blockSeparated input hfit n hn
    hash := hashAt32_of_hashWords hw }
  have hout := BlockKernel.hashResult kernel (states kernel input n)
    input n h hfit hn ctx (hashArray_hashStateAfter input n)
  have harray := hashArray_hashStateAfter input n
  rw [harray] at hout
  rw [states]
  intro i
  rw [hashAfter_succ]
  fin_cases i
  · exact congrArg Compression.EvmHashState.h0 hout
  · exact congrArg Compression.EvmHashState.h1 hout
  · exact congrArg Compression.EvmHashState.h2 hout
  · exact congrArg Compression.EvmHashState.h3 hout
  · exact congrArg Compression.EvmHashState.h4 hout

theorem hashWords (kernel : BlockKernel) (input : ByteArray)
    (hfit : CalldataFits input) :
    ∀ n, n ≤ DriverTrace.blockCount input →
      CompressionSeamBridge.HashWordsAt input n (states kernel input n) := by
  intro n hn
  induction n with
  | zero => exact initialHashWords kernel input hfit
  | succ n ih => exact hashWords_succ kernel input hfit n (by omega) (ih (by omega))

def compressionRun (kernel : BlockKernel) (input : ByteArray)
    (hfit : CalldataFits input) : CompressionSeamBridge.CompressionRun input where
  states := states kernel input
  initial := states_initial kernel input
  code := fun i _ => states_code kernel input i
  fork := fun i _ => states_fork kernel input i
  running := fun i _ => states_halt kernel input i
  noPrecompile := fun i _ => states_noPrecompile kernel input i
  callStack := fun i _ => states_callStack kernel input i
  blockTrace := by
    intro i hi
    let h := hashStateAfter input i
    let ctx : BlockContext (states kernel input i) input i h := {
      calldata := states_calldata kernel input i
      messageBlock := messageBlockAt kernel input hfit i hi
      separated := blockSeparated input hfit i hi
      hash := hashAt32_of_hashWords
        (hashWords kernel input hfit i (by omega)) }
    have hgas := BlockKernel.gasSteps kernel (states kernel input i)
      input i h hfit hi ctx
      (states_code kernel input i) (states_fork kernel input i)
      (states_halt kernel input i) (states_noPrecompile kernel input i)
    simpa [states] using hgas
  hashWords := fun i hi => hashWords kernel input hfit i hi

def compressionSeam (kernel : BlockKernel) :
    ∀ input : ByteArray, CalldataFits input → DirectCorrect.CompressionSeam input :=
  fun input hfit => CompressionSeamBridge.toCompressionSeam
    (compressionRun kernel input hfit)

/-- Correctness remains conditional on the genuine block kernel. -/
theorem correct_of_block_kernel (kernel : BlockKernel)
    (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 0x3ee)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  exact FastOutputResultBridge.correct_of_compression_trace (compressionSeam kernel) input hfit entryPrefix

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRunBridge
