import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionTailComposition

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-!
# Functional refinement of the concrete compression trace

This layer is deliberately separate from the executable trace.  It records
the mathematical invariant carried by the concrete `leftStates` and
`rightStates` folds and connects the tail stores to `compressBlock`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionFunctionalTrace

open EvmSemantics
open EvmSemantics.EVM
open CompressionTrace
open CompressionRightTrace
open CompressionTailTrace

def blockWords (padded : ByteArray) (blockOff : Nat) : Nat → UInt32 :=
  fun i => (CompressionCorrect.schedule padded blockOff)[i]!

private theorem blockWords_eq_readLE32 (padded : ByteArray) (blockOff i : Nat)
    (hi : i < 16) :
    blockWords padded blockOff i =
      Crypto.Ripemd160.readLE32 padded (blockOff + i * 4) := by
  unfold blockWords
  interval_cases i <;>
    simp [CompressionCorrect.schedule, List.range']

def rightInitialState (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  leftFinalState s messageOffset returnDest rest

def rightFinalState (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  rightStates (rightInitialState s messageOffset returnDest rest)
    messageOffset returnDest rest 80

def hashAt32 (s : State) : Compression.EvmHashState :=
  { h0 := wordAt s 32
    h1 := wordAt s 64
    h2 := wordAt s 96
    h3 := wordAt s 128
    h4 := wordAt s 160 }

/-- Embed the five-word array returned by `Crypto.Ripemd160.compressBlock`
into the EVM-word representation used by the concrete memory trace. -/
def embedHashArray (a : Array UInt32) : Compression.EvmHashState :=
  { h0 := Challenge.EvmProof.Word.ofUInt32 a[0]!
    h1 := Challenge.EvmProof.Word.ofUInt32 a[1]!
    h2 := Challenge.EvmProof.Word.ofUInt32 a[2]!
    h3 := Challenge.EvmProof.Word.ofUInt32 a[3]!
    h4 := Challenge.EvmProof.Word.ofUInt32 a[4]! }

@[simp] theorem embedHashArray_hashArray (h : Compression.HashState) :
    embedHashArray (CompressionCorrect.hashArray h) =
      Compression.embedHash h := by
  rfl

/-- Raw, algorithm-facing facts available at a concrete compressor call.
Unlike `BlockRefinement`, these fields only describe the incoming memory;
all preservation across schedule, copies, and rounds is proved below. -/
structure BlockInputs (s : State) (messageOffset : UInt256)
    (padded : ByteArray) (blockOff : Nat) (h : Compression.HashState) where
  separated : ∀ k, k < 16 →
    0x4a0 ≤ (Schedule.loadOffsetWord messageOffset k).toNat
  messageBlock : ScheduleCorrect.MessageBlockAt s.memory messageOffset
    padded blockOff
  tables : InitializationCorrect.TablesCorrect s.memory
  constants :
    (∀ j, j < 5 →
      InitializationCorrect.slotWord s.memory 0x620 j =
        Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!)) ∧
    (∀ j, j < 5 →
      InitializationCorrect.slotWord s.memory 0x6c0 j =
        Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!))
  hash : hashAt32 s = Compression.embedHash h

private theorem loopState_word_outsideX (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (n address : Nat) (hn : n ≤ 16)
    (houtside : address + 32 ≤ 0x2a0 ∨ 0x4a0 ≤ address) :
    wordAt (Schedule.loopState s messageOffset returnDest rest n) address =
      wordAt s address := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Schedule.loopState]
      unfold wordAt
      simp only [ScheduleCorrect.afterIteration_memory]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
        rw [ScheduleCorrect.xSlotWord_toNat n (by omega)]
        rcases houtside with hbefore | hafter
        · left
          omega
        · right
          omega

theorem scheduledState_word_outsideX (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (address : Nat)
    (houtside : address + 32 ≤ 0x2a0 ∨ 0x4a0 ≤ address) :
    wordAt (scheduledState s messageOffset returnDest rest) address =
      wordAt s address := by
  exact loopState_word_outsideX s messageOffset (UInt256.ofNat 630)
    (messageOffset :: returnDest :: rest) 16 address (by omega) houtside

private theorem copyRegion_word_inside (s : State) (dest src size off : Nat)
    (hoff : off + 32 ≤ size) :
    wordAt (copyRegion s dest src size) (dest + off) =
      wordAt s (src + off) := by
  unfold wordAt copyRegion MachineState.readWord
  apply congrArg UInt256.ofNat
  apply congrArg Data.Bytes.bytesToBigEndianNat
  change MachineState.readPadded
      (MachineState.writeBytes s.memory
        (MachineState.readPadded s.memory src size) dest)
      (dest + off) 32 = MachineState.readPadded s.memory (src + off) 32
  apply ByteArray.ext_getElem
  · simp
  · intro i hi₁ hi₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₂,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD]
    have hi : i < 32 := by simpa using hi₁
    rw [if_pos hi, if_pos hi, MachineState.writeBytes_getElem?_getD,
      if_pos (by
        rw [Challenge.EvmProof.Memory.readPadded_size]
        omega),
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos (by omega)]
    congr 2
    omega

private theorem copyRegion_word_disjoint (s : State) (dest src size address : Nat)
    (hdisjoint : address + 32 ≤ dest ∨ dest + size ≤ address) :
    wordAt (copyRegion s dest src size) address = wordAt s address := by
  unfold wordAt copyRegion
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa only [Challenge.EvmProof.Memory.readPadded_size] using hdisjoint

private theorem copiedWorkingState_word_left (s : State) (off : Nat)
    (hoff : off + 32 ≤ 160) :
    wordAt (copiedWorkingState s) (192 + off) = wordAt s (32 + off) := by
  unfold copiedWorkingState
  calc
    wordAt (copyRegion
        (copyRegion (copyRegion s 192 32 160) 352 32 160) 512 32 160)
        (192 + off) =
      wordAt (copyRegion (copyRegion s 192 32 160) 352 32 160)
        (192 + off) := copyRegion_word_disjoint _ _ _ _ _ (Or.inl (by omega))
    _ = wordAt (copyRegion s 192 32 160) (192 + off) :=
      copyRegion_word_disjoint _ _ _ _ _ (Or.inl (by omega))
    _ = wordAt s (32 + off) := copyRegion_word_inside _ _ _ _ _ hoff

private theorem copiedWorkingState_word_right (s : State) (off : Nat)
    (hoff : off + 32 ≤ 160) :
    wordAt (copiedWorkingState s) (352 + off) = wordAt s (32 + off) := by
  unfold copiedWorkingState
  calc
    wordAt (copyRegion
        (copyRegion (copyRegion s 192 32 160) 352 32 160) 512 32 160)
        (352 + off) =
      wordAt (copyRegion (copyRegion s 192 32 160) 352 32 160)
        (352 + off) := copyRegion_word_disjoint _ _ _ _ _ (Or.inl (by omega))
    _ = wordAt (copyRegion s 192 32 160) (32 + off) :=
      copyRegion_word_inside _ _ _ _ _ hoff
    _ = wordAt s (32 + off) :=
      copyRegion_word_disjoint _ _ _ _ _ (Or.inl (by omega))

private theorem copiedWorkingState_word_saved (s : State) (off : Nat)
    (hoff : off + 32 ≤ 160) :
    wordAt (copiedWorkingState s) (512 + off) = wordAt s (32 + off) := by
  unfold copiedWorkingState
  calc
    wordAt (copyRegion
        (copyRegion (copyRegion s 192 32 160) 352 32 160) 512 32 160)
        (512 + off) =
      wordAt (copyRegion (copyRegion s 192 32 160) 352 32 160)
        (32 + off) := copyRegion_word_inside _ _ _ _ _ hoff
    _ = wordAt (copyRegion s 192 32 160) (32 + off) :=
      copyRegion_word_disjoint _ _ _ _ _ (Or.inl (by omega))
    _ = wordAt s (32 + off) :=
      copyRegion_word_disjoint _ _ _ _ _ (Or.inl (by omega))

private theorem copiedWorkingState_word_above (s : State) (address : Nat)
    (haddress : 0x2a0 ≤ address) :
    wordAt (copiedWorkingState s) address = wordAt s address := by
  unfold copiedWorkingState
  rw [copyRegion_word_disjoint, copyRegion_word_disjoint,
    copyRegion_word_disjoint] <;> right <;> omega

private theorem copiedWorkingState_word_below (s : State) (address : Nat)
    (haddress : address + 32 ≤ 192) :
    wordAt (copiedWorkingState s) address = wordAt s address := by
  unfold copiedWorkingState
  rw [copyRegion_word_disjoint, copyRegion_word_disjoint,
    copyRegion_word_disjoint] <;> left <;> omega

theorem copiedWorkingState_left (s : State) :
    workingAt (copiedWorkingState s) 192 =
      CompressionCorrect.evmWorkingOfHash (hashAt32 s) := by
  unfold workingAt hashAt32 CompressionCorrect.evmWorkingOfHash
  rw [copiedWorkingState_word_left s 0 (by omega),
    copiedWorkingState_word_left s 32 (by omega),
    copiedWorkingState_word_left s 64 (by omega),
    copiedWorkingState_word_left s 96 (by omega),
    copiedWorkingState_word_left s 128 (by omega)]

theorem copiedWorkingState_right (s : State) :
    workingAt (copiedWorkingState s) 352 =
      CompressionCorrect.evmWorkingOfHash (hashAt32 s) := by
  unfold workingAt hashAt32 CompressionCorrect.evmWorkingOfHash
  rw [copiedWorkingState_word_right s 0 (by omega),
    copiedWorkingState_word_right s 32 (by omega),
    copiedWorkingState_word_right s 64 (by omega),
    copiedWorkingState_word_right s 96 (by omega),
    copiedWorkingState_word_right s 128 (by omega)]

theorem copiedWorkingState_saved (s : State) :
    savedHashAt512 (copiedWorkingState s) = hashAt32 s := by
  unfold savedHashAt512 hashAt32
  rw [copiedWorkingState_word_saved s 0 (by omega),
    copiedWorkingState_word_saved s 32 (by omega),
    copiedWorkingState_word_saved s 64 (by omega),
    copiedWorkingState_word_saved s 96 (by omega),
    copiedWorkingState_word_saved s 128 (by omega)]

theorem scheduledState_hashAt32 (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    hashAt32 (scheduledState s messageOffset returnDest rest) = hashAt32 s := by
  unfold hashAt32
  rw [scheduledState_word_outsideX s messageOffset returnDest rest 32 (by omega),
    scheduledState_word_outsideX s messageOffset returnDest rest 64 (by omega),
    scheduledState_word_outsideX s messageOffset returnDest rest 96 (by omega),
    scheduledState_word_outsideX s messageOffset returnDest rest 128 (by omega),
    scheduledState_word_outsideX s messageOffset returnDest rest 160 (by omega)]

theorem leftInitialState_working (inputs :
    BlockInputs s messageOffset padded blockOff h) :
    workingAt (leftInitialState s messageOffset returnDest rest) 192 =
      CompressionCorrect.evmWorkingOfHash (Compression.embedHash h) := by
  rw [leftInitialState, copiedWorkingState_left,
    scheduledState_hashAt32, inputs.hash]

theorem leftInitialState_rightWorking (inputs :
    BlockInputs s messageOffset padded blockOff h) :
    workingAt (leftInitialState s messageOffset returnDest rest) 352 =
      CompressionCorrect.evmWorkingOfHash (Compression.embedHash h) := by
  rw [leftInitialState, copiedWorkingState_right,
    scheduledState_hashAt32, inputs.hash]

theorem leftInitialState_saved (inputs :
    BlockInputs s messageOffset padded blockOff h) :
    savedHashAt512 (leftInitialState s messageOffset returnDest rest) =
      Compression.embedHash h := by
  rw [leftInitialState, copiedWorkingState_saved,
    scheduledState_hashAt32, inputs.hash]

theorem leftInitialState_words (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (address : Nat) (haddress : 0x4a0 ≤ address) :
    wordAt (leftInitialState s messageOffset returnDest rest) address =
      wordAt s address := by
  unfold leftInitialState
  rw [copiedWorkingState_word_above]
  · exact scheduledState_word_outsideX s messageOffset returnDest rest address
      (Or.inr haddress)
  · omega

theorem leftInitialState_tables (inputs :
    BlockInputs s messageOffset padded blockOff h) :
    InitializationCorrect.TablesCorrect
      (leftInitialState s messageOffset returnDest rest).memory := by
  rcases inputs.tables with ⟨hr, hrP, hs, hsP⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    unfold InitializationCorrect.tableByte
    change UInt256.byteAt (UInt256.ofNat (i % 32))
      (wordAt (leftInitialState s messageOffset returnDest rest)
        (0x4a0 + 32 * (i / 32))) = _
    rw [leftInitialState_words s messageOffset returnDest rest
      (0x4a0 + 32 * (i / 32)) (by omega)]
    exact hr i hi
  · intro i hi
    unfold InitializationCorrect.tableByte
    change UInt256.byteAt (UInt256.ofNat (i % 32))
      (wordAt (leftInitialState s messageOffset returnDest rest)
        (0x500 + 32 * (i / 32))) = _
    rw [leftInitialState_words s messageOffset returnDest rest
      (0x500 + 32 * (i / 32)) (by omega)]
    exact hrP i hi
  · intro i hi
    unfold InitializationCorrect.tableByte
    change UInt256.byteAt (UInt256.ofNat (i % 32))
      (wordAt (leftInitialState s messageOffset returnDest rest)
        (0x560 + 32 * (i / 32))) = _
    rw [leftInitialState_words s messageOffset returnDest rest
      (0x560 + 32 * (i / 32)) (by omega)]
    exact hs i hi
  · intro i hi
    unfold InitializationCorrect.tableByte
    change UInt256.byteAt (UInt256.ofNat (i % 32))
      (wordAt (leftInitialState s messageOffset returnDest rest)
        (0x5c0 + 32 * (i / 32))) = _
    rw [leftInitialState_words s messageOffset returnDest rest
      (0x5c0 + 32 * (i / 32)) (by omega)]
    exact hsP i hi

theorem leftInitialState_constants (inputs :
    BlockInputs s messageOffset padded blockOff h) :
    (∀ j, j < 5 →
      InitializationCorrect.slotWord
          (leftInitialState s messageOffset returnDest rest).memory 0x620 j =
        Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!)) ∧
    (∀ j, j < 5 →
      InitializationCorrect.slotWord
          (leftInitialState s messageOffset returnDest rest).memory 0x6c0 j =
        Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!)) := by
  rcases inputs.constants with ⟨hk, hkP⟩
  refine ⟨?_, ?_⟩
  · intro j hj
    unfold InitializationCorrect.slotWord
    change wordAt (leftInitialState s messageOffset returnDest rest)
      (0x620 + 32 * j) = _
    rw [leftInitialState_words s messageOffset returnDest rest
      (0x620 + 32 * j) (by omega)]
    exact hk j hj
  · intro j hj
    unfold InitializationCorrect.slotWord
    change wordAt (leftInitialState s messageOffset returnDest rest)
      (0x6c0 + 32 * j) = _
    rw [leftInitialState_words s messageOffset returnDest rest
      (0x6c0 + 32 * j) (by omega)]
    exact hkP j hj

/-- The concrete schedule state contains the sixteen little-endian words of
the selected padded-message block. -/
theorem scheduledState_words (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (padded : ByteArray) (blockOff : Nat)
    (hseparated : ∀ k, k < 16 →
      0x4a0 ≤ (Schedule.loadOffsetWord messageOffset k).toNat)
    (hblock : ScheduleCorrect.MessageBlockAt s.memory messageOffset
      padded blockOff) :
    ∀ k, k < 16 →
      ScheduleCorrect.xValue
        (scheduledState s messageOffset returnDest rest) k =
        Challenge.EvmProof.Word.ofUInt32
          (Crypto.Ripemd160.readLE32 padded (blockOff + k * 4)) := by
  intro k hk
  unfold scheduledState
  exact ScheduleCorrect.loopState_sixteen_cryptoWords s messageOffset
    (UInt256.ofNat 630) (messageOffset :: returnDest :: rest)
    padded blockOff hseparated hblock k hk

theorem leftInitialState_words_crypto (inputs :
    BlockInputs s messageOffset padded blockOff h) :
    ∀ k, k < 16 →
      ScheduleCorrect.xValue
        (leftInitialState s messageOffset returnDest rest) k =
        Challenge.EvmProof.Word.ofUInt32
          (Crypto.Ripemd160.readLE32 padded (blockOff + k * 4)) := by
  intro k hk
  unfold leftInitialState ScheduleCorrect.xValue
  change wordAt (copiedWorkingState
    (scheduledState s messageOffset returnDest rest))
      (Schedule.xSlotWord k).toNat = _
  rw [copiedWorkingState_word_above]
  · exact scheduledState_words s messageOffset returnDest rest padded blockOff
      inputs.separated inputs.messageBlock k hk
  · rw [ScheduleCorrect.xSlotWord_toNat k hk]
    omega

private theorem leftRotation_pos (i : Nat) (hi : i < 80) :
    0 < Crypto.Ripemd160.s[i]! := by
  interval_cases i <;> decide

private theorem leftRotation_lt (i : Nat) (hi : i < 80) :
    Crypto.Ripemd160.s[i]! < 32 := by
  interval_cases i <;> decide

private theorem rightRotation_pos (i : Nat) (hi : i < 80) :
    0 < Crypto.Ripemd160.sP[i]! := by
  interval_cases i <;> decide

private theorem rightRotation_lt (i : Nat) (hi : i < 80) :
    Crypto.Ripemd160.sP[i]! < 32 := by
  interval_cases i <;> decide

private theorem leftSelector_lt (i : Nat) (hi : i < 80) :
    Crypto.Ripemd160.r[i]! < 16 := by
  interval_cases i <;> decide

private theorem rightSelector_lt (i : Nat) (hi : i < 80) :
    Crypto.Ripemd160.rP[i]! < 16 := by
  interval_cases i <;> decide

set_option linter.unusedSimpArgs false in
theorem leftRoundState_working_update (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    workingAt (leftRoundState s messageOffset returnDest rest i) 192 =
      RoundTrace.roundResult (workingAt s 192) (roundIndex i)
        (RoundTrace.roundWord
          (leftSecondReturned s messageOffset returnDest rest i)
          (UInt256.ofNat 192)
          (TableTrace.tableValue
            (leftFirstReturned s messageOffset returnDest rest i)
            (UInt256.ofNat 1184) (UInt256.ofNat i)))
        (TableTrace.tableValue s (UInt256.ofNat 1376)
          (UInt256.ofNat i)).toNat
        (constantAt s 1568 i) := by
  simpa [leftRoundState, leftSecondReturned, leftFirstReturned,
    afterConstantLoad, TableTrace.tableAtReturned, workingAt, wordAt,
    RoundTrace.workingAtNat] using
      RoundTrace.roundReturned_workingAtNat
        (leftSecondReturned s messageOffset returnDest rest i) 192
        (by norm_num) (roundIndex i)
        (TableTrace.tableValue
          (leftFirstReturned s messageOffset returnDest rest i)
          (UInt256.ofNat 1184) (UInt256.ofNat i))
        (TableTrace.tableValue s (UInt256.ofNat 1376) (UInt256.ofNat i))
        (constantAt s 1568 i) (UInt256.ofNat 714)
        (UInt256.ofNat (roundIndex i) :: UInt256.ofNat i ::
          messageOffset :: returnDest :: rest)

theorem rightRoundState_working_update (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    workingAt (rightRoundState s messageOffset returnDest rest i) 352 =
      RoundTrace.roundResult (workingAt s 352) (rightRoundIndex i)
        (RoundTrace.roundWord
          (rightSecondReturned s messageOffset returnDest rest i)
          (UInt256.ofNat 352)
          (TableTrace.tableValue
            (rightFirstReturned s messageOffset returnDest rest i)
            (UInt256.ofNat 1280) (UInt256.ofNat i)))
        (TableTrace.tableValue s (UInt256.ofNat 1472)
          (UInt256.ofNat i)).toNat
        (constantAt s 1728 i) := by
  simpa [rightRoundState, rightSecondReturned, rightFirstReturned,
    afterConstantLoad, TableTrace.tableAtReturned, workingAt, wordAt,
    RoundTrace.workingAtNat] using
      RoundTrace.roundReturned_workingAtNat
        (rightSecondReturned s messageOffset returnDest rest i) 352
        (by norm_num) (rightRoundIndex i)
        (TableTrace.tableValue
          (rightFirstReturned s messageOffset returnDest rest i)
          (UInt256.ofNat 1280) (UInt256.ofNat i))
        (TableTrace.tableValue s (UInt256.ofNat 1472) (UInt256.ofNat i))
        (constantAt s 1728 i) (UInt256.ofNat 792)
        (UInt256.ofNat (roundIndex i) :: UInt256.ofNat i ::
          messageOffset :: returnDest :: rest)

theorem leftRoundState_word_outside (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i address : Nat)
    (houtside : address + 32 ≤ 192 ∨ 352 ≤ address) :
    wordAt (leftRoundState s messageOffset returnDest rest i) address =
      wordAt s address := by
  simpa [leftRoundState, leftSecondReturned, leftFirstReturned,
    afterConstantLoad, TableTrace.tableAtReturned, wordAt] using
      RoundTrace.roundReturned_word_outside
        (leftSecondReturned s messageOffset returnDest rest i) 192 address
        (by norm_num) houtside (roundIndex i)
        (TableTrace.tableValue
          (leftFirstReturned s messageOffset returnDest rest i)
          (UInt256.ofNat 1184) (UInt256.ofNat i))
        (TableTrace.tableValue s (UInt256.ofNat 1376) (UInt256.ofNat i))
        (constantAt s 1568 i) (UInt256.ofNat 714)
        (UInt256.ofNat (roundIndex i) :: UInt256.ofNat i ::
          messageOffset :: returnDest :: rest)

theorem rightRoundState_word_outside (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (i address : Nat)
    (houtside : address + 32 ≤ 352 ∨ 512 ≤ address) :
    wordAt (rightRoundState s messageOffset returnDest rest i) address =
      wordAt s address := by
  simpa [rightRoundState, rightSecondReturned, rightFirstReturned,
    afterConstantLoad, TableTrace.tableAtReturned, wordAt] using
      RoundTrace.roundReturned_word_outside
        (rightSecondReturned s messageOffset returnDest rest i) 352 address
        (by norm_num) houtside (rightRoundIndex i)
        (TableTrace.tableValue
          (rightFirstReturned s messageOffset returnDest rest i)
          (UInt256.ofNat 1280) (UInt256.ofNat i))
        (TableTrace.tableValue s (UInt256.ofNat 1472) (UInt256.ofNat i))
        (constantAt s 1728 i) (UInt256.ofNat 792)
        (UInt256.ofNat (roundIndex i) :: UInt256.ofNat i ::
          messageOffset :: returnDest :: rest)

theorem leftStates_word_outside (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (n address : Nat) (houtside : address + 32 ≤ 192 ∨ 352 ≤ address) :
    wordAt (leftStates s messageOffset returnDest rest n) address =
      wordAt s address := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [leftStates_succ, leftRoundState_word_outside _ _ _ _ _ _ houtside,
        ih]

theorem rightStates_word_outside (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (n address : Nat) (houtside : address + 32 ≤ 352 ∨ 512 ≤ address) :
    wordAt (rightStates s messageOffset returnDest rest n) address =
      wordAt s address := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [rightStates_succ, rightRoundState_word_outside _ _ _ _ _ _ houtside,
        ih]

private theorem leftStates_tableByte (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (n base i : Nat) (hbase : 352 ≤ base) :
    InitializationCorrect.tableByte
        (leftStates s messageOffset returnDest rest n).memory base i =
      InitializationCorrect.tableByte s.memory base i := by
  unfold InitializationCorrect.tableByte
  change UInt256.byteAt (UInt256.ofNat (i % 32))
      (wordAt (leftStates s messageOffset returnDest rest n)
        (base + 32 * (i / 32))) = _
  rw [leftStates_word_outside _ _ _ _ _ _ (Or.inr (by omega))]
  rfl

private theorem rightStates_tableByte (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (n base i : Nat) (hbase : 512 ≤ base) :
    InitializationCorrect.tableByte
        (rightStates s messageOffset returnDest rest n).memory base i =
      InitializationCorrect.tableByte s.memory base i := by
  unfold InitializationCorrect.tableByte
  change UInt256.byteAt (UInt256.ofNat (i % 32))
      (wordAt (rightStates s messageOffset returnDest rest n)
        (base + 32 * (i / 32))) = _
  rw [rightStates_word_outside _ _ _ _ _ _ (Or.inr (by omega))]
  rfl

private theorem leftStates_xValue (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (n k : Nat) (hk : k < 16) :
    ScheduleCorrect.xValue (leftStates s messageOffset returnDest rest n) k =
      ScheduleCorrect.xValue s k := by
  unfold ScheduleCorrect.xValue
  change wordAt (leftStates s messageOffset returnDest rest n)
      (Schedule.xSlotWord k).toNat = _
  rw [leftStates_word_outside _ _ _ _ _ _ (Or.inr (by
    rw [ScheduleCorrect.xSlotWord_toNat k hk]
    omega))]
  rfl

private theorem rightStates_xValue (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (n k : Nat) (hk : k < 16) :
    ScheduleCorrect.xValue (rightStates s messageOffset returnDest rest n) k =
      ScheduleCorrect.xValue s k := by
  unfold ScheduleCorrect.xValue
  change wordAt (rightStates s messageOffset returnDest rest n)
      (Schedule.xSlotWord k).toNat = _
  rw [rightStates_word_outside _ _ _ _ _ _ (Or.inr (by
    rw [ScheduleCorrect.xSlotWord_toNat k hk]
    omega))]
  rfl

/-- `roundResult_embed` turns the exact left-round memory update into the
pure `evmLeftStep` transition once the three initialized lookup values are
identified. -/
theorem left_step_of_roundResult (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (word : Nat → UInt32) (i : Nat) (hi : i < 80)
    (x : Compression.Working)
    (hworking : workingAt s 192 = Compression.embed x)
    (hword : RoundTrace.roundWord
      (leftSecondReturned s messageOffset returnDest rest i)
      (UInt256.ofNat 192)
      (TableTrace.tableValue
        (leftFirstReturned s messageOffset returnDest rest i)
        (UInt256.ofNat 1184) (UInt256.ofNat i)) =
        Challenge.EvmProof.Word.ofUInt32
          (word (Crypto.Ripemd160.r[i]!)))
    (hrotation : (TableTrace.tableValue s (UInt256.ofNat 1376)
      (UInt256.ofNat i)).toNat = Crypto.Ripemd160.s[i]!)
    (hconstant : constantAt s 1568 i =
      Challenge.EvmProof.Word.ofUInt32
        (Crypto.Ripemd160.K[roundIndex i]!))
    (hmemory : workingAt
      (leftRoundState s messageOffset returnDest rest i) 192 =
      RoundTrace.roundResult (workingAt s 192) (roundIndex i)
        (RoundTrace.roundWord
          (leftSecondReturned s messageOffset returnDest rest i)
          (UInt256.ofNat 192)
          (TableTrace.tableValue
            (leftFirstReturned s messageOffset returnDest rest i)
            (UInt256.ofNat 1184) (UInt256.ofNat i)))
        (TableTrace.tableValue s (UInt256.ofNat 1376)
          (UInt256.ofNat i)).toNat
        (constantAt s 1568 i)) :
    workingAt (leftRoundState s messageOffset returnDest rest i) 192 =
      CompressionCorrect.evmLeftStep word i (workingAt s 192) := by
  rw [hmemory, hworking, hword, hrotation, hconstant]
  unfold CompressionCorrect.evmLeftStep
  change RoundTrace.roundResult (Compression.embed x) (roundIndex i)
      (Challenge.EvmProof.Word.ofUInt32
        (word (Crypto.Ripemd160.r[i]!)))
      (Crypto.Ripemd160.s[i]!)
      (Challenge.EvmProof.Word.ofUInt32
        (Crypto.Ripemd160.K[roundIndex i]!)) =
    Compression.evmRound (Compression.embed x) (roundIndex i)
      (Challenge.EvmProof.Word.ofUInt32
        (word (Crypto.Ripemd160.r[i]!)))
      (Crypto.Ripemd160.s[i]!)
      (Challenge.EvmProof.Word.ofUInt32
        (Crypto.Ripemd160.K[roundIndex i]!))
  rw [Compression.evmRound_embed x (roundIndex i)
    (word (Crypto.Ripemd160.r[i]!))
    (Crypto.Ripemd160.K[roundIndex i]!) (Crypto.Ripemd160.s[i]!)
    (by unfold roundIndex; omega) (leftRotation_pos i hi)
    (leftRotation_lt i hi)]
  exact RoundTrace.roundResult_embed x (roundIndex i)
    (word (Crypto.Ripemd160.r[i]!))
    (Crypto.Ripemd160.K[roundIndex i]!) (Crypto.Ripemd160.s[i]!)
    (by unfold roundIndex; omega) (leftRotation_pos i hi)
    (leftRotation_lt i hi)

/-- Right-line counterpart of `left_step_of_roundResult`. -/
theorem right_step_of_roundResult (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (word : Nat → UInt32) (i : Nat) (hi : i < 80)
    (x : Compression.Working)
    (hworking : workingAt s 352 = Compression.embed x)
    (hword : RoundTrace.roundWord
      (rightSecondReturned s messageOffset returnDest rest i)
      (UInt256.ofNat 352)
      (TableTrace.tableValue
        (rightFirstReturned s messageOffset returnDest rest i)
        (UInt256.ofNat 1280) (UInt256.ofNat i)) =
        Challenge.EvmProof.Word.ofUInt32
          (word (Crypto.Ripemd160.rP[i]!)))
    (hrotation : (TableTrace.tableValue s (UInt256.ofNat 1472)
      (UInt256.ofNat i)).toNat = Crypto.Ripemd160.sP[i]!)
    (hconstant : constantAt s 1728 i =
      Challenge.EvmProof.Word.ofUInt32
        (Crypto.Ripemd160.KP[roundIndex i]!))
    (hmemory : workingAt
      (rightRoundState s messageOffset returnDest rest i) 352 =
      RoundTrace.roundResult (workingAt s 352)
        (rightRoundIndex i)
        (RoundTrace.roundWord
          (rightSecondReturned s messageOffset returnDest rest i)
          (UInt256.ofNat 352)
          (TableTrace.tableValue
            (rightFirstReturned s messageOffset returnDest rest i)
            (UInt256.ofNat 1280) (UInt256.ofNat i)))
        (TableTrace.tableValue s (UInt256.ofNat 1472)
          (UInt256.ofNat i)).toNat
        (constantAt s 1728 i)) :
    workingAt (rightRoundState s messageOffset returnDest rest i) 352 =
      CompressionCorrect.evmRightStep word i (workingAt s 352) := by
  rw [hmemory, hworking, hword, hrotation, hconstant]
  unfold CompressionCorrect.evmRightStep rightRoundIndex
  change RoundTrace.roundResult (Compression.embed x) (4 - roundIndex i)
      (Challenge.EvmProof.Word.ofUInt32
        (word (Crypto.Ripemd160.rP[i]!)))
      (Crypto.Ripemd160.sP[i]!)
      (Challenge.EvmProof.Word.ofUInt32
        (Crypto.Ripemd160.KP[roundIndex i]!)) =
    Compression.evmRound (Compression.embed x) (4 - roundIndex i)
      (Challenge.EvmProof.Word.ofUInt32
        (word (Crypto.Ripemd160.rP[i]!)))
      (Crypto.Ripemd160.sP[i]!)
      (Challenge.EvmProof.Word.ofUInt32
        (Crypto.Ripemd160.KP[roundIndex i]!))
  rw [Compression.evmRound_embed x (4 - roundIndex i)
    (word (Crypto.Ripemd160.rP[i]!))
    (Crypto.Ripemd160.KP[roundIndex i]!) (Crypto.Ripemd160.sP[i]!)
    (by unfold roundIndex; omega) (rightRotation_pos i hi)
    (rightRotation_lt i hi)]
  exact RoundTrace.roundResult_embed x (4 - roundIndex i)
    (word (Crypto.Ripemd160.rP[i]!))
    (Crypto.Ripemd160.KP[roundIndex i]!) (Crypto.Ripemd160.sP[i]!)
    (by unfold roundIndex; omega) (rightRotation_pos i hi)
    (rightRotation_lt i hi)

/-- Induction principle pairing the concrete left-state fold with the pure
EVM-word round fold.  The step premise is a single uniform refinement fact,
not eighty unrelated hypotheses. -/
theorem leftStates_tracks (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (word : Nat → UInt32)
    (initial : Compression.EvmWorking)
    (hinitial : workingAt s 192 = initial)
    (hstep : ∀ i, i < 80 →
      workingAt
        (leftRoundState
          (leftStates s messageOffset returnDest rest i)
          messageOffset returnDest rest i) 192 =
        CompressionCorrect.evmLeftStep word i
          (workingAt (leftStates s messageOffset returnDest rest i) 192)) :
    ∀ n, n ≤ 80 →
      workingAt (leftStates s messageOffset returnDest rest n) 192 =
        CompressionCorrect.evmLeftRounds word n initial := by
  intro n hn
  induction n with
  | zero => simpa [CompressionCorrect.evmLeftRounds] using hinitial
  | succ n ih =>
      rw [leftStates_succ, hstep n (by omega), ih (by omega)]
      rfl

/-- Right-line counterpart of `leftStates_tracks`. -/
theorem rightStates_tracks (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (word : Nat → UInt32)
    (initial : Compression.EvmWorking)
    (hinitial : workingAt s 352 = initial)
    (hstep : ∀ i, i < 80 →
      workingAt
        (rightRoundState
          (rightStates s messageOffset returnDest rest i)
          messageOffset returnDest rest i) 352 =
        CompressionCorrect.evmRightStep word i
          (workingAt (rightStates s messageOffset returnDest rest i) 352)) :
    ∀ n, n ≤ 80 →
      workingAt (rightStates s messageOffset returnDest rest n) 352 =
        CompressionCorrect.evmRightRounds word n initial := by
  intro n hn
  induction n with
  | zero => simpa [CompressionCorrect.evmRightRounds] using hinitial
  | succ n ih =>
      rw [rightStates_succ, hstep n (by omega), ih (by omega)]
      rfl

theorem leftStates_concrete (inputs :
    BlockInputs s messageOffset padded blockOff h) :
    ∀ n, n ≤ 80 →
      workingAt
          (leftStates (leftInitialState s messageOffset returnDest rest)
            messageOffset returnDest rest n) 192 =
        CompressionCorrect.evmLeftRounds (blockWords padded blockOff) n
          (CompressionCorrect.evmWorkingOfHash (Compression.embedHash h)) := by
  intro n hn
  induction n with
  | zero =>
      simpa [CompressionCorrect.evmLeftRounds] using
        (leftInitialState_working (returnDest := returnDest)
          (rest := rest) inputs)
  | succ i ih =>
      let q := leftStates (leftInitialState s messageOffset returnDest rest)
        messageOffset returnDest rest i
      have hi : i < 80 := by omega
      have htables := leftInitialState_tables (returnDest := returnDest)
        (rest := rest) inputs
      have hconstants := leftInitialState_constants (returnDest := returnDest)
        (rest := rest) inputs
      have hselector : TableTrace.tableValue
          (leftFirstReturned q messageOffset returnDest rest i)
          (UInt256.ofNat 1184) (UInt256.ofNat i) =
            UInt256.ofNat (Crypto.Ripemd160.r[i]!) := by
        rw [TableTrace.tableValue_tableByte _ 1184 i (by omega) (by omega) hi]
        change InitializationCorrect.tableByte q.memory 1184 i = _
        rw [leftStates_tableByte _ _ _ _ i 1184 i (by omega)]
        exact htables.1 i hi
      have hword : RoundTrace.roundWord
          (leftSecondReturned q messageOffset returnDest rest i)
          (UInt256.ofNat 192)
          (TableTrace.tableValue
            (leftFirstReturned q messageOffset returnDest rest i)
            (UInt256.ofNat 1184) (UInt256.ofNat i)) =
            Challenge.EvmProof.Word.ofUInt32
              (blockWords padded blockOff (Crypto.Ripemd160.r[i]!)) := by
        rw [hselector]
        calc
          RoundTrace.roundWord
              (leftSecondReturned q messageOffset returnDest rest i)
              (UInt256.ofNat 192)
              (UInt256.ofNat (Crypto.Ripemd160.r[i]!)) =
            ScheduleCorrect.xValue q (Crypto.Ripemd160.r[i]!) := by
              change TableTrace.loadedWord q (UInt256.ofNat 672)
                (UInt256.ofNat (Crypto.Ripemd160.r[i]!)) = _
              exact TableTrace.loadedWord_xValue q
                (Crypto.Ripemd160.r[i]!) (leftSelector_lt i hi)
          _ = _ := by
            rw [leftStates_xValue _ _ _ _ i _ (leftSelector_lt i hi)]
            have hb := blockWords_eq_readLE32 padded blockOff
              (Crypto.Ripemd160.r[i]!) (leftSelector_lt i hi)
            rw [hb]
            exact leftInitialState_words_crypto (returnDest := returnDest)
              (rest := rest) inputs _ (leftSelector_lt i hi)
      have hrotationWord : TableTrace.tableValue q (UInt256.ofNat 1376)
          (UInt256.ofNat i) = UInt256.ofNat (Crypto.Ripemd160.s[i]!) := by
        rw [TableTrace.tableValue_tableByte _ 1376 i (by omega) (by omega) hi]
        rw [leftStates_tableByte _ _ _ _ i 1376 i (by omega)]
        exact htables.2.2.1 i hi
      have hrotation : (TableTrace.tableValue q (UInt256.ofNat 1376)
          (UInt256.ofNat i)).toNat = Crypto.Ripemd160.s[i]! := by
        rw [hrotationWord, Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt (by
            have := leftRotation_lt i hi
            omega)]
      have hconstant : constantAt q 1568 i =
          Challenge.EvmProof.Word.ofUInt32
            (Crypto.Ripemd160.K[roundIndex i]!) := by
        unfold constantAt
        change wordAt q (1568 + roundIndex i * 32) = _
        rw [leftStates_word_outside _ _ _ _ i _ (Or.inr (by omega))]
        simpa [wordAt, InitializationCorrect.slotWord, Nat.mul_comm] using
          hconstants.1 (roundIndex i) (by unfold roundIndex; omega)
      have hworking : workingAt q 192 = Compression.embed
          (CompressionCorrect.leftRounds (blockWords padded blockOff) i
            (CompressionCorrect.workingOfHash h)) := by
        rw [ih (by omega)]
        exact CompressionCorrect.evmLeftRounds_embed
          (blockWords padded blockOff) i (CompressionCorrect.workingOfHash h)
          (by omega)
      rw [leftStates_succ]
      rw [left_step_of_roundResult q messageOffset returnDest rest
        (blockWords padded blockOff) i hi
        (CompressionCorrect.leftRounds (blockWords padded blockOff) i
          (CompressionCorrect.workingOfHash h)) hworking hword hrotation
        hconstant (leftRoundState_working_update q messageOffset returnDest rest i)]
      rw [ih (by omega)]
      rfl

theorem leftFinalState_rightWorking (inputs :
    BlockInputs s messageOffset padded blockOff h) :
    workingAt (rightInitialState s messageOffset returnDest rest) 352 =
      CompressionCorrect.evmWorkingOfHash (Compression.embedHash h) := by
  unfold rightInitialState leftFinalState workingAt
  rw [leftStates_word_outside _ _ _ _ 80 352 (Or.inr (by omega)),
    leftStates_word_outside _ _ _ _ 80 384 (Or.inr (by omega)),
    leftStates_word_outside _ _ _ _ 80 416 (Or.inr (by omega)),
    leftStates_word_outside _ _ _ _ 80 448 (Or.inr (by omega)),
    leftStates_word_outside _ _ _ _ 80 480 (Or.inr (by omega))]
  exact leftInitialState_rightWorking (returnDest := returnDest)
    (rest := rest) inputs

theorem rightStates_concrete (inputs :
    BlockInputs s messageOffset padded blockOff h) :
    ∀ n, n ≤ 80 →
      workingAt
          (rightStates (rightInitialState s messageOffset returnDest rest)
            messageOffset returnDest rest n) 352 =
        CompressionCorrect.evmRightRounds (blockWords padded blockOff) n
          (CompressionCorrect.evmWorkingOfHash (Compression.embedHash h)) := by
  intro n hn
  induction n with
  | zero =>
      simpa [CompressionCorrect.evmRightRounds] using
        (leftFinalState_rightWorking (returnDest := returnDest)
          (rest := rest) inputs)
  | succ i ih =>
      let q := rightStates (rightInitialState s messageOffset returnDest rest)
        messageOffset returnDest rest i
      have hi : i < 80 := by omega
      have htables := leftInitialState_tables (returnDest := returnDest)
        (rest := rest) inputs
      have hconstants := leftInitialState_constants (returnDest := returnDest)
        (rest := rest) inputs
      have hselector : TableTrace.tableValue
          (rightFirstReturned q messageOffset returnDest rest i)
          (UInt256.ofNat 1280) (UInt256.ofNat i) =
            UInt256.ofNat (Crypto.Ripemd160.rP[i]!) := by
        rw [TableTrace.tableValue_tableByte _ 1280 i (by omega) (by omega) hi]
        change InitializationCorrect.tableByte q.memory 1280 i = _
        rw [rightStates_tableByte _ _ _ _ i 1280 i (by omega)]
        unfold rightInitialState leftFinalState
        rw [leftStates_tableByte _ _ _ _ 80 1280 i (by omega)]
        exact htables.2.1 i hi
      have hword : RoundTrace.roundWord
          (rightSecondReturned q messageOffset returnDest rest i)
          (UInt256.ofNat 352)
          (TableTrace.tableValue
            (rightFirstReturned q messageOffset returnDest rest i)
            (UInt256.ofNat 1280) (UInt256.ofNat i)) =
            Challenge.EvmProof.Word.ofUInt32
              (blockWords padded blockOff (Crypto.Ripemd160.rP[i]!)) := by
        rw [hselector]
        calc
          RoundTrace.roundWord
              (rightSecondReturned q messageOffset returnDest rest i)
              (UInt256.ofNat 352)
              (UInt256.ofNat (Crypto.Ripemd160.rP[i]!)) =
            ScheduleCorrect.xValue q (Crypto.Ripemd160.rP[i]!) := by
              change TableTrace.loadedWord q (UInt256.ofNat 672)
                (UInt256.ofNat (Crypto.Ripemd160.rP[i]!)) = _
              exact TableTrace.loadedWord_xValue q
                (Crypto.Ripemd160.rP[i]!) (rightSelector_lt i hi)
          _ = _ := by
            rw [rightStates_xValue _ _ _ _ i _ (rightSelector_lt i hi)]
            unfold rightInitialState leftFinalState
            rw [leftStates_xValue _ _ _ _ 80 _ (rightSelector_lt i hi)]
            have hb := blockWords_eq_readLE32 padded blockOff
              (Crypto.Ripemd160.rP[i]!) (rightSelector_lt i hi)
            rw [hb]
            exact leftInitialState_words_crypto (returnDest := returnDest)
              (rest := rest) inputs _ (rightSelector_lt i hi)
      have hrotationWord : TableTrace.tableValue q (UInt256.ofNat 1472)
          (UInt256.ofNat i) = UInt256.ofNat (Crypto.Ripemd160.sP[i]!) := by
        rw [TableTrace.tableValue_tableByte _ 1472 i (by omega) (by omega) hi]
        rw [rightStates_tableByte _ _ _ _ i 1472 i (by omega)]
        unfold rightInitialState leftFinalState
        rw [leftStates_tableByte _ _ _ _ 80 1472 i (by omega)]
        exact htables.2.2.2 i hi
      have hrotation : (TableTrace.tableValue q (UInt256.ofNat 1472)
          (UInt256.ofNat i)).toNat = Crypto.Ripemd160.sP[i]! := by
        rw [hrotationWord, Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt (by
            have := rightRotation_lt i hi
            omega)]
      have hconstant : constantAt q 1728 i =
          Challenge.EvmProof.Word.ofUInt32
            (Crypto.Ripemd160.KP[roundIndex i]!) := by
        unfold constantAt
        change wordAt q (1728 + roundIndex i * 32) = _
        rw [rightStates_word_outside _ _ _ _ i _ (Or.inr (by omega))]
        unfold rightInitialState leftFinalState
        rw [leftStates_word_outside _ _ _ _ 80 _ (Or.inr (by omega))]
        simpa [wordAt, InitializationCorrect.slotWord, Nat.mul_comm] using
          hconstants.2 (roundIndex i) (by unfold roundIndex; omega)
      have hworking : workingAt q 352 = Compression.embed
          (CompressionCorrect.rightRounds (blockWords padded blockOff) i
            (CompressionCorrect.workingOfHash h)) := by
        rw [ih (by omega)]
        exact CompressionCorrect.evmRightRounds_embed
          (blockWords padded blockOff) i (CompressionCorrect.workingOfHash h)
          (by omega)
      rw [rightStates_succ]
      rw [right_step_of_roundResult q messageOffset returnDest rest
        (blockWords padded blockOff) i hi
        (CompressionCorrect.rightRounds (blockWords padded blockOff) i
          (CompressionCorrect.workingOfHash h)) hworking hword hrotation
        hconstant (rightRoundState_working_update q messageOffset returnDest rest i)]
      rw [ih (by omega)]
      rfl

theorem rightFinalState_saved (inputs :
    BlockInputs s messageOffset padded blockOff h) :
    savedHashAt512 (rightFinalState s messageOffset returnDest rest) =
      Compression.embedHash h := by
  unfold rightFinalState rightInitialState leftFinalState savedHashAt512
  rw [rightStates_word_outside _ _ _ _ 80 512 (Or.inr (by omega)),
    rightStates_word_outside _ _ _ _ 80 544 (Or.inr (by omega)),
    rightStates_word_outside _ _ _ _ 80 576 (Or.inr (by omega)),
    rightStates_word_outside _ _ _ _ 80 608 (Or.inr (by omega)),
    rightStates_word_outside _ _ _ _ 80 640 (Or.inr (by omega)),
    leftStates_word_outside _ _ _ _ 80 512 (Or.inr (by omega)),
    leftStates_word_outside _ _ _ _ 80 544 (Or.inr (by omega)),
    leftStates_word_outside _ _ _ _ 80 576 (Or.inr (by omega)),
    leftStates_word_outside _ _ _ _ 80 608 (Or.inr (by omega)),
    leftStates_word_outside _ _ _ _ 80 640 (Or.inr (by omega))]
  exact leftInitialState_saved (returnDest := returnDest) (rest := rest) inputs

theorem rightFinalState_leftPreserved :
    workingAt (rightFinalState s messageOffset returnDest rest) 192 =
      workingAt (leftFinalState s messageOffset returnDest rest) 192 := by
  unfold rightFinalState rightInitialState workingAt
  rw [rightStates_word_outside _ _ _ _ 80 192 (Or.inl (by omega)),
    rightStates_word_outside _ _ _ _ 80 224 (Or.inl (by omega)),
    rightStates_word_outside _ _ _ _ 80 256 (Or.inl (by omega)),
    rightStates_word_outside _ _ _ _ 80 288 (Or.inl (by omega)),
    rightStates_word_outside _ _ _ _ 80 320 (Or.inl (by omega))]

/-- A compact functional certificate for one concrete compressor invocation.
The two step fields are uniform theorems over the executable folds. -/
structure BlockRefinement (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (padded : ByteArray) (blockOff : Nat)
    (h : Compression.HashState) where
  leftInitial : workingAt (leftInitialState s messageOffset returnDest rest) 192 =
    CompressionCorrect.evmWorkingOfHash (Compression.embedHash h)
  rightInitial : workingAt (rightInitialState s messageOffset returnDest rest) 352 =
    CompressionCorrect.evmWorkingOfHash (Compression.embedHash h)
  savedFinal : savedHashAt512
    (rightFinalState s messageOffset returnDest rest) = Compression.embedHash h
  leftPreserved : workingAt
    (rightFinalState s messageOffset returnDest rest) 192 =
      workingAt (leftFinalState s messageOffset returnDest rest) 192
  leftStep : ∀ i, i < 80 →
    workingAt
      (leftRoundState
        (leftStates (leftInitialState s messageOffset returnDest rest)
          messageOffset returnDest rest i)
        messageOffset returnDest rest i) 192 =
      CompressionCorrect.evmLeftStep (blockWords padded blockOff) i
        (workingAt
          (leftStates (leftInitialState s messageOffset returnDest rest)
            messageOffset returnDest rest i) 192)
  rightStep : ∀ i, i < 80 →
    workingAt
      (rightRoundState
        (rightStates (rightInitialState s messageOffset returnDest rest)
          messageOffset returnDest rest i)
        messageOffset returnDest rest i) 352 =
      CompressionCorrect.evmRightStep (blockWords padded blockOff) i
        (workingAt
          (rightStates (rightInitialState s messageOffset returnDest rest)
            messageOffset returnDest rest i) 352)

theorem blockRefinement_of_inputs (inputs :
    BlockInputs s messageOffset padded blockOff h) :
    BlockRefinement s messageOffset returnDest rest padded blockOff h where
  leftInitial := leftInitialState_working (returnDest := returnDest)
    (rest := rest) inputs
  rightInitial := leftFinalState_rightWorking (returnDest := returnDest)
    (rest := rest) inputs
  savedFinal := rightFinalState_saved (returnDest := returnDest)
    (rest := rest) inputs
  leftPreserved := rightFinalState_leftPreserved
  leftStep := by
    intro i hi
    have hnext := leftStates_concrete (returnDest := returnDest)
      (rest := rest) inputs (i + 1) (by omega)
    have hcurrent := leftStates_concrete (returnDest := returnDest)
      (rest := rest) inputs i (by omega)
    rw [leftStates_succ] at hnext
    simpa [CompressionCorrect.evmLeftRounds, hcurrent] using hnext
  rightStep := by
    intro i hi
    have hnext := rightStates_concrete (returnDest := returnDest)
      (rest := rest) inputs (i + 1) (by omega)
    have hcurrent := rightStates_concrete (returnDest := returnDest)
      (rest := rest) inputs i (by omega)
    rw [rightStates_succ] at hnext
    simpa [CompressionCorrect.evmRightRounds, hcurrent] using hnext

theorem BlockRefinement.leftFinal
    (ref : BlockRefinement s messageOffset returnDest rest padded blockOff h) :
    workingAt (leftFinalState s messageOffset returnDest rest) 192 =
      CompressionCorrect.evmLeftRounds (blockWords padded blockOff) 80
        (CompressionCorrect.evmWorkingOfHash (Compression.embedHash h)) := by
  simpa [leftFinalState] using
    leftStates_tracks (leftInitialState s messageOffset returnDest rest)
      messageOffset returnDest rest (blockWords padded blockOff)
      (CompressionCorrect.evmWorkingOfHash (Compression.embedHash h))
      ref.leftInitial ref.leftStep 80 (by omega)

theorem BlockRefinement.rightFinal
    (ref : BlockRefinement s messageOffset returnDest rest padded blockOff h) :
    workingAt (rightFinalState s messageOffset returnDest rest) 352 =
      CompressionCorrect.evmRightRounds (blockWords padded blockOff) 80
        (CompressionCorrect.evmWorkingOfHash (Compression.embedHash h)) := by
  simpa [rightFinalState] using
    rightStates_tracks (rightInitialState s messageOffset returnDest rest)
      messageOffset returnDest rest (blockWords padded blockOff)
      (CompressionCorrect.evmWorkingOfHash (Compression.embedHash h))
      ref.rightInitial ref.rightStep 80 (by omega)

/-- The concrete tail contains the pure compression-model result. -/
theorem tail_hash_eq_compressModel
    (ref : BlockRefinement s messageOffset returnDest rest padded blockOff h) :
    hashAt32
      (rightTailResult (rightInitialState s messageOffset returnDest rest)
        messageOffset returnDest rest) =
      Compression.embedHash
        (CompressionCorrect.compressModel (blockWords padded blockOff) h) := by
  apply rightTailResult_hash_correct
  · exact ref.savedFinal
  · change workingAt (rightFinalState s messageOffset returnDest rest) 192 = _
    rw [ref.leftPreserved, ref.leftFinal]
    exact CompressionCorrect.evmLeftRounds_embed
      (blockWords padded blockOff) 80 (CompressionCorrect.workingOfHash h)
      (by omega)
  · change workingAt (rightFinalState s messageOffset returnDest rest) 352 = _
    rw [ref.rightFinal]
    exact CompressionCorrect.evmRightRounds_embed
      (blockWords padded blockOff) 80 (CompressionCorrect.workingOfHash h)
      (by omega)

/-- Array-level statement identifying the preceding model with Ethereum's
pinned `compressBlock` implementation. -/
theorem compressModel_hashArray_eq_compressBlock
    (padded : ByteArray) (blockOff : Nat) (h : Compression.HashState) :
    CompressionCorrect.hashArray
        (CompressionCorrect.compressModel (blockWords padded blockOff) h) =
      Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
        padded blockOff := by
  exact CompressionCorrect.compressModel_eq_compressBlock padded blockOff h

/-- End-to-end functional statement for one compressor call.  Its only
premise is the raw incoming-memory contract; the round refinement certificate
is constructed internally. -/
theorem tail_hash_eq_compressBlock_of_inputs (inputs :
    BlockInputs s messageOffset padded blockOff h) :
    hashAt32
        (rightTailResult (rightInitialState s messageOffset returnDest rest)
          messageOffset returnDest rest) =
      embedHashArray
        (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
          padded blockOff) := by
  rw [tail_hash_eq_compressModel
    (blockRefinement_of_inputs (returnDest := returnDest) (rest := rest) inputs)]
  rw [← embedHashArray_hashArray,
    compressModel_hashArray_eq_compressBlock]

/-- A complete compressor invocation only mutates memory below the packed
lookup-table region.  This is the frame property used to carry tables,
constants, and the padded message across driver iterations. -/
theorem compressorResult_word_above (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (address : Nat) (haddress : 0x4a0 ≤ address) :
    wordAt
        (rightTailResult (leftFinalState s messageOffset returnDest rest)
          messageOffset returnDest rest) address =
      wordAt s address := by
  unfold wordAt rightTailResult combinationReturned combinationCleaned
  simp only [combination4]
  unfold CompressionTailTrace.storeWordMemory
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · change wordAt
        (rightStates (leftFinalState s messageOffset returnDest rest)
          messageOffset returnDest rest 80) address = wordAt s address
    rw [rightStates_word_outside _ _ _ _ 80 address (Or.inr (by omega))]
    unfold leftFinalState
    rw [leftStates_word_outside _ _ _ _ 80 address (Or.inr (by omega))]
    exact leftInitialState_words s messageOffset returnDest rest address haddress
  all_goals
    simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    right
    omega

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionFunctionalTrace
