import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleTemplate
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-!
# H17 ascending packed-schedule evaluator traces

The theorems in this file are generic in the surrounding EVM state.  The raw
trace stops before the helper's final `JUMP` and uses only the executable
instruction evaluator from `StackRoundTrace`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

def afterInitial (s : State) (startPC messageOffset returnPC : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := pcAfter startPC initialTemplate
    stack := [inputWord0 s messageOffset, inputWord1 s messageOffset, returnPC] ++ rest
    activeWords := warmupActiveWords s messageOffset }

def afterHalf (s : State) (startPC : UInt256) (half : Nat)
    (value : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := pcAfter startPC (halfTemplate half)
    stack := rest
    memory := writePackedHalf s.memory half value
    activeWords := storeActiveWords s.activeWords (storeAddresses half) }

def stageState (s : State) (endPC value : UInt256) (shift : Nat)
    (mask : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := endPC
    stack := packedStage value shift mask :: rest }

def storeState (s : State) (endPC : UInt256) (half : Nat)
    (value : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := endPC
    stack := rest
    memory := writePackedHalf s.memory half value
    activeWords := storeActiveWords s.activeWords (storeAddresses half) }

def initialState (s : State) (startPC messageOffset returnPC : UInt256)
    (rest : List UInt256) : State :=
  afterInitial s startPC messageOffset returnPC rest

def finalState (s : State) (startPC messageOffset returnPC : UInt256)
    (rest : List UInt256) : State :=
  expectedState s startPC messageOffset returnPC rest

theorem pcAfter_append (pc : UInt256) (first second : List Instr) :
    pcAfter pc (first ++ second) = pcAfter (pcAfter pc first) second := by
  induction first generalizing pc with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.cons_append, pcAfter]
      exact ih (pc := pc + UInt256.ofNat instruction.size)

private theorem word_add_assoc (u v w : UInt256) :
    (u + v) + w = u + (v + w) := by
  apply word_ext
  change ((u.val + v.val) + w.val).val =
    (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

private theorem word_add_ofNat_assoc (u : UInt256) (a b : Nat) :
    (u + UInt256.ofNat a) + UInt256.ofNat b =
      u + UInt256.ofNat (a + b) := by
  rw [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem add_ofNat_assoc (u : UInt256) (a b : Nat) :
    UInt256.add (UInt256.add u (UInt256.ofNat a)) (UInt256.ofNat b) =
      UInt256.add u (UInt256.ofNat (a + b)) := by
  change (u + UInt256.ofNat a) + UInt256.ofNat b =
    u + UInt256.ofNat (a + b)
  exact word_add_ofNat_assoc u a b

private theorem add_ofNat_assoc_hAdd (u : UInt256) (a b : Nat) :
    (UInt256.add u (UInt256.ofNat a)) + UInt256.ofNat b =
      u + UInt256.ofNat (a + b) := by
  change (u + UInt256.ofNat a) + UInt256.ofNat b =
    u + UInt256.ofNat (a + b)
  exact word_add_ofNat_assoc u a b

private theorem add_ofNat_assoc_add (u : UInt256) (a b : Nat) :
    UInt256.add (u + UInt256.ofNat a) (UInt256.ofNat b) =
      u + UInt256.ofNat (a + b) := by
  change (u + UInt256.ofNat a) + UInt256.ofNat b =
    u + UInt256.ofNat (a + b)
  exact word_add_ofNat_assoc u a b

private theorem add_assoc_explicit (u v w : UInt256) :
    UInt256.add (UInt256.add u v) w =
      UInt256.add u (UInt256.add v w) := by
  change (u + v) + w = u + (v + w)
  exact word_add_assoc u v w

private theorem add_assoc_explicit_hAdd (u v w : UInt256) :
    (UInt256.add u v) + w = u + (v + w) := by
  change (u + v) + w = u + (v + w)
  exact word_add_assoc u v w

private theorem add_assoc_hAdd_explicit (u v w : UInt256) :
    UInt256.add (u + v) w = u + (v + w) := by
  change (u + v) + w = u + (v + w)
  exact word_add_assoc u v w

private theorem shiftRight_zero (u : UInt256) :
    UInt256.shiftRight u (UInt256.ofNat 0) = u := by
  apply word_ext
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by norm_num)]
  simp

private theorem pcAfter_eq_add (pc : UInt256) (instructions : List Instr) :
    pcAfter pc instructions =
      pc + UInt256.ofNat ((instructions.map Instr.size).sum) := by
  induction instructions generalizing pc with
  | nil =>
      change pc = pc + (0 : UInt256)
      exact (Word.add_zero pc).symm
  | cons instruction rest ih =>
      simp only [pcAfter, List.map_cons, List.sum_cons]
      rw [ih, word_add_ofNat_assoc]

theorem runInstrSeq_append_running
    {first second : List Instr} {s middle result : State}
    (hfirst : runInstrSeq first s = some middle)
    (hmiddle : middle.halt = .Running)
    (hsecond : runInstrSeq second middle = some result) :
    runInstrSeq (first ++ second) s = some result := by
  induction first generalizing s middle with
  | nil =>
      simp only [List.nil_append, runInstrSeq] at hfirst ⊢
      cases hfirst
      exact hsecond
  | cons instruction rest ih =>
      cases hrun : Challenge.EvmProof.Stepper.runInstr instruction s with
      | none =>
          simp [runInstrSeq, hrun] at hfirst
      | some next =>
          cases rest with
          | nil =>
              have hnext : next = middle := by
                simpa [runInstrSeq, hrun] using hfirst
              subst middle
              cases second with
              | nil =>
                  simpa [runInstrSeq, hrun] using hsecond
              | cons nextInstruction secondRest =>
                  simpa [runInstrSeq, hrun, hmiddle] using hsecond
          | cons nextInstruction restTail =>
              cases hhalt : next.halt with
              | Running =>
                  have htail :
                      runInstrSeq (nextInstruction :: restTail) next = some middle := by
                    simpa [runInstrSeq, hrun, hhalt] using hfirst
                  have hjoined := ih (s := next) (middle := middle)
                    htail hmiddle hsecond
                  simpa [runInstrSeq, hrun, hhalt] using hjoined
              | Success =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst
              | Returned =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst
              | Reverted =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst
              | Exception error =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst

@[simp] theorem afterInitial_halt
    (s : State) (startPC messageOffset returnPC : UInt256)
    (rest : List UInt256) :
    (afterInitial s startPC messageOffset returnPC rest).halt = s.halt := by
  rfl

@[simp] theorem afterHalf_halt
    (s : State) (startPC : UInt256) (half : Nat)
    (value : UInt256) (rest : List UInt256) :
    (afterHalf s startPC half value rest).halt = s.halt := by
  rfl

@[simp] theorem stageState_halt
    (s : State) (endPC value : UInt256) (shift : Nat)
    (mask : UInt256) (rest : List UInt256) :
    (stageState s endPC value shift mask rest).halt = s.halt := by
  rfl

@[simp] theorem storeState_halt
    (s : State) (endPC : UInt256) (half : Nat)
    (value : UInt256) (rest : List UInt256) :
    (storeState s endPC half value rest).halt = s.halt := by
  rfl

theorem runInstrSeq_endianStage
    (s : State) (startPC value : UInt256) (shift : Nat) (mask : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hrun : s.halt = .Running) :
    runInstrSeq (endianStage shift mask)
      { s with pc := startPC, stack := value :: rest } =
      some (stageState s
        (pcAfter startPC (endianStage shift mask)) value shift mask rest) := by
  have hcap (m : Nat) (hm : m ≤ 2) : rest.length + m < 1024 := by
    omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by
    omega
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by
    omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  simp (config := { maxSteps := 1000000 })
    [endianStage, op, push1, push32, dup1, swap1, packedStage,
      stageState, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      pcAfter, hrun, hcap, hcap2, hcap3, hswap1, UInt256.succ, Instr.size,
      Instr.size_push, Instr.size_op, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, word_add_assoc,
      word_add_ofNat_assoc, Word.land_comm,
      Word.lor_comm]
  rw [add_ofNat_assoc_hAdd startPC 1 2]
  repeat first
    | rw [add_ofNat_assoc_hAdd]
    | rw [add_ofNat_assoc_add]
    | rw [add_ofNat_assoc]
  simp only [add_assoc_explicit, add_assoc_explicit_hAdd,
    add_assoc_hAdd_explicit, word_add_assoc]
  simp [Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]

theorem runInstrSeq_initial
    (s : State) (startPC messageOffset returnPC : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1018)
    (hrun : s.halt = .Running) :
    runInstrSeq initialTemplate
      (scheduleEntry s startPC messageOffset returnPC rest) =
      some (afterInitial s startPC messageOffset returnPC rest) := by
  have hcap (m : Nat) (hm : m ≤ 4) : rest.length + m < 1024 := by
    omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by
    omega
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by
    omega
  have hcap4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by
    omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  have h60 : UInt256.ofNat 60 + messageOffset =
      messageOffset + UInt256.ofNat 60 :=
    word_add_comm _ _
  have h32 : UInt256.ofNat 32 + messageOffset =
      messageOffset + UInt256.ofNat 32 :=
    word_add_comm _ _
  simp (config := { maxSteps := 2000000 })
    [initialTemplate, scheduleEntry, afterInitial, inputWord0, inputWord1,
      warmupActiveWords, activeAfterWord, op, push1, dup1, swap1,
      runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, hrun, hcap,
      hcap2, hcap3, hcap4, hswap1, h60, h32, word_add_assoc,
      word_add_ofNat_assoc, Nat.add_assoc,
      Word.land_comm, Word.lor_comm, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, UInt256.succ, Instr.size,
      Instr.size_push, Instr.size_op]
  rw [add_ofNat_assoc startPC 1 1]
  repeat first
    | rw [add_ofNat_assoc_hAdd]
    | rw [add_ofNat_assoc_add]
    | rw [add_ofNat_assoc]
  simp only [add_assoc_explicit, add_assoc_explicit_hAdd,
    add_assoc_hAdd_explicit, word_add_assoc]
  simp [Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]

theorem runInstrSeq_store0
    (s : State) (startPC value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq (storeTemplate 0)
      { s with pc := startPC, stack := value :: rest } =
      some (storeState s
        (pcAfter startPC (storeTemplate 0)) 0 value rest) := by
  have hcap (m : Nat) (hm : m ≤ 2) : rest.length + m < 1024 := by
    omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by
    omega
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by
    omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  simp (config := { maxSteps := 3000000 })
    [storeTemplate, storeJ0, storeJ, storeJ7, storeState, writePackedHalf,
      writeWordsAscending, packedChunks, packedChunk, storeActiveWords,
      storeAddresses, activeAfterWord, wordBytes, storeAddress, storeBase,
      List.range, List.range.loop, List.foldl,
      op, push1, push2, push4, dup1, runInstrSeq,
      Challenge.EvmProof.Stepper.runInstr, pcAfter, hrun, hcap, hcap2, hcap3,
      hswap1, word_add_assoc, word_add_ofNat_assoc, Nat.add_assoc,
      Word.land_comm, Word.lor_comm,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, UInt256.succ, Instr.size,
      Instr.size_push, Instr.size_op]
  simp only [add_assoc_explicit, add_assoc_explicit_hAdd,
    add_assoc_hAdd_explicit, word_add_assoc]
  simp [Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc,
    shiftRight_zero, Word.land_comm]

theorem runInstrSeq_store1
    (s : State) (startPC value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq (storeTemplate 1)
      { s with pc := startPC, stack := value :: rest } =
      some (storeState s
        (pcAfter startPC (storeTemplate 1)) 1 value rest) := by
  have hcap (m : Nat) (hm : m ≤ 2) : rest.length + m < 1024 := by
    omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by
    omega
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by
    omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  simp (config := { maxSteps := 3000000 })
    [storeTemplate, storeJ0, storeJ, storeJ7, storeState, writePackedHalf,
      writeWordsAscending, packedChunks, packedChunk, storeActiveWords,
      storeAddresses, activeAfterWord, wordBytes, storeAddress, storeBase,
      List.range, List.range.loop, List.foldl,
      op, push1, push2, push4, dup1, runInstrSeq,
      Challenge.EvmProof.Stepper.runInstr, pcAfter, hrun, hcap, hcap2, hcap3,
      hswap1, word_add_assoc, word_add_ofNat_assoc, Nat.add_assoc,
      Word.land_comm, Word.lor_comm,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, UInt256.succ, Instr.size,
      Instr.size_push, Instr.size_op]
  simp only [add_assoc_explicit, add_assoc_explicit_hAdd,
    add_assoc_hAdd_explicit, word_add_assoc]
  simp [Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc,
    shiftRight_zero, Word.land_comm]

private theorem runInstrSeq_half_of_store
    (s : State) (startPC : UInt256) (half : Nat)
    (value other : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1018) (hrun : s.halt = .Running)
    (hstore :
      runInstrSeq (storeTemplate half)
        { s with
          pc := pcAfter (pcAfter startPC (endianStage 8 mask8))
            (endianStage 16 mask16)
          stack := packedWord value :: other :: rest } =
      some (storeState s
        (pcAfter (pcAfter (pcAfter startPC (endianStage 8 mask8))
          (endianStage 16 mask16)) (storeTemplate half))
        half (packedWord value) (other :: rest))) :
    runInstrSeq (halfTemplate half)
      { s with pc := startPC, stack := value :: other :: rest } =
      some (afterHalf s startPC half (packedWord value) (other :: rest)) := by
  have h8 := runInstrSeq_endianStage s startPC value 8 mask8 (other :: rest)
    (by simp; omega) hrun
  have h16 := runInstrSeq_endianStage s
    (pcAfter startPC (endianStage 8 mask8))
    (packedStage value 8 mask8) 16 mask16 (other :: rest)
    (by simp; omega) hrun
  have h16store := runInstrSeq_append_running h16
    (by simp [stageState_halt, hrun])
    (by simpa only [stageState, packedWord] using hstore)
  have hhalf :
      runInstrSeq
        (endianStage 8 mask8 ++
          (endianStage 16 mask16 ++ storeTemplate half))
        { s with pc := startPC, stack := value :: other :: rest } =
      some (storeState s
        (pcAfter (pcAfter (pcAfter startPC (endianStage 8 mask8))
          (endianStage 16 mask16)) (storeTemplate half))
        half (packedWord value) (other :: rest)) := by
    have h := runInstrSeq_append_running h8
      (by simp [stageState_halt, hrun]) h16store
    simpa only [List.append_assoc, packedWord] using h
  have hpc :
      pcAfter startPC (halfTemplate half) =
        pcAfter (pcAfter (pcAfter startPC (endianStage 8 mask8))
          (endianStage 16 mask16)) (storeTemplate half) := by
    rw [halfTemplate, pcAfter_append, pcAfter_append]
  have hend :
      afterHalf s startPC half (packedWord value) (other :: rest) =
        storeState s
          (pcAfter (pcAfter (pcAfter startPC (endianStage 8 mask8))
            (endianStage 16 mask16)) (storeTemplate half))
          half (packedWord value) (other :: rest) := by
    unfold afterHalf storeState
    rw [hpc]
  rw [hend]
  rw [halfTemplate, List.append_assoc]
  exact hhalf

theorem runInstrSeq_half0
    (s : State) (startPC : UInt256)
    (value other : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1018) (hrun : s.halt = .Running) :
    runInstrSeq (halfTemplate 0)
      { s with pc := startPC, stack := value :: other :: rest } =
      some (afterHalf s startPC 0 (packedWord value) (other :: rest)) := by
  exact runInstrSeq_half_of_store s startPC 0 value other rest hstack hrun
    (by
      simpa [packedWord] using
        (runInstrSeq_store0 s
          (pcAfter (pcAfter startPC (endianStage 8 mask8))
            (endianStage 16 mask16))
          (packedWord value) (other :: rest) (by simp; omega) hrun))

theorem runInstrSeq_half1
    (s : State) (startPC : UInt256)
    (value other : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1018) (hrun : s.halt = .Running) :
    runInstrSeq (halfTemplate 1)
      { s with pc := startPC, stack := value :: other :: rest } =
      some (afterHalf s startPC 1 (packedWord value) (other :: rest)) := by
  exact runInstrSeq_half_of_store s startPC 1 value other rest hstack hrun
    (by
      simpa [packedWord] using
        (runInstrSeq_store1 s
          (pcAfter (pcAfter startPC (endianStage 8 mask8))
            (endianStage 16 mask16))
          (packedWord value) (other :: rest) (by simp; omega) hrun))

theorem runInstrSeq_ascendingPacked
    (s : State) (startPC messageOffset returnPC : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1017)
    (hrun : s.halt = .Running) :
    runInstrSeq ascendingPackedTemplate
      (scheduleEntry s startPC messageOffset returnPC rest) =
      some (expectedState s startPC messageOffset returnPC rest) := by
  have hinitial := runInstrSeq_initial s startPC messageOffset returnPC rest
    (by omega) hrun
  let t0 : State :=
    afterHalf (afterInitial s startPC messageOffset returnPC rest)
      (pcAfter startPC initialTemplate) 0
      (packedWord (inputWord0 s messageOffset))
      (inputWord1 s messageOffset :: returnPC :: rest)
  have h0raw := runInstrSeq_half0
    (afterInitial s startPC messageOffset returnPC rest)
    (pcAfter startPC initialTemplate)
    (inputWord0 s messageOffset) (inputWord1 s messageOffset)
    (returnPC :: rest) (by simp; omega) (by simpa using hrun)
  have h0 :
      runInstrSeq (halfTemplate 0)
        (afterInitial s startPC messageOffset returnPC rest) =
      some t0 := by
    simpa only [t0, afterInitial, List.cons_append, List.nil_append] using h0raw
  have hinit0 :
      runInstrSeq (initialTemplate ++ halfTemplate 0)
        (scheduleEntry s startPC messageOffset returnPC rest) =
      some t0 := by
    have h := runInstrSeq_append_running hinitial
      (by simpa using hrun) h0
    simpa only [t0] using h
  have h1raw := runInstrSeq_half1 t0 t0.pc
    (inputWord1 s messageOffset) returnPC rest
    (by omega) (by simpa [t0] using hrun)
  have h1 :
      runInstrSeq (halfTemplate 1) t0 =
        some (afterHalf t0 t0.pc 1
          (packedWord (inputWord1 s messageOffset)) (returnPC :: rest)) := by
    simpa only [t0, afterHalf] using h1raw
  have hfull :
      runInstrSeq ((initialTemplate ++ halfTemplate 0) ++ halfTemplate 1)
        (scheduleEntry s startPC messageOffset returnPC rest) =
      some (afterHalf t0 t0.pc 1
        (packedWord (inputWord1 s messageOffset)) (returnPC :: rest)) := by
    exact runInstrSeq_append_running hinit0
      (by simp [afterHalf_halt, t0, afterInitial_halt, hrun]) h1
  have hend :
      afterHalf t0 t0.pc 1
          (packedWord (inputWord1 s messageOffset)) (returnPC :: rest) =
        expectedState s startPC messageOffset returnPC rest := by
    simp only [t0, afterInitial, afterHalf, expectedState, expectedMemory,
      expectedActiveWords, packedInput0, packedInput1, ascendingPackedTemplate,
      pcAfter_append, List.cons_append, List.nil_append]
  rw [hend] at hfull
  simpa only [ascendingPackedTemplate] using hfull

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleTrace
