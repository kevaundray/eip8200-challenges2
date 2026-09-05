import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-!
# Raw evaluator trace for the dense two-word schedule helper

This file proves the 56 instructions before the final return `JUMP`.  The
result is generic in the surrounding state, memory, words, return address,
and suffix stack.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

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

theorem pcAfter_append (pc : UInt256) (first second : List Instr) :
    pcAfter pc (first ++ second) = pcAfter (pcAfter pc first) second := by
  induction first generalizing pc with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.cons_append, pcAfter]
      exact ih (pc := pc + UInt256.ofNat instruction.size)

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

@[simp] theorem afterDenseHalf_halt
    (s : State) (startPC : UInt256) (half : Nat)
    (value : UInt256) (rest : List UInt256) :
    (afterDenseHalf s startPC half value rest).halt = s.halt := by
  rfl

def stageState (s : State) (endPC value : UInt256)
    (shift : Nat) (mask : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := endPC
    stack := packedStage value shift mask :: rest }

@[simp] theorem stageState_halt
    (s : State) (endPC value : UInt256) (shift : Nat)
    (mask : UInt256) (rest : List UInt256) :
    (stageState s endPC value shift mask rest).halt = s.halt := by
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
  have h32 : UInt256.ofNat 32 + messageOffset =
      messageOffset + UInt256.ofNat 32 :=
    word_add_comm _ _
  simp (config := { maxSteps := 2000000 })
    [initialTemplate, scheduleEntry, afterInitial, inputWord0, inputWord1,
      loadedActiveWords, activeAfterWord, op, push1, dup1, swap1,
      runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, hrun, hcap,
      hcap2, hcap3, hcap4, hswap1, h32, word_add_assoc,
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

theorem runInstrSeq_denseStore
    (s : State) (startPC : UInt256) (half : Nat)
    (value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1022) (hrun : s.halt = .Running) :
    runInstrSeq
        [push2 (UInt256.ofNat (denseStoreAddress half)), op .MSTORE]
      { s with pc := startPC, stack := value :: rest } =
      some { s with
        pc := pcAfter startPC
          [push2 (UInt256.ofNat (denseStoreAddress half)), op .MSTORE]
        stack := rest
        memory := writeDenseWord s.memory (denseStoreOffset half) value
        activeWords := denseStoreActiveWords s.activeWords
          [denseStoreOffset half] } := by
  have hcap (m : Nat) (hm : m ≤ 2) : rest.length + m < 1024 := by
    omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by
    omega
  simp [push2, op, denseStoreAddress, denseStoreOffset, writeDenseWord, wordBytes,
    denseStoreActiveWords, activeAfterWord, runInstrSeq,
    Challenge.EvmProof.Stepper.runInstr, pcAfter, hrun, hcap, hcap2,
    UInt256.succ, Instr.size, Instr.size_push, Instr.size_op,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, add_ofNat_assoc_hAdd]
  rfl

theorem runInstrSeq_denseHalf
    (s : State) (startPC : UInt256) (half : Nat)
    (value other : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1018) (hrun : s.halt = .Running) :
    runInstrSeq (denseHalfTemplate half)
      { s with pc := startPC, stack := value :: other :: rest } =
      some (afterDenseHalf s startPC half (packedWord value)
        (other :: rest)) := by
  have h8 := runInstrSeq_endianStage s startPC value 8 mask8
    (other :: rest) (by simp; omega) hrun
  have h16 := runInstrSeq_endianStage s
    (pcAfter startPC endianStage8)
    (packedStage value 8 mask8) 16 mask16 (other :: rest)
    (by simp; omega) hrun
  have hstore := runInstrSeq_denseStore s
    (pcAfter (pcAfter startPC endianStage8) endianStage16)
    half (packedWord value) (other :: rest) (by simp; omega) hrun
  have h16store := runInstrSeq_append_running h16
    (by simp [stageState_halt, hrun])
    (by simpa only [stageState, packedWord, endianStage16] using hstore)
  have hhalf :
      runInstrSeq (endianStage8 ++ (endianStage16 ++
        [push2 (UInt256.ofNat (denseStoreAddress half)), op .MSTORE]))
        { s with pc := startPC, stack := value :: other :: rest } =
      some { s with
        pc := pcAfter (pcAfter (pcAfter startPC endianStage8) endianStage16)
          [push2 (UInt256.ofNat (denseStoreAddress half)), op .MSTORE]
        stack := other :: rest
        memory := writeDenseWord s.memory (denseStoreOffset half)
          (packedWord value)
        activeWords := denseStoreActiveWords s.activeWords
          [denseStoreOffset half] } := by
    have h := runInstrSeq_append_running h8
      (by simp [stageState_halt, hrun]) h16store
    simpa only [List.append_assoc, packedWord, endianStage8, endianStage16] using h
  have hpc :
      pcAfter startPC (denseHalfTemplate half) =
        pcAfter (pcAfter (pcAfter startPC endianStage8) endianStage16)
          [push2 (UInt256.ofNat (denseStoreAddress half)), op .MSTORE] := by
    rw [denseHalfTemplate, pcAfter_append, pcAfter_append]
  have hend :
      afterDenseHalf s startPC half (packedWord value) (other :: rest) =
        { s with
          pc := pcAfter (pcAfter (pcAfter startPC endianStage8) endianStage16)
            [push2 (UInt256.ofNat (denseStoreAddress half)), op .MSTORE]
          stack := other :: rest
          memory := writeDenseWord s.memory (denseStoreOffset half)
            (packedWord value)
          activeWords := denseStoreActiveWords s.activeWords
            [denseStoreOffset half] } := by
    unfold afterDenseHalf
    rw [hpc]
  rw [hend]
  rw [denseHalfTemplate, List.append_assoc]
  exact hhalf

theorem runInstrSeq_denseBeforeJump
    (s : State) (startPC messageOffset returnPC : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1017)
    (hrun : s.halt = .Running) :
    runInstrSeq denseBeforeJumpTemplate
      (scheduleEntry s startPC messageOffset returnPC rest) =
      some (denseExpectedState s startPC messageOffset returnPC rest) := by
  have hinitial := runInstrSeq_initial s startPC messageOffset returnPC rest
    (by omega) hrun
  let t1 : State :=
    afterDenseHalf (afterInitial s startPC messageOffset returnPC rest)
      (pcAfter startPC initialTemplate) 1
      (packedWord (inputWord1 s messageOffset))
      (inputWord0 s messageOffset :: returnPC :: rest)
  have h1raw := runInstrSeq_denseHalf
    (afterInitial s startPC messageOffset returnPC rest)
    (pcAfter startPC initialTemplate)
    1 (inputWord1 s messageOffset) (inputWord0 s messageOffset)
    (returnPC :: rest) (by simp; omega) (by simpa using hrun)
  have h1 :
      runInstrSeq (denseHalfTemplate 1)
        (afterInitial s startPC messageOffset returnPC rest) =
      some t1 := by
    simpa only [t1, afterInitial, List.cons_append, List.nil_append] using h1raw
  have hinit1 :
      runInstrSeq (initialTemplate ++ denseHalfTemplate 1)
        (scheduleEntry s startPC messageOffset returnPC rest) =
      some t1 := by
    have h := runInstrSeq_append_running hinitial
      (by simpa using hrun) h1
    simpa only [t1] using h
  have h0raw := runInstrSeq_denseHalf t1 t1.pc 0
    (inputWord0 s messageOffset) returnPC rest
    (by omega) (by simpa [t1] using hrun)
  have h0 :
      runInstrSeq (denseHalfTemplate 0) t1 =
        some (afterDenseHalf t1 t1.pc 0
          (packedWord (inputWord0 s messageOffset)) (returnPC :: rest)) := by
    convert h0raw using 1
    all_goals simp [t1, afterDenseHalf]
  have hfull :
      runInstrSeq ((initialTemplate ++ denseHalfTemplate 1) ++
        denseHalfTemplate 0)
        (scheduleEntry s startPC messageOffset returnPC rest) =
      some (afterDenseHalf t1 t1.pc 0
        (packedWord (inputWord0 s messageOffset)) (returnPC :: rest)) := by
    exact runInstrSeq_append_running hinit1
      (by simp [afterDenseHalf_halt, t1, afterInitial_halt, hrun]) h0
  have hend :
      afterDenseHalf t1 t1.pc 0
          (packedWord (inputWord0 s messageOffset)) (returnPC :: rest) =
        denseExpectedState s startPC messageOffset returnPC rest := by
    simp only [t1, afterInitial, afterDenseHalf, denseExpectedState,
      denseExpectedMemory, denseExpectedActiveWords,
      denseStoreActiveWords, denseStoreAddresses, denseStoreOffset,
      denseStoreAddress,
      packedInput0, packedInput1, pcAfter_append,
      List.cons_append, List.nil_append]
  rw [hend] at hfull
  simpa only [denseBeforeJumpTemplate] using hfull

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
