import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-!
# H31 fast-output raw trace

The trace is generic in the complete machine state, memory, and suffix stack.
It proves the primary 50-operation helper: 49 operations before `RETURN` and
the final `RETURN` operation.  The five loads occur before the only store.
Canonical 32-bit conditions are intentionally absent from this raw layer.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

def inputAddress (index : Nat) : Nat := 32 + 32 * index

def inputWord (s : State) (index : Nat) : UInt256 :=
  MachineState.readWord s.memory (inputAddress index)

def loadActive (current : UInt256) (address : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.activeWordsAfter current.toNat address 32)

def loadActive5 (s : State) : UInt256 :=
  loadActive (loadActive (loadActive (loadActive
    (loadActive s.activeWords (inputAddress 0)) (inputAddress 1))
    (inputAddress 2)) (inputAddress 3)) (inputAddress 4)

def outputWord (s : State) : UInt256 :=
  DenseScheduleTemplate.packedStage (DenseScheduleTemplate.packedStage
    (packWords (inputWord s 0) (inputWord s 1) (inputWord s 2)
      (inputWord s 3) (inputWord s 4)) 8 FastOutputTemplate.mask8) 16
        FastOutputTemplate.mask16

def outputMemory (s : State) : ByteArray :=
  MachineState.writeBytes s.memory
    (Data.Bytes.natToBytesPadded (outputWord s).toNat 32) 0

def afterFastLoad (s : State) (startPC : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := pcAfter startPC fastLoad0
    stack := [inputWord s 0] ++ rest
    activeWords := loadActive s.activeWords (inputAddress 0) }

def afterFastPackStep (s : State) (startPC : UInt256) (address : Nat)
    (acc : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := pcAfter startPC (fastPackStep address)
    stack := [packAppend acc (MachineState.readWord s.memory address)] ++ rest
    activeWords := loadActive s.activeWords address }

def afterFastPack (s : State) (startPC : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := pcAfter startPC fastPackTemplate
    stack := [packWords (inputWord s 0) (inputWord s 1) (inputWord s 2)
      (inputWord s 3) (inputWord s 4)] ++ rest
    activeWords := loadActive5 s }

@[simp] theorem afterFastLoad_halt
    (s : State) (startPC : UInt256) (rest : List UInt256) :
    (afterFastLoad s startPC rest).halt = s.halt := by
  rfl

@[simp] theorem afterFastPackStep_halt
    (s : State) (startPC : UInt256) (address : Nat)
    (acc : UInt256) (rest : List UInt256) :
    (afterFastPackStep s startPC address acc rest).halt = s.halt := by
  rfl

def afterFastEndian (s : State) (startPC : UInt256)
    (stage : List Instr) (shift : Nat) (mask : UInt256)
    (value : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := pcAfter startPC stage
    stack := [DenseScheduleTemplate.packedStage value shift mask] ++ rest }

@[simp] theorem afterFastEndian_halt
    (s : State) (startPC : UInt256) (stage : List Instr) (shift : Nat)
    (mask value : UInt256) (rest : List UInt256) :
    (afterFastEndian s startPC stage shift mask value rest).halt = s.halt := by
  rfl

def afterFastStore (s : State) (startPC value : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := pcAfter startPC fastStoreAndSetup
    stack := [⟨0⟩, UInt256.ofNat 32] ++ rest
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded value.toNat 32) 0
    activeWords := s.activeWordsAfterUInt256 0 32 }

def afterFastReturn (s : State) (startPC : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := startPC
    stack := rest
    halt := .Returned
    hReturn := MachineState.readPadded s.memory 0 32
    activeWords := s.activeWordsAfterUInt256 0 32 }

def outputActiveWords (s : State) : UInt256 :=
  loadActive5 s

def fastOutputBeforeReturnState
    (s : State) (startPC : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := pcAfter startPC fastOutputBeforeReturnTemplate
    stack := [⟨0⟩, UInt256.ofNat 32] ++ rest
    memory := outputMemory s
    activeWords := outputActiveWords s }

def fastOutputReturned
    (s : State) (startPC : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := pcAfter startPC fastOutputBeforeReturnTemplate
    stack := rest
    memory := outputMemory s
    halt := .Returned
    hReturn := MachineState.readPadded (outputMemory s) 0 32
    activeWords := outputActiveWords s }

private theorem activeWordsAfter_zero32 (current : Nat) (hcurrent : 1 ≤ current) :
    MachineState.activeWordsAfter current 0 32 = current := by
  simp [MachineState.activeWordsAfter, hcurrent]

private theorem activeWordsAfterUInt256_zero32_eq (s : State)
    (hcurrent : 1 ≤ s.activeWords.toNat) :
    s.activeWordsAfterUInt256 0 32 = s.activeWords := by
  unfold State.activeWordsAfterUInt256
  rw [activeWordsAfter_zero32 s.activeWords.toNat hcurrent]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat s.activeWords).symm

private theorem activeWordsAfter_lt256 (current address : Nat)
    (hcurrent : current < 2 ^ 256) (haddress : address + 32 < 2 ^ 256) :
    MachineState.activeWordsAfter current address 32 < 2 ^ 256 := by
  unfold MachineState.activeWordsAfter
  simp only [if_neg (by norm_num : (32 : Nat) ≠ 0)]
  rw [Nat.max_lt]
  constructor
  · exact hcurrent
  · have hdiv : (address + 32 - 1) / 32 < 2 ^ 256 := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < (32 : Nat))]
      omega
    omega

private theorem loadActive_toNat (current : UInt256) (address : Nat)
    (haddress : address + 32 < 2 ^ 256) :
    (loadActive current address).toNat =
      MachineState.activeWordsAfter current.toNat address 32 := by
  unfold loadActive
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (activeWordsAfter_lt256 current.toNat address
      current.val.isLt haddress)]

private theorem loadActive_pos (current : UInt256) (address : Nat)
    (haddress : address + 32 < 2 ^ 256) :
    1 ≤ (loadActive current address).toNat := by
  rw [loadActive_toNat current address haddress]
  simp [MachineState.activeWordsAfter]

private theorem loadActive5_pos (s : State) :
    1 ≤ (loadActive5 s).toNat := by
  unfold loadActive5
  apply loadActive_pos
  norm_num [inputAddress]

private theorem state_eq_of_fields {a b : State}
    (hshared : a.toSharedState = b.toSharedState)
    (hpc : a.pc = b.pc) (hstack : a.stack = b.stack)
    (hexec : a.execLength = b.execLength) (hhalt : a.halt = b.halt)
    (hcall : a.callStack = b.callStack) : a = b := by
  cases a
  cases b
  simp_all

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

theorem runInstrSeq_fastLoad0
    (s : State) (startPC : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq fastLoad0 { s with pc := startPC, stack := rest } =
      some (afterFastLoad s startPC rest) := by
  have hcap (m : Nat) (hm : m ≤ 2) : rest.length + m < 1024 := by
    omega
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  simp [fastLoad0, afterFastLoad, inputWord, inputAddress,
    DenseScheduleTemplate.push1, DenseScheduleTemplate.op,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter,
    hrun, hcap, hcap0, hcap1, loadActive, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.succ,
    Instr.size, Instr.size_push, Instr.size_op]
  rfl

theorem runInstrSeq_fastPackStep
    (s : State) (startPC : UInt256) (address : Nat)
    (acc : UInt256) (rest : List UInt256)
    (haddress : address < 2 ^ 256)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq (fastPackStep address)
      { s with pc := startPC, stack := acc :: rest } =
      some (afterFastPackStep s startPC address acc rest) := by
  have hcap (m : Nat) (hm : m ≤ 2) : rest.length + m < 1024 := by
    omega
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have haddressWord : (UInt256.ofNat address).toNat = address := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt haddress
  simp [fastPackStep, afterFastPackStep, packAppend,
    DenseScheduleTemplate.push1, DenseScheduleTemplate.op,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter,
    hrun, hcap, hcap0, hcap1, hcap2, haddressWord,
    loadActive, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.succ,
    Instr.size, Instr.size_push, Instr.size_op]
  constructor
  · rfl
  · exact Word.lor_comm _ _

theorem runInstrSeq_jumpdest
    (s : State) (startPC : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq [DenseScheduleTemplate.op .JUMPDEST]
      { s with pc := startPC, stack := rest } =
      some { s with
        pc := pcAfter startPC [DenseScheduleTemplate.op .JUMPDEST]
        stack := rest } := by
  have hcap : rest.length < 1024 := by omega
  simp [runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter,
    DenseScheduleTemplate.op, hrun, hcap, UInt256.succ,
    Instr.size, Instr.size_op]
  change startPC + UInt256.ofNat 1 = startPC + UInt256.ofNat 1
  rfl

theorem runInstrSeq_fastPackTemplate
    (s : State) (startPC : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq fastPackTemplate
      { s with pc := startPC, stack := rest } =
      some (afterFastPack s startPC rest) := by
  let entry : State := { s with
    pc := pcAfter startPC [DenseScheduleTemplate.op .JUMPDEST]
    stack := rest }
  have hjump := runInstrSeq_jumpdest s startPC rest hstack hrun
  have hload := runInstrSeq_fastLoad0 s entry.pc rest hstack hrun
  have hprefix :
      runInstrSeq ([DenseScheduleTemplate.op .JUMPDEST] ++ fastLoad0)
        { s with pc := startPC, stack := rest } =
      some (afterFastLoad s entry.pc rest) := by
    have h := runInstrSeq_append_running hjump
      hrun hload
    simpa only [entry, List.cons_append, List.nil_append] using h
  let t0 : State := afterFastLoad s entry.pc rest
  have h1raw := runInstrSeq_fastPackStep t0 t0.pc 64
    (inputWord s 0) rest (by norm_num) hstack (by simpa [t0] using hrun)
  have h1 :
      runInstrSeq (fastPackStep 64) t0 =
        some (afterFastPackStep t0 t0.pc 64 (inputWord s 0) rest) := by
    simpa [t0, afterFastLoad, inputWord] using h1raw
  let t1 : State := afterFastPackStep t0 t0.pc 64 (inputWord s 0) rest
  have hprefix1 :
      runInstrSeq (([DenseScheduleTemplate.op .JUMPDEST] ++ fastLoad0) ++
          fastPackStep 64)
        { s with pc := startPC, stack := rest } = some t1 := by
    exact runInstrSeq_append_running hprefix
      (by simpa [t1, t0] using hrun) h1
  have h2raw := runInstrSeq_fastPackStep t1 t1.pc 96
    (packAppend (inputWord s 0) (inputWord s 1)) rest
    (by norm_num) hstack (by simpa [t1, t0] using hrun)
  have h2 :
      runInstrSeq (fastPackStep 96) t1 =
        some (afterFastPackStep t1 t1.pc 96
          (packAppend (inputWord s 0) (inputWord s 1)) rest) := by
    simpa [t1, t0, afterFastLoad, afterFastPackStep, inputWord,
      inputAddress] using h2raw
  let t2 : State := afterFastPackStep t1 t1.pc 96
    (packAppend (inputWord s 0) (inputWord s 1)) rest
  have hprefix2 :
      runInstrSeq ((([DenseScheduleTemplate.op .JUMPDEST] ++ fastLoad0) ++
          fastPackStep 64) ++ fastPackStep 96)
        { s with pc := startPC, stack := rest } = some t2 := by
    exact runInstrSeq_append_running hprefix1
      (by simpa [t2, t1, t0] using hrun) h2
  have h3raw := runInstrSeq_fastPackStep t2 t2.pc 128
    (packAppend (packAppend (inputWord s 0) (inputWord s 1))
      (inputWord s 2)) rest
    (by norm_num) hstack (by simpa [t2, t1, t0] using hrun)
  have h3 :
      runInstrSeq (fastPackStep 128) t2 =
        some (afterFastPackStep t2 t2.pc 128
          (packAppend (packAppend (inputWord s 0) (inputWord s 1))
            (inputWord s 2)) rest) := by
    simpa [t2, t1, t0, afterFastLoad, afterFastPackStep, inputWord,
      inputAddress] using h3raw
  let t3 : State := afterFastPackStep t2 t2.pc 128
    (packAppend (packAppend (inputWord s 0) (inputWord s 1))
      (inputWord s 2)) rest
  have hprefix3 :
      runInstrSeq (((( [DenseScheduleTemplate.op .JUMPDEST] ++ fastLoad0) ++
          fastPackStep 64) ++ fastPackStep 96) ++ fastPackStep 128)
        { s with pc := startPC, stack := rest } = some t3 := by
    exact runInstrSeq_append_running hprefix2
      (by simpa [t3, t2, t1, t0] using hrun) h3
  have h4raw := runInstrSeq_fastPackStep t3 t3.pc 160
    (packAppend (packAppend (packAppend (inputWord s 0) (inputWord s 1))
      (inputWord s 2)) (inputWord s 3)) rest
    (by norm_num) hstack (by simpa [t3, t2, t1, t0] using hrun)
  have h4 :
      runInstrSeq (fastPackStep 160) t3 =
        some (afterFastPackStep t3 t3.pc 160
          (packAppend (packAppend (packAppend (inputWord s 0) (inputWord s 1))
            (inputWord s 2)) (inputWord s 3)) rest) := by
    simpa [t3, t2, t1, t0, afterFastLoad, afterFastPackStep, inputWord,
      inputAddress] using h4raw
  let t4 : State := afterFastPackStep t3 t3.pc 160
    (packAppend (packAppend (packAppend (inputWord s 0) (inputWord s 1))
      (inputWord s 2)) (inputWord s 3)) rest
  have hfull :
      runInstrSeq ((((([DenseScheduleTemplate.op .JUMPDEST] ++ fastLoad0) ++
          fastPackStep 64) ++ fastPackStep 96) ++ fastPackStep 128) ++
          fastPackStep 160)
        { s with pc := startPC, stack := rest } = some t4 := by
    exact runInstrSeq_append_running hprefix3
      (by simpa [t4, t3, t2, t1, t0] using hrun) h4
  have ht4 : t4 = afterFastPack s startPC rest := by
    simp [t4, t3, t2, t1, t0, entry, afterFastPackStep, afterFastLoad,
      afterFastPack, fastPackTemplate, fastLoad0, fastPackStep,
      inputWord, inputAddress, loadActive5, loadActive, packWords,
      pcAfter_append, pcAfter, Instr.size, List.cons_append, List.nil_append]
  rw [ht4] at hfull
  simpa only [fastPackTemplate, List.append_assoc] using hfull

theorem runInstrSeq_fastEndianStage8
    (s : State) (startPC value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq fastEndianStage8
      { s with pc := startPC, stack := value :: rest } =
      some { s with
        pc := pcAfter startPC fastEndianStage8
        stack := DenseScheduleTemplate.packedStage value 8
          FastOutputTemplate.mask8 :: rest } := by
  have hcap (m : Nat) (hm : m ≤ 2) : rest.length + m < 1024 := by
    omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  simp (config := { maxSteps := 1000000 })
    [fastEndianStage8, push31, DenseScheduleTemplate.push1,
      DenseScheduleTemplate.op, DenseScheduleTemplate.dup1,
      DenseScheduleTemplate.swap1, DenseScheduleTemplate.packedStage,
      runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, hrun,
      hcap, hcap2, hcap3, hswap1, UInt256.succ, Instr.size,
      Instr.size_push, Instr.size_op,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, Word.land_comm,
      Word.lor_comm]
  repeat first
    | rw [add_ofNat_assoc_hAdd]
    | rw [add_ofNat_assoc_add]
    | rw [add_ofNat_assoc]
  simp only [add_assoc_explicit, add_assoc_explicit_hAdd,
    add_assoc_hAdd_explicit, word_add_assoc]
  simp [Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]

theorem runInstrSeq_fastEndianStage16
    (s : State) (startPC value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq fastEndianStage16
      { s with pc := startPC, stack := value :: rest } =
      some { s with
        pc := pcAfter startPC fastEndianStage16
        stack := DenseScheduleTemplate.packedStage value 16
          FastOutputTemplate.mask16 :: rest } := by
  have hcap (m : Nat) (hm : m ≤ 2) : rest.length + m < 1024 := by
    omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  simp (config := { maxSteps := 1000000 })
    [fastEndianStage16, push30, DenseScheduleTemplate.push1,
      DenseScheduleTemplate.op, DenseScheduleTemplate.dup1,
      DenseScheduleTemplate.swap1, DenseScheduleTemplate.packedStage,
      runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, hrun,
      hcap, hcap2, hcap3, hswap1, UInt256.succ, Instr.size,
      Instr.size_push, Instr.size_op,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, Word.land_comm,
      Word.lor_comm]
  repeat first
    | rw [add_ofNat_assoc_hAdd]
    | rw [add_ofNat_assoc_add]
    | rw [add_ofNat_assoc]
  simp only [add_assoc_explicit, add_assoc_explicit_hAdd,
    add_assoc_hAdd_explicit, word_add_assoc]
  simp [Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]

theorem runInstrSeq_fastStoreAndSetup
    (s : State) (startPC value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq fastStoreAndSetup
      { s with pc := startPC, stack := value :: rest } =
      some (afterFastStore s startPC value rest) := by
  have hcap (m : Nat) (hm : m ≤ 2) : rest.length + m < 1024 := by
    omega
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  simp [fastStoreAndSetup, afterFastStore,
    push0, DenseScheduleTemplate.push1, DenseScheduleTemplate.op,
    runInstrSeq,
    Challenge.EvmProof.Stepper.runInstr, pcAfter, hrun, hcap,
    hcap0, hcap1, hcap2, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.succ,
    Instr.size, Instr.size_push, Instr.size_op,
    add_ofNat_assoc_hAdd, add_ofNat_assoc_add, add_ofNat_assoc]
  constructor
  · constructor <;> rfl
  · repeat first
      | rw [word_add_assoc]
    simp [Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]

theorem runInstrSeq_fastReturn
    (s : State) (startPC : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq fastOutputReturnTemplate
      { s with pc := startPC, stack := [⟨0⟩, UInt256.ofNat 32] ++ rest } =
      some (afterFastReturn s startPC rest) := by
  have hcap : rest.length + 2 < 1024 := by omega
  simp [fastOutputReturnTemplate, afterFastReturn, runInstrSeq,
    DenseScheduleTemplate.op, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, hrun, hcap,
    State.activeWordsAfterUInt256]
  constructor <;> rfl

theorem runInstrSeq_fastOutput_beforeReturn
    (s : State) (startPC : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq fastOutputBeforeReturnTemplate
      { s with pc := startPC, stack := rest } =
      some (fastOutputBeforeReturnState s startPC rest) := by
  let packed0 : UInt256 :=
    packWords (inputWord s 0) (inputWord s 1) (inputWord s 2)
      (inputWord s 3) (inputWord s 4)
  let packed8 : UInt256 :=
    DenseScheduleTemplate.packedStage packed0 8 FastOutputTemplate.mask8
  let packed16 : UInt256 :=
    DenseScheduleTemplate.packedStage packed8 16 FastOutputTemplate.mask16
  let t0 : State := afterFastPack s startPC rest
  have hpack : runInstrSeq fastPackTemplate
      { s with pc := startPC, stack := rest } = some t0 := by
    simpa [t0, packed0] using
      (runInstrSeq_fastPackTemplate s startPC rest hstack hrun)
  let t1 : State := afterFastEndian t0 t0.pc fastEndianStage8 8
    FastOutputTemplate.mask8 packed0 rest
  have h8 : runInstrSeq fastEndianStage8 t0 = some t1 := by
    have h := runInstrSeq_fastEndianStage8 t0 t0.pc packed0 rest hstack
      (by simpa [t0, afterFastPack] using hrun)
    simpa [t1, t0, packed0, afterFastEndian, afterFastPack] using h
  let t2 : State := afterFastEndian t1 t1.pc fastEndianStage16 16
    FastOutputTemplate.mask16 packed8 rest
  have h16 : runInstrSeq fastEndianStage16 t1 = some t2 := by
    have h := runInstrSeq_fastEndianStage16 t1 t1.pc packed8 rest hstack
      (by simpa [t1, t0, afterFastEndian, afterFastPack] using hrun)
    simpa [t2, t1, t0, packed8, afterFastEndian, afterFastPack] using h
  let t3 : State := afterFastStore t2 t2.pc packed16 rest
  have hstore : runInstrSeq fastStoreAndSetup t2 = some t3 := by
    have h := runInstrSeq_fastStoreAndSetup t2 t2.pc packed16 rest hstack
      (by simpa [t2, t1, t0, afterFastEndian, afterFastPack] using hrun)
    simpa [t3, t2, t1, t0, packed16, afterFastStore,
      afterFastEndian, afterFastPack] using h
  have h16store : runInstrSeq (fastEndianStage16 ++ fastStoreAndSetup) t1 =
      some t3 := by
    exact runInstrSeq_append_running h16
      (by simpa [t2, t1, t0, afterFastEndian, afterFastPack] using hrun) hstore
  have h8store : runInstrSeq
      (fastEndianStage8 ++ (fastEndianStage16 ++ fastStoreAndSetup)) t0 =
      some t3 := by
    exact runInstrSeq_append_running h8
      (by simpa [t1, t0, afterFastEndian, afterFastPack] using hrun) h16store
  have hfull : runInstrSeq
      (fastPackTemplate ++
        (fastEndianStage8 ++ (fastEndianStage16 ++ fastStoreAndSetup)))
      { s with pc := startPC, stack := rest } = some t3 := by
    exact runInstrSeq_append_running hpack
      (by simpa [t0, afterFastPack] using hrun) h8store
  have ht3 : t3 = fastOutputBeforeReturnState s startPC rest := by
    have hactive_t2 : 1 ≤ t2.activeWords.toNat := by
      simpa [t2, t1, t0, afterFastEndian, afterFastPack,
        outputActiveWords] using loadActive5_pos s
    have hstore_active :
        (afterFastStore t2 t2.pc packed16 rest).activeWords = t2.activeWords := by
      change t2.activeWordsAfterUInt256 0 32 = t2.activeWords
      exact activeWordsAfterUInt256_zero32_eq t2 hactive_t2
    have ht2_active : t2.activeWords = outputActiveWords s := by
      simp [t2, t1, t0, afterFastEndian, afterFastPack, outputActiveWords]
    apply state_eq_of_fields
    · simp [t3, t2, t1, t0, afterFastStore, afterFastEndian, afterFastPack,
        fastOutputBeforeReturnState]
      constructor
      · change (afterFastStore t2 t2.pc packed16 rest).activeWords =
          outputActiveWords s
        exact hstore_active.trans ht2_active
      · simp [afterFastStore, t2, t1, t0, packed16, packed8, packed0,
          afterFastEndian, afterFastPack, outputMemory, outputWord]
    · simp [t3, t2, t1, t0, packed0, packed8, packed16,
        afterFastStore, afterFastEndian, afterFastPack,
        fastOutputBeforeReturnState, fastOutputBeforeReturnTemplate,
        pcAfter_append, pcAfter, Instr.size, List.append_assoc]
    · simp [t3, afterFastStore, fastOutputBeforeReturnState]
    · simp [t3, t2, t1, t0, afterFastStore, afterFastEndian, afterFastPack,
        fastOutputBeforeReturnState]
    · simp [t3, t2, t1, t0, afterFastStore, afterFastEndian, afterFastPack,
        fastOutputBeforeReturnState]
    · simp [t3, t2, t1, t0, afterFastStore, afterFastEndian, afterFastPack,
        fastOutputBeforeReturnState]
  rw [ht3] at hfull
  simpa only [fastOutputBeforeReturnTemplate, List.append_assoc] using hfull

theorem runInstrSeq_fastOutput
    (s : State) (startPC : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq fastOutputTemplate
      { s with pc := startPC, stack := rest } =
      some (fastOutputReturned s startPC rest) := by
  let t : State := fastOutputBeforeReturnState s startPC rest
  have hpre : runInstrSeq fastOutputBeforeReturnTemplate
      { s with pc := startPC, stack := rest } = some t := by
    simpa [t] using
      (runInstrSeq_fastOutput_beforeReturn s startPC rest hstack hrun)
  have hret : runInstrSeq fastOutputReturnTemplate t =
      some (afterFastReturn t t.pc rest) := by
    have h := runInstrSeq_fastReturn t t.pc rest hstack
      (by simpa [t, fastOutputBeforeReturnState] using hrun)
    simpa [t, fastOutputBeforeReturnState] using h
  have hfull : runInstrSeq
      (fastOutputBeforeReturnTemplate ++ fastOutputReturnTemplate)
      { s with pc := startPC, stack := rest } =
      some (afterFastReturn t t.pc rest) := by
    exact runInstrSeq_append_running hpre
      (by simpa [t, fastOutputBeforeReturnState] using hrun) hret
  have hfinal : afterFastReturn t t.pc rest =
      fastOutputReturned s startPC rest := by
    have hactive_t : 1 ≤ t.activeWords.toNat := by
      simpa [t, fastOutputBeforeReturnState, outputActiveWords] using
        loadActive5_pos s
    have hreturn_active :
        (afterFastReturn t t.pc rest).activeWords = t.activeWords := by
      change t.activeWordsAfterUInt256 0 32 = t.activeWords
      exact activeWordsAfterUInt256_zero32_eq t hactive_t
    have ht_active : t.activeWords = outputActiveWords s := by
      simp [t, fastOutputBeforeReturnState, outputActiveWords]
    apply state_eq_of_fields
    · simp [t, afterFastReturn, fastOutputBeforeReturnState,
        fastOutputReturned, outputMemory, outputWord, outputActiveWords]
      change (afterFastReturn t t.pc rest).activeWords = outputActiveWords s
      exact hreturn_active.trans ht_active
    · simp [t, afterFastReturn, fastOutputBeforeReturnState,
        fastOutputReturned, outputMemory, outputWord, outputActiveWords]
    · simp [t, afterFastReturn, fastOutputBeforeReturnState,
        fastOutputReturned, outputMemory, outputWord, outputActiveWords]
    · simp [t, afterFastReturn, fastOutputBeforeReturnState,
        fastOutputReturned, outputMemory, outputWord, outputActiveWords]
    · simp [t, afterFastReturn, fastOutputBeforeReturnState,
        fastOutputReturned, outputMemory, outputWord, outputActiveWords]
    · simp [t, afterFastReturn, fastOutputBeforeReturnState,
        fastOutputReturned, outputMemory, outputWord, outputActiveWords]
  rw [hfinal] at hfull
  simpa only [fastOutputTemplate, List.append_assoc] using hfull

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputTrace
