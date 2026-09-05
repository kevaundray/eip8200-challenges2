import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# H12 shared selecting-round raw evaluator traces

These theorems evaluate the generic helper body for forms `f1` and `f3`.
The final `JUMP` is outside the template.  No concrete artifact is used.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedSelectRoundTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanSelect
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTrace

private theorem word_add_assoc (u v w : UInt256) :
    (u + v) + w = u + (v + w) := by
  apply word_ext
  change ((u.val + v.val) + w.val).val =
    (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

/-! ## Raw f1 evaluator trace -/

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_f1 (s : State) (startPC xAddress returnPC : UInt256)
    (rotation : Nat) (working : Compression.EvmWorking)
    (constant : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1013)
    (hrun : s.halt = .Running) (hrot : rotation ≤ 32) :
    runInstrSeq
        (helperBeforeJumpTemplate 1 xAddress rotation constant)
        (helperEntry s startPC xAddress rotation returnPC working rest) =
      some (afterHelperBeforeJump s
        (pcAfter startPC
          (helperBeforeJumpTemplate 1 xAddress rotation constant))
        returnPC 1 working xAddress rotation constant rest) := by
  have hcap (m : Nat) (hm : m ≤ 11) : rest.length + m < 1024 := by
    omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  have hswap2 (u v w : UInt256) (rho : List UInt256) :
      (u :: v :: w :: rho).exchange 0 2 =
        some (w :: v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u w [v] rho
  have hswap3 (u v w z : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: rho).exchange 0 3 =
        some (z :: v :: w :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u z [v, w] rho
  have hswap4 (u v w z q : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: rho).exchange 0 4 =
        some (q :: v :: w :: z :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u q [v, w, z] rho
  have hswap5 (u v w z q r : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: r :: rho).exchange 0 5 =
        some (r :: v :: w :: z :: q :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u r [v, w, z, q] rho
  have hadd (u v : UInt256) : u + v = u.add v := by
    rfl
  have hzero (u : UInt256) : u.add (0 : UInt256) = u := by
    apply word_ext
    change (u.val + (0 : UInt256).val).val = u.val.val
    rw [Fin.val_add]
    change (u.val.val + 0) % UInt256.size = u.val.val
    rw [Nat.add_zero, Nat.mod_eq_of_lt u.val.isLt]
  have hcomm (u v : UInt256) : u.add v = v.add u := by
    exact word_add_comm u v
  have hxorcomm (u v : UInt256) : u.xor v = v.xor u := by
    exact BooleanSelect.xor_comm u v
  have hbase : constant.add
      (working.a.add
        ((MachineState.readWord s.memory xAddress.toNat).add
          (working.d.xor (working.b.land (working.c.xor working.d))))) =
      constant.add
        ((working.a.add
          (working.d.xor ((working.c.xor working.d).land working.b))).add
          (MachineState.readWord s.memory xAddress.toNat)) := by
    rw [Word.land_comm working.b (working.c.xor working.d)]
    apply congrArg (fun z : UInt256 => constant.add z)
    rw [hcomm (MachineState.readWord s.memory xAddress.toNat)
      (working.d.xor ((working.c.xor working.d).land working.b))]
    exact (word_add_assoc working.a
      (working.d.xor ((working.c.xor working.d).land working.b))
      (MachineState.readWord s.memory xAddress.toNat)).symm
  simp (config := { maxSteps := 3000000 })
    [helperBeforeJumpTemplate, booleanOps, op, push1, push4, dup1, dup2,
      dup3, dup4, dup5, dup6, dup7, dup8, swap1, swap2, swap3, swap4, swap5,
      mask, c10, c22, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      helperEntry, afterHelperBeforeJump, roundWords,
      pcAfter, StackRound.stackRound, StackRound.stackF,
      StackRound.stackSum, StackRound.stackRawRot, StackRound.stackC10,
      Word.mask32, List.exchange, hrun, hcap, hswap1, hswap2, hswap3,
      hswap4, hswap5, UInt256.succ, Instr.size, Instr.size_push,
      Instr.size_op, Nat.add_assoc, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, Word.land_comm,
      Word.lor_comm, BooleanSelect.xor_comm, State.activeWordsAfterUInt256,
      hadd, hzero, hcomm, hxorcomm]
  constructor
  · rw [hbase, hcomm working.e]
    rw [hcomm working.e]
    exact SharedRoundTrace.raw_rotate_or_fold _ working.e rotation
      (SharedRoundTrace.mask_land_toNat_lt _) hrot
  · exact SharedRoundTrace.c10_or_fold working.c

/-! ## Raw f3 evaluator trace -/

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_f3 (s : State) (startPC xAddress returnPC : UInt256)
    (rotation : Nat) (working : Compression.EvmWorking)
    (constant : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1013)
    (hrun : s.halt = .Running) (hrot : rotation ≤ 32) :
    runInstrSeq
        (helperBeforeJumpTemplate 3 xAddress rotation constant)
        (helperEntry s startPC xAddress rotation returnPC working rest) =
      some (afterHelperBeforeJump s
        (pcAfter startPC
          (helperBeforeJumpTemplate 3 xAddress rotation constant))
        returnPC 3 working xAddress rotation constant rest) := by
  have hcap (m : Nat) (hm : m ≤ 11) : rest.length + m < 1024 := by
    omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  have hswap2 (u v w : UInt256) (rho : List UInt256) :
      (u :: v :: w :: rho).exchange 0 2 =
        some (w :: v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u w [v] rho
  have hswap3 (u v w z : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: rho).exchange 0 3 =
        some (z :: v :: w :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u z [v, w] rho
  have hswap4 (u v w z q : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: rho).exchange 0 4 =
        some (q :: v :: w :: z :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u q [v, w, z] rho
  have hswap5 (u v w z q r : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: r :: rho).exchange 0 5 =
        some (r :: v :: w :: z :: q :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u r [v, w, z, q] rho
  have hadd (u v : UInt256) : u + v = u.add v := by
    rfl
  have hzero (u : UInt256) : u.add (0 : UInt256) = u := by
    apply word_ext
    change (u.val + (0 : UInt256).val).val = u.val.val
    rw [Fin.val_add]
    change (u.val.val + 0) % UInt256.size = u.val.val
    rw [Nat.add_zero, Nat.mod_eq_of_lt u.val.isLt]
  have hcomm (u v : UInt256) : u.add v = v.add u := by
    exact word_add_comm u v
  have hxorcomm (u v : UInt256) : u.xor v = v.xor u := by
    exact BooleanSelect.xor_comm u v
  have hbase : constant.add
      (working.a.add
        ((MachineState.readWord s.memory xAddress.toNat).add
          (working.c.xor (working.d.land (working.b.xor working.c))))) =
      constant.add
        ((working.a.add
          (working.c.xor ((working.b.xor working.c).land working.d))).add
          (MachineState.readWord s.memory xAddress.toNat)) := by
    rw [Word.land_comm working.d (working.b.xor working.c)]
    apply congrArg (fun z : UInt256 => constant.add z)
    rw [hcomm (MachineState.readWord s.memory xAddress.toNat)
      (working.c.xor ((working.b.xor working.c).land working.d))]
    exact (word_add_assoc working.a
      (working.c.xor ((working.b.xor working.c).land working.d))
      (MachineState.readWord s.memory xAddress.toNat)).symm
  simp (config := { maxSteps := 3000000 })
    [helperBeforeJumpTemplate, booleanOps, op, push1, push4, dup1, dup2,
      dup3, dup4, dup5, dup6, dup7, dup8, swap1, swap2, swap3, swap4, swap5,
      mask, c10, c22, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      helperEntry, afterHelperBeforeJump, roundWords,
      pcAfter, StackRound.stackRound, StackRound.stackF,
      StackRound.stackSum, StackRound.stackRawRot, StackRound.stackC10,
      Word.mask32, List.exchange, hrun, hcap, hswap1, hswap2, hswap3,
      hswap4, hswap5, UInt256.succ, Instr.size, Instr.size_push,
      Instr.size_op, Nat.add_assoc, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, Word.land_comm,
      Word.lor_comm, BooleanSelect.xor_comm, State.activeWordsAfterUInt256,
      hadd, hzero, hcomm, hxorcomm]
  constructor
  · rw [hbase, hcomm working.e]
    rw [hcomm working.e]
    exact SharedRoundTrace.raw_rotate_or_fold _ working.e rotation
      (SharedRoundTrace.mask_land_toNat_lt _) hrot
  · exact SharedRoundTrace.c10_or_fold working.c

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedSelectRoundTrace
