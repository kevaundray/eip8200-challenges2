import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationFold
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# H12 shared round raw-state interfaces and evaluator traces

The interfaces in this file stop immediately before the helper's final
`JUMP`.  They are generic in the surrounding EVM state and do not inspect a
concrete artifact.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTemplate

def helperEntry (s : State) (startPC xAddress : UInt256)
    (rotation : Nat) (returnPC : UInt256)
    (working : Compression.EvmWorking) (rest : List UInt256) : State :=
  { s with
    pc := startPC
    stack := [xAddress, returnPC, UInt256.ofNat (32 - rotation)] ++
      roundWords working ++ rest }

def afterHelperBeforeJump (s : State) (endPC returnPC : UInt256)
    (j : Nat) (working : Compression.EvmWorking) (xAddress : UInt256)
    (rotation : Nat) (constant : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := endPC
    stack := returnPC ::
      roundWords (StackRound.stackRound working j
        (MachineState.readWord s.memory xAddress.toNat) rotation constant) ++ rest
    memory := s.memory
    activeWords := s.activeWordsAfterUInt256 xAddress.toNat 32 }

def rawEntry := helperEntry
def rawAfterHelperBeforeJump := afterHelperBeforeJump

theorem mask_land_toNat_lt (x : UInt256) :
    (UInt256.land mask x).toNat < 2 ^ 32 := by
  rw [Word.land_comm mask x]
  change (Word.mask32 x).toNat < 2 ^ 32
  rw [Word.mask32_eq_ofUInt32, Word.ofUInt32_toNat]
  exact (Word.toUInt32 x).toNat_lt

private theorem word_add_assoc (u v w : UInt256) :
    (u + v) + w = u + (v + w) := by
  apply word_ext
  change ((u.val + v.val) + w.val).val =
    (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

private theorem maskedRotateAdd (q e r r' : UInt256) :
    UInt256.land mask
        (UInt256.add
          (((mask.land q).shiftLeft r).lor
            ((mask.land q).shiftRight r')) e) =
      UInt256.land
        (UInt256.add
          (((q.land mask).shiftLeft r).lor
            ((q.land mask).shiftRight r')) e) mask := by
  rw [Word.land_comm mask q]
  exact Word.land_comm _ _

theorem raw_rotate_or_fold (q e : UInt256) (rotation : Nat)
    (hq : (mask.land q).toNat < 2 ^ 32) (hrot : rotation ≤ 32) :
    UInt256.land mask
        (UInt256.add
          (UInt256.shiftRight
            ((mask.land q).lor
              ((mask.land q).shiftLeft (UInt256.ofNat 32)))
            (UInt256.ofNat (32 - rotation)))
          e) =
      UInt256.land
        (UInt256.add
          (((q.land mask).shiftLeft (UInt256.ofNat rotation)).lor
            ((q.land mask).shiftRight (UInt256.ofNat (32 - rotation))))
          e)
        mask := by
  have hfold :
      UInt256.shiftRight
          ((mask.land q).lor
            ((mask.land q).shiftLeft (UInt256.ofNat 32)))
          (UInt256.ofNat (32 - rotation)) =
        StackRound.stackRawRot (mask.land q) rotation := by
    simpa [HOr.hOr, OrOp.or, EvmSemantics.UInt256.instOrOp] using
      (RotationFold.rawRot_or_fold (q := mask.land q)
        (r := rotation) hq hrot)
  rw [hfold]
  simpa [StackRound.stackRawRot, HOr.hOr, OrOp.or,
    EvmSemantics.UInt256.instOrOp] using
    (maskedRotateAdd q e (UInt256.ofNat rotation)
      (UInt256.ofNat (32 - rotation)))

theorem c10_or_fold (c : UInt256) :
    UInt256.land mask
        (UInt256.shiftRight
          (c.lor (c.shiftLeft (UInt256.ofNat 32)))
          (UInt256.ofNat 22)) =
      StackRound.stackC10 c := by
  rw [Word.land_comm mask]
  simpa [StackRound.stackC10, Word.mask32, mask, HAnd.hAnd, AndOp.and,
    EvmSemantics.UInt256.instAndOp, HOr.hOr, OrOp.or,
    EvmSemantics.UInt256.instOrOp] using
    (RotationFold.C10_or_fold c)

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_f0 (s : State) (startPC xAddress returnPC : UInt256)
    (rotation : Nat) (working : Compression.EvmWorking)
    (rest : List UInt256) (hstack : rest.length < 1013)
    (hrun : s.halt = .Running) (hrot : rotation ≤ 32) :
    runInstrSeq
        (helperBeforeJumpTemplate 0 xAddress rotation 0)
        (helperEntry s startPC xAddress rotation returnPC working rest) =
      some (afterHelperBeforeJump s
        (pcAfter startPC (helperBeforeJumpTemplate 0 xAddress rotation 0))
        returnPC 0 working xAddress rotation 0 rest) := by
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
    exact Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanSelect.xor_comm u v
  have hbase : working.a.add
      ((MachineState.readWord s.memory xAddress.toNat).add
        (working.d.xor (working.b.xor working.c))) =
      (working.a.add (working.d.xor (working.b.xor working.c))).add
        (MachineState.readWord s.memory xAddress.toNat) := by
    rw [hcomm (MachineState.readWord s.memory xAddress.toNat)]
    exact (word_add_assoc working.a
      (working.d.xor (working.b.xor working.c))
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
      hadd, hzero, hcomm, hxorcomm, hbase]
  constructor
  · rw [hcomm working.e]
    rw [hcomm working.e]
    rw [hcomm (MachineState.readWord s.memory xAddress.toNat)]
    exact raw_rotate_or_fold _ working.e rotation
      (mask_land_toNat_lt _) hrot
  · exact c10_or_fold working.c

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTrace
