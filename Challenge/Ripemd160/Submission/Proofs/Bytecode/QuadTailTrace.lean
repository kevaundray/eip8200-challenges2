import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# H30b cached-factor tail raw trace

The tail changes only stack addressing and cleanup.  Its arithmetic and all
memory operations are unchanged from `StackTail`.  The main theorem is a raw
before-`JUMP` adapter; a caller must supply the actual dynamic jump-destination
fact before lifting the final instruction.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

private theorem tailCapacity (rho : List UInt256) (hstack : rho.length < 1007)
    (m : Nat) (hm : m ≤ 16) : rho.length + m < 1024 := by
  omega

set_option linter.unusedSimpArgs false in
theorem quadTail_runTail_of_old_raw
    (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) (out : State)
    (hstack : rest.length < 1007)
    (hraw : StackTail.runTailInstrs StackTail.tail60Instructions
      (StackTail.tailEntry s left right ret rest) = some out) :
    StackTail.runTailInstrs QuadTailTemplate.quadTailBeforeJumpTemplate
      (QuadTailTemplate.tailEntry s left right ret rest) =
      some { out with pc := QuadTailTemplate.tailJumpPC } := by
  have hcap (m : Nat) (hm : m ≤ 16) : rest.length + m < 1024 := by
    exact tailCapacity rest hstack m hm
  have hadd (u v : UInt256) : u + v = u.add v := by
    rfl
  have hraw' := hraw
  simp (config := { maxSteps := 5000000 })
    [StackTail.tail60Instructions, StackTail.c0Instructions,
      StackTail.c1Instructions, StackTail.c2Instructions,
      StackTail.c3Instructions, StackTail.c4Instructions,
      StackTail.storeH0Instructions, StackTail.cleanupInstructions,
      StackTail.tailEntry, StackTail.workingStack,
      StackTail.runTailInstrs, Challenge.EvmProof.Stepper.runInstr,
      hcap, hadd, State.activeWordsAfterUInt256, UInt256.succ,
      Instr.size, Instr.size_push, Instr.size_op,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc] at hraw'
  cases hraw'
  simp (config := { maxSteps := 5000000 })
    [QuadTailTemplate.quadTailBeforeJumpTemplate,
      QuadTailTemplate.c0Instructions, QuadTailTemplate.c1Instructions,
      QuadTailTemplate.c2Instructions, QuadTailTemplate.c3Instructions,
      QuadTailTemplate.c4Instructions,
      QuadTailTemplate.dup4H, QuadTailTemplate.dup9H,
      QuadTailTemplate.dup6H, QuadTailTemplate.dup11H,
      QuadTailTemplate.dup2H, QuadTailTemplate.dup12H,
      QuadTailTemplate.dup3H, QuadTailTemplate.dup13H,
      QuadTailTemplate.storeH0Instructions,
      QuadTailTemplate.cleanupInstructions, QuadTailTemplate.tailEntry,
      QuadTailTemplate.workingStack, QuadTailTemplate.beforeJumpResult,
      StackTail.preJumpResult, StackTail.workingStack,
      StackTail.combined, op, push1, push4, mask,
      StackTail.runTailInstrs, Challenge.EvmProof.Stepper.runInstr,
      QuadTailTemplate.factor, QuadTailTemplate.tailStartPC,
      QuadTailTemplate.tailJumpPC, hcap, hadd,
      State.activeWordsAfterUInt256, UInt256.succ, Instr.size,
      Instr.size_push, Instr.size_op, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]
  decide

theorem runTail_quadTail_beforeJump
    (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256)
    (hactive : 66 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1007) :
    StackTail.runTailInstrs QuadTailTemplate.quadTailBeforeJumpTemplate
      (QuadTailTemplate.tailEntry s left right ret rest) =
      some (QuadTailTemplate.beforeJumpResult s left right ret rest) := by
  have hstackOld : rest.length < 1009 := by omega
  have hraw := StackTail.run_tail60 s left right ret rest hactive hstackOld
  have hrel := quadTail_runTail_of_old_raw s left right ret rest
    (StackTail.preJumpResult s left right ret rest) hstack hraw
  simpa [QuadTailTemplate.beforeJumpResult] using hrel

private theorem runTailInstrs_append {xs ys : List Instr} {s t u : State}
    (hxs : StackTail.runTailInstrs xs s = some t)
    (hys : StackTail.runTailInstrs ys t = some u) :
    StackTail.runTailInstrs (xs ++ ys) s = some u := by
  induction xs generalizing s t with
  | nil =>
      simp [StackTail.runTailInstrs] at hxs
      subst t
      simpa [StackTail.runTailInstrs] using hys
  | cons instruction instructions ih =>
      cases hstep : Challenge.EvmProof.Stepper.runInstr instruction s with
      | none =>
          simp [StackTail.runTailInstrs, hstep] at hxs
      | some next =>
          have hrest : StackTail.runTailInstrs instructions next = some t := by
            simpa [StackTail.runTailInstrs, hstep] using hxs
          have h := ih hrest hys
          simpa [StackTail.runTailInstrs, hstep] using h

theorem runTail_quadTail
    (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256)
    (hactive : 66 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1007)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    StackTail.runTailInstrs QuadTailTemplate.quadTailTemplate
      (QuadTailTemplate.tailEntry s left right ret rest) =
      some (QuadTailTemplate.finalResult s left right ret rest) := by
  have hbody := runTail_quadTail_beforeJump s left right ret rest hactive hstack
  have hjump :
      StackTail.runTailInstrs [StackRoundTemplate.op .JUMP]
        (QuadTailTemplate.beforeJumpResult s left right ret rest) =
      some (QuadTailTemplate.finalResult s left right ret rest) := by
    have hcap : rest.length + 1 < 1024 := by omega
    simp [StackTail.runTailInstrs, QuadTailTemplate.beforeJumpResult,
      QuadTailTemplate.finalResult, StackTail.preJumpResult,
      StackRoundTemplate.op, Challenge.EvmProof.Stepper.runInstr,
      hvalid, hcap]
  have hall := runTailInstrs_append hbody hjump
  simpa [QuadTailTemplate.quadTailTemplate] using hall

set_option linter.unusedSimpArgs false in
theorem quadTail_beforeJump_of_old_raw
    (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) (out : State)
    (hstack : rest.length < 1007) (hrun : s.halt = .Running)
    (hraw : runInstrSeq StackTail.tail60Instructions
      (StackTail.tailEntry s left right ret rest) = some out) :
    runInstrSeq QuadTailTemplate.quadTailBeforeJumpTemplate
      (QuadTailTemplate.tailEntry s left right ret rest) =
      some { out with pc := QuadTailTemplate.tailJumpPC } := by
  have hcap (m : Nat) (hm : m ≤ 16) : rest.length + m < 1024 := by
    exact tailCapacity rest hstack m hm
  have hadd (u v : UInt256) : u + v = u.add v := by
    rfl
  have hraw' := hraw
  simp (config := { maxSteps := 5000000 })
    [StackTail.tail60Instructions, StackTail.c0Instructions,
      StackTail.c1Instructions, StackTail.c2Instructions,
      StackTail.c3Instructions, StackTail.c4Instructions,
      StackTail.storeH0Instructions, StackTail.cleanupInstructions,
      StackTail.tailEntry, StackTail.workingStack,
      runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      hrun, hcap, hadd,
      State.activeWordsAfterUInt256, UInt256.succ, Instr.size,
      Instr.size_push, Instr.size_op, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc] at hraw'
  cases hraw'
  simp (config := { maxSteps := 5000000 })
    [QuadTailTemplate.quadTailBeforeJumpTemplate,
      QuadTailTemplate.c0Instructions, QuadTailTemplate.c1Instructions,
      QuadTailTemplate.c2Instructions, QuadTailTemplate.c3Instructions,
      QuadTailTemplate.c4Instructions,
      QuadTailTemplate.dup4H, QuadTailTemplate.dup9H,
      QuadTailTemplate.dup6H, QuadTailTemplate.dup11H,
      QuadTailTemplate.dup2H, QuadTailTemplate.dup12H,
      QuadTailTemplate.dup3H, QuadTailTemplate.dup13H,
      QuadTailTemplate.storeH0Instructions,
      QuadTailTemplate.cleanupInstructions, QuadTailTemplate.tailEntry,
      QuadTailTemplate.workingStack, QuadTailTemplate.beforeJumpResult,
      StackTail.preJumpResult, StackTail.workingStack,
      StackTail.combined,
      op, push1, push4, mask,
      runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      QuadTailTemplate.factor, QuadTailTemplate.tailStartPC,
      QuadTailTemplate.tailJumpPC, hrun, hcap, hadd,
      State.activeWordsAfterUInt256, UInt256.succ, Instr.size,
      Instr.size_push, Instr.size_op, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailTrace
