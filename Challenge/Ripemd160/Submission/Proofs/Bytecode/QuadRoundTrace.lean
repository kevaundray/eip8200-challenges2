import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCachedTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# H30b four-round raw evaluator trace

The proof composes the generic first gap trace, one `SWAP1`, and the generic
cached pair tail trace.  It is generic in all 256-bit working and stack
values; only the rotation bounds, the strict suffix bound, and the usual
round-zero constant premise are required.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCachedTrace

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_quad (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (constant : UInt256) (rho : List UInt256)
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32)
    (hrot2 : r2 ≤ 32) (hrot3 : r3 ≤ 32) :
    runInstrSeq (quadBeforeJumpTemplate j constant)
      (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working rho) =
      some (quadAfterHelperBeforeJump s
        (pcAfter startPC (quadBeforeJumpTemplate j constant))
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
  let firstPC : UInt256 := pcAfter startPC (firstFTemplate j constant)
  let secondPC : UInt256 := pcAfter firstPC [swap1]
  let firstWorking : Compression.EvmWorking :=
    quadFirstWorking s working j p0 p1 r0 r1 constant
  let afterFirstPair : State := quadFirstState s p0 p1
  let gapState : State :=
    insertState 1
      [p2, UInt256.ofNat (32 - r2), p3, UInt256.ofNat (32 - r3)]
      firstPC
      (pairAfterHelperBeforeJump s
        (pcAfter 0 (pairBeforeJumpTemplate j constant))
        returnPC j working p0 p1 r0 r1 constant
          (QuadGapTemplate.factor :: rho))
  let pairState : State :=
    pairHelperEntry afterFirstPair secondPC p2 p3 returnPC
      r2 r3 firstWorking (QuadRoundTemplate.factor :: rho)

  have hgap := QuadGapTrace.run_firstF j hj constant s startPC p0 p1
    returnPC p2 (UInt256.ofNat (32 - r2)) p3 (UInt256.ofNat (32 - r3))
    r0 r1 working rho hstack hrun hzero hrot0 hrot1
  have hfirst :
      runInstrSeq (firstFTemplate j constant)
        (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
          r0 r1 r2 r3 working rho) = some gapState := by
    simpa [gapState, firstPC, quadHelperEntry, insertState,
      pairHelperEntry, roundWords, QuadGapTemplate.factor,
      QuadRoundTemplate.factor] using hgap

  have hgapRunning : gapState.halt = .Running := by
    simp [gapState, insertState, pairAfterHelperBeforeJump, hrun]

  have hcap (m : Nat) (hm : m ≤ 11) : rho.length + m < 1024 := by
    omega
  have hcap11 : rho.length + 11 < 1024 := by
    omega
  have hsecondPC : firstPC.add (UInt256.ofNat 1) = secondPC := by
    rfl
  have hswap1 (u v : UInt256) (tail : List UInt256) :
      (u :: v :: tail).exchange 0 1 = some (v :: u :: tail) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) tail

  have hswap : runInstrSeq [swap1] gapState = some pairState := by
    simp (config := { maxSteps := 3000000 })
      [gapState, pairState, afterFirstPair, firstWorking,
        quadFirstState, quadFirstWorking, insertState,
        pairAfterHelperBeforeJump, pairHelperEntry, roundWords,
        runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
        swap1, op, pcAfter, UInt256.succ, Instr.size,
        Instr.size_op, List.exchange, hrun, hcap, hcap11, hsecondPC,
        QuadGapTemplate.factor, QuadRoundTemplate.factor]

  have hpairRunning : pairState.halt = .Running := by
    simpa [pairState, afterFirstPair, quadFirstState, pairHelperEntry] using hrun

  have htail := QuadCachedTrace.cachedTail_of_pair_raw j hj
    afterFirstPair secondPC p2 p3 returnPC r2 r3 firstWorking constant rho
    hzero hstack hrun hrot2 hrot3
  have hsecond :
      runInstrSeq (cachedTailFTemplate j constant) pairState =
        some (quadAfterHelperBeforeJump s
          (pcAfter secondPC (cachedTailFTemplate j constant))
          returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
    simpa [pairState, afterFirstPair, firstWorking,
      quadAfterHelperBeforeJump, quadFirstState, quadFirstWorking,
      pairHelperEntry, QuadRoundTemplate.factor] using htail

  have hswapTail := runInstrSeq_append hswap hpairRunning hsecond
  have hpc :
      pcAfter startPC (quadBeforeJumpTemplate j constant) =
        pcAfter secondPC (cachedTailFTemplate j constant) := by
    calc
      pcAfter startPC (quadBeforeJumpTemplate j constant) =
          pcAfter (pcAfter startPC
            (firstFTemplate j constant ++ [swap1]))
            (cachedTailFTemplate j constant) := by
              rw [quadBeforeJumpTemplate, QuadRoundState.pcAfter_append]
      _ = pcAfter
            (pcAfter (pcAfter startPC (firstFTemplate j constant)) [swap1])
            (cachedTailFTemplate j constant) := by
              rw [QuadRoundState.pcAfter_append]
      _ = pcAfter (pcAfter startPC (firstFTemplate j constant))
            ([swap1] ++ cachedTailFTemplate j constant) := by
              rw [QuadRoundState.pcAfter_append]
      _ = pcAfter secondPC (cachedTailFTemplate j constant) := by
            rfl
  rw [← hpc] at hswapTail
  have hall := runInstrSeq_append hfirst hgapRunning hswapTail
  simpa [quadBeforeJumpTemplate, List.append_assoc,
    quadAfterHelperBeforeJump, quadWorking, quadFirstState,
    quadFirstWorking, firstWorking, afterFirstPair,
    QuadRoundTemplate.factor] using hall

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace
