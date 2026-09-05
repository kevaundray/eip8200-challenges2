import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScratchLow
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxRecDepth 30000

/-!
# H27 paired-round common states

This file contains only the shared call-stack states and the pure two-round
endpoint.  The evaluator proof is in `PairRoundTrace`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.ScratchLow
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate

/-- Instructions push `s1, p1, s0, return-PC, p0, helper-PC` in that order.
The resulting top-first stack is `[helper-PC, p0, return-PC, s0, p1, s1]`. -/
def pairCallPushes (returnPC p0 p1 helperPC : UInt256) (r0 r1 : Nat) : List Instr :=
  [push1 (UInt256.ofNat (32 - r1)), push2 p1,
    push1 (UInt256.ofNat (32 - r0)), push2 returnPC,
    push2 p0, push2 helperPC]

/-- State after the pair wrapper has pushed its six values. -/
def pairCallPushed (s : State) (pc returnPC p0 p1 helperPC : UInt256)
    (r0 r1 : Nat) (working : Compression.EvmWorking)
    (rest : List UInt256) : State :=
  { s with
    pc := pc
    stack := [helperPC, p0, returnPC, UInt256.ofNat (32 - r0), p1,
      UInt256.ofNat (32 - r1)] ++ roundWords working ++ rest }

/-- Helper-entry state.  `r0` and `r1` are passed as `32 - r0` and `32 - r1`. -/
def pairHelperEntry (s : State) (startPC p0 p1 returnPC : UInt256)
    (r0 r1 : Nat) (working : Compression.EvmWorking)
    (rest : List UInt256) : State :=
  { s with
    pc := startPC
    stack := [p0, returnPC, UInt256.ofNat (32 - r0), p1,
      UInt256.ofNat (32 - r1)] ++ roundWords working ++ rest }

/-- The pure endpoint of the pair helper: read `p0`, then `p1`. -/
def pairWorking (s : State) (working : Compression.EvmWorking) (j : Nat)
    (p0 p1 : UInt256) (r0 r1 : Nat) (constant : UInt256) :
    Compression.EvmWorking :=
  ScratchLow.rawRound
    (ScratchLow.rawRound working j (MachineState.readWord s.memory p0.toNat) r0 constant)
    j (MachineState.readWord s.memory p1.toNat) r1 constant

/-- State immediately before the helper's final `JUMP`. -/
def pairAfterHelperBeforeJump (s : State) (endPC returnPC : UInt256)
    (j : Nat) (working : Compression.EvmWorking) (p0 p1 : UInt256)
    (r0 r1 : Nat) (constant : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := endPC
    stack := returnPC :: roundWords
      (pairWorking s working j p0 p1 r0 r1 constant) ++ rest
    memory := s.memory
    activeWords := s.activeWordsAfterUInt256_2 p0.toNat 32 p1.toNat 32 }

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
