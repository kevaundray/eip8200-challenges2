import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleTrace

set_option warningAsError true
set_option maxRecDepth 30000

/-!
# H30b four-round raw state interfaces

The quad helper is the H30b gap followed by one stack swap and the cached
second pair tail.  This file contains only its template, entry, working, and
endpoint states plus the generic sequence-composition lemma.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate

def quadBeforeJumpTemplate (j : Nat) (constant : UInt256) : List Instr :=
  firstFTemplate j constant ++ [swap1] ++ cachedTailFTemplate j constant

def quadHelperEntry (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (rho : List UInt256) : State :=
  { s with
    pc := startPC
    stack := [p0, returnPC, UInt256.ofNat (32 - r0), p1,
      UInt256.ofNat (32 - r1), p2, UInt256.ofNat (32 - r2), p3,
      UInt256.ofNat (32 - r3)] ++ roundWords working ++
      [QuadRoundTemplate.factor] ++ rho }

def quadFirstWorking (s : State) (working : Compression.EvmWorking)
    (j : Nat) (p0 p1 : UInt256) (r0 r1 : Nat) (constant : UInt256) :
    Compression.EvmWorking :=
  pairWorking s working j p0 p1 r0 r1 constant

def quadFirstState (s : State) (p0 p1 : UInt256) : State :=
  {s with activeWords :=
    (s.activeWordsAfterUInt256_2 p0.toNat 32 p1.toNat 32)}

def quadWorking (s : State) (working : Compression.EvmWorking) (j : Nat)
    (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256) : Compression.EvmWorking :=
  pairWorking (quadFirstState s p0 p1)
    (quadFirstWorking s working j p0 p1 r0 r1 constant)
    j p2 p3 r2 r3 constant

def quadActiveWordsAfterUInt256_4 (s : State)
    (p0 p1 p2 p3 : Nat) : UInt256 :=
  let afterFirstPair : State :=
    {s with activeWords := s.activeWordsAfterUInt256_2 p0 32 p1 32}
  afterFirstPair.activeWordsAfterUInt256_2 p2 32 p3 32

def quadAfterHelperBeforeJump (s : State) (endPC returnPC : UInt256)
    (j : Nat) (working : Compression.EvmWorking)
    (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256) (rho : List UInt256) : State :=
  pairAfterHelperBeforeJump (quadFirstState s p0 p1) endPC returnPC j
    (quadFirstWorking s working j p0 p1 r0 r1 constant)
    p2 p3 r2 r3 constant (QuadRoundTemplate.factor :: rho)

theorem runInstrSeq_append
    {first second : List Instr} {s middle result : State}
    (hfirst : runInstrSeq first s = some middle)
    (hmiddle : middle.halt = .Running)
    (hsecond : runInstrSeq second middle = some result) :
    runInstrSeq (first ++ second) s = some result := by
  exact PackedScheduleTrace.runInstrSeq_append_running hfirst hmiddle hsecond

theorem pcAfter_append (pc : UInt256) (first second : List Instr) :
    pcAfter pc (first ++ second) = pcAfter (pcAfter pc first) second := by
  exact PackedScheduleTrace.pcAfter_append pc first second

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
