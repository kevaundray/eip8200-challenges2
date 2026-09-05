import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundCertificates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

/-!
# H24 paired-round lane

The lane repeats forty paired wrappers.  It keeps the old lane invariants but
uses only the H24 paired site and certificate modules.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairLane

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundCertificates
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

def stateAt (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (rest : List UInt256) : State :=
  roundEntry s pc w.a w.b w.c w.d w.e rest

def WordsAt (s : State) (word : Nat → UInt32) : Prop :=
  ∀ k, k < 16 → Challenge.EvmProof.Word.toUInt32
    (MachineState.readWord s.memory (644 + 4 * k)) = word k

theorem stateAt_words (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (rest : List UInt256) (word : Nat → UInt32) (hwords : WordsAt s word) :
    WordsAt (stateAt s pc w rest) word := by
  intro k hk
  simpa [stateAt, roundEntry] using hwords k hk

theorem stateAt_activeWords (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (rest : List UInt256) :
    (stateAt s pc w rest).activeWords = s.activeWords := by
  rfl

private theorem leftRounds_pair (word : Nat → UInt32) (i : Nat)
    (working : Compression.EvmWorking) :
    StackCompression.leftRounds word (2 * (i + 1)) working =
      StackCompression.leftStep word (2 * i + 1)
        (StackCompression.leftStep word (2 * i)
          (StackCompression.leftRounds word (2 * i) working)) := by
  have h1 : 2 * (i + 1) = (2 * i + 1) + 1 := by omega
  rw [h1]
  simp only [StackCompression.leftRounds]

private theorem rightRounds_pair (word : Nat → UInt32) (i : Nat)
    (working : Compression.EvmWorking) :
    StackCompression.rightRounds word (2 * (i + 1)) working =
      StackCompression.rightStep word (2 * i + 1)
        (StackCompression.rightStep word (2 * i)
          (StackCompression.rightRounds word (2 * i) working)) := by
  have h1 : 2 * (i + 1) = (2 * i + 1) + 1 := by omega
  rw [h1]
  simp only [StackCompression.rightRounds]

def gasSteps_left80 (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (rest : List UInt256)
    (hwords : WordsAt s word) (hactive : 67 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (PairSites.leftPC 0) w rest)
      (stateAt s (PairSites.leftPC 40)
        (StackCompression.leftRounds word 80 w) rest) := by
  let states := fun n => stateAt s (PairSites.leftPC n)
    (StackCompression.leftRounds word (2 * n) w) rest
  have step (i : Nat) (hi : i < 40) : GasSteps (states i) (states (i + 1)) := by
    let k : Fin 40 := ⟨i, hi⟩
    have g := PairRoundCertificates.gasSteps_leftPair s word
      (StackCompression.leftRounds word (2 * i) w) rest k
      (fun n hn => hwords n hn) hactive hstack hcode hfork hrun hnp
    have hnext :
        StackCompression.leftRounds word (2 * (i + 1)) w =
          PairRoundCertificates.purePairWorking s
            (StackCompression.leftRounds word (2 * i) w) (k.val / 8)
            (PairSites.leftAddress0 k) (PairSites.leftAddress1 k)
            (PairSites.leftRotation0 k) (PairSites.leftRotation1 k)
            (PairSites.leftConstant k) := by
      rw [PairRoundCertificates.purePairWorking_left s word
        (StackCompression.leftRounds word (2 * i) w) k
        (fun n hn => hwords n hn)]
      exact leftRounds_pair word i w
    apply g.cast
    · rfl
    · simp only [states, stateAt, roundEntry, roundWords, k]
      rw [hnext]
  have g := GasSteps.iterateBounded 40 step
  simpa only [states, Nat.mul_zero, StackCompression.leftRounds] using g

def gasSteps_right80 (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (rest : List UInt256)
    (hwords : WordsAt s word) (hactive : 67 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (PairSites.rightPC 0) w rest)
      (stateAt s (PairSites.rightPC 40)
        (StackCompression.rightRounds word 80 w) rest) := by
  let states := fun n => stateAt s (PairSites.rightPC n)
    (StackCompression.rightRounds word (2 * n) w) rest
  have step (i : Nat) (hi : i < 40) : GasSteps (states i) (states (i + 1)) := by
    let k : Fin 40 := ⟨i, hi⟩
    have g := PairRoundCertificates.gasSteps_rightPair s word
      (StackCompression.rightRounds word (2 * i) w) rest k
      (fun n hn => hwords n hn) hactive hstack hcode hfork hrun hnp
    have hnext :
        StackCompression.rightRounds word (2 * (i + 1)) w =
          PairRoundCertificates.purePairWorking s
            (StackCompression.rightRounds word (2 * i) w) (4 - k.val / 8)
            (PairSites.rightAddress0 k) (PairSites.rightAddress1 k)
            (PairSites.rightRotation0 k) (PairSites.rightRotation1 k)
            (PairSites.rightConstant k) := by
      rw [PairRoundCertificates.purePairWorking_right s word
        (StackCompression.rightRounds word (2 * i) w) k
        (fun n hn => hwords n hn)]
      exact rightRounds_pair word i w
    apply g.cast
    · rfl
    · simp only [states, stateAt, roundEntry, roundWords, k]
      rw [hnext]
  have g := GasSteps.iterateBounded 40 step
  simpa only [states, Nat.mul_zero, StackCompression.rightRounds] using g

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairLane
