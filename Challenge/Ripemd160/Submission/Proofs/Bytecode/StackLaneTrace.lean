import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundCertificates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSelectRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackNegatedRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleActiveWords

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLaneTrace

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StackRoundData StackRoundTemplate StackRoundTrace

def stateAt (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (rest : List UInt256) : State :=
  roundEntry s pc w.a w.b w.c w.d w.e rest

def WordsAt (s : State) (word : Nat → UInt32) : Prop :=
  ∀ k, k < 16 → MachineState.readWord s.memory (672 + 32 * k) =
    Challenge.EvmProof.Word.ofUInt32 (word k)

def gasSteps_template (j : Nat) (hj : j < 5)
    (address : UInt256) (rotation : Nat) (constant : UInt256)
    (hzero : j = 0 → constant = 0)
    (site : GenericRoundSite Artifact.submissionArtifact .Osaka
      (template j address rotation constant))
    (s : State) (w : Compression.EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1015)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s site.startPC w rest)
      (roundReturned s site.endPC j w.a w.b w.c w.d w.e address rotation constant rest) := by
  interval_cases j
  · have hc := hzero rfl
    subst constant
    exact gasSteps_f0 address rotation site s w.a w.b w.c w.d w.e rest
      hstack hcode hfork hrun hnp
  · exact StackSelectRoundTrace.gasSteps_f1 address rotation constant site s
      w.a w.b w.c w.d w.e rest hstack hcode hfork hrun hnp
  · exact StackNegatedRoundTrace.gasSteps_f2 address rotation constant site s
      w.a w.b w.c w.d w.e rest hstack hcode hfork hrun hnp
  · exact StackSelectRoundTrace.gasSteps_f3 address rotation constant site s
      w.a w.b w.c w.d w.e rest hstack hcode hfork hrun hnp
  · exact StackNegatedRoundTrace.gasSteps_f4 address rotation constant site s
      w.a w.b w.c w.d w.e rest hstack hcode hfork hrun hnp

theorem returned_eq_stateAt (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (j : Nat) (address word constant : UInt256)
    (rotation : Nat) (rest : List UInt256)
    (hword : MachineState.readWord s.memory address.toNat = word)
    (hactive : s.activeWordsAfterUInt256 address.toNat 32 = s.activeWords) :
    roundReturned s pc j w.a w.b w.c w.d w.e address rotation constant rest =
      stateAt s pc (StackRound.stackRound w j word rotation constant) rest := by
  simp only [roundReturned, roundResult, roundWorking, roundWord, hword, hactive,
    stateAt, roundEntry, roundWords]

private theorem leftIndex_lt (i : Fin 80) : Crypto.Ripemd160.r[i.val]! < 16 := by
  fin_cases i <;> decide

theorem leftAddress_toNat (i : Fin 80) :
    (leftAddress i.val).toNat = 672 + 32 * Crypto.Ripemd160.r[i.val]! := by
  have hk := leftIndex_lt i
  unfold leftAddress
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

def gasSteps_leftStep (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (rest : List UInt256) (i : Fin 80)
    (hwords : WordsAt s word) (hactive : 67 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1013)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (StackSites.leftPC i.val) w rest)
      (stateAt s (StackSites.leftPC (i.val + 1))
        (StackCompression.leftStep word i.val w) rest) := by
  have hw : MachineState.readWord s.memory (leftAddress i.val).toNat =
      Challenge.EvmProof.Word.ofUInt32 (word (Crypto.Ripemd160.r[i.val]!)) := by
    rw [leftAddress_toNat i]
    exact hwords _ (leftIndex_lt i)
  have ha : s.activeWordsAfterUInt256 (leftAddress i.val).toNat 32 = s.activeWords := by
    apply ScheduleActiveWords.activeWordsAfterUInt256_eq
    rw [leftAddress_toNat i]
    have hk := leftIndex_lt i
    omega
  have g := SharedRoundCertificates.gasSteps_leftRound s w rest i hstack hcode hfork hrun hnp
  rw [returned_eq_stateAt s _ w _ _ _ _ _ rest hw ha] at g
  simpa only [stateAt, StackCompression.leftStep, leftRotation, leftConstant] using g

def gasSteps_left80 (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (rest : List UInt256)
    (hwords : WordsAt s word) (hactive : 67 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1013)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (StackSites.leftPC 0) w rest)
      (stateAt s (StackSites.leftPC 80) (StackCompression.leftRounds word 80 w) rest) := by
  let states := fun n => stateAt s (StackSites.leftPC n)
    (StackCompression.leftRounds word n w) rest
  have step (i : Nat) (hi : i < 80) : GasSteps (states i) (states (i + 1)) := by
    exact gasSteps_leftStep s word (StackCompression.leftRounds word i w)
      rest ⟨i, hi⟩ hwords hactive hstack hcode hfork hrun hnp
  exact GasSteps.iterateBounded 80 step

private theorem rightIndex_lt (i : Fin 80) : Crypto.Ripemd160.rP[i.val]! < 16 := by
  fin_cases i <;> decide

theorem rightAddress_toNat (i : Fin 80) :
    (rightAddress i.val).toNat = 672 + 32 * Crypto.Ripemd160.rP[i.val]! := by
  have hk := rightIndex_lt i
  unfold rightAddress
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

def gasSteps_rightStep (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (rest : List UInt256) (i : Fin 80)
    (hwords : WordsAt s word) (hactive : 67 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1013)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (StackSites.rightPC i.val) w rest)
      (stateAt s (StackSites.rightPC (i.val + 1))
        (StackCompression.rightStep word i.val w) rest) := by
  have hw : MachineState.readWord s.memory (rightAddress i.val).toNat =
      Challenge.EvmProof.Word.ofUInt32 (word (Crypto.Ripemd160.rP[i.val]!)) := by
    rw [rightAddress_toNat i]
    exact hwords _ (rightIndex_lt i)
  have ha : s.activeWordsAfterUInt256 (rightAddress i.val).toNat 32 = s.activeWords := by
    apply ScheduleActiveWords.activeWordsAfterUInt256_eq
    rw [rightAddress_toNat i]
    have hk := rightIndex_lt i
    omega
  have g := SharedRoundCertificates.gasSteps_rightRound s w rest i hstack hcode hfork hrun hnp
  rw [returned_eq_stateAt s _ w _ _ _ _ _ rest hw ha] at g
  simpa only [stateAt, StackCompression.rightStep, rightRotation, rightConstant] using g

def gasSteps_right80 (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (rest : List UInt256)
    (hwords : WordsAt s word) (hactive : 67 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1013)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (StackSites.rightPC 0) w rest)
      (stateAt s (StackSites.rightPC 80) (StackCompression.rightRounds word 80 w) rest) := by
  let states := fun n => stateAt s (StackSites.rightPC n)
    (StackCompression.rightRounds word n w) rest
  have step (i : Nat) (hi : i < 80) : GasSteps (states i) (states (i + 1)) := by
    exact gasSteps_rightStep s word (StackCompression.rightRounds word i w)
      rest ⟨i, hi⟩ hwords hactive hstack hcode hfork hrun hnp
  exact GasSteps.iterateBounded 80 step

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLaneTrace
