import Challenge.Modexp.Submission.Proofs.Memo.Dispatch
import Challenge.Modexp.Submission.Proofs.Memo.V2.Data

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V2.State

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo
open Logic

def accState (input : ByteArray) (pc : Nat) (acc : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat pc
      stack := [acc, UInt256.ofNat input.size] }

def acc0 (input : ByteArray) : UInt256 :=
  UInt256.xor (MachineState.readWord input 0) (1 : UInt256)

def chunk0 : List (Nat × UInt256) := (Data.checks.drop 1).take 3
def acc1 (input : ByteArray) : UInt256 := scanDiff input chunk0 (acc0 input)

theorem acc1_eq_guardDiff (input : ByteArray) :
    acc1 input = guardDiff Data.checks input := by rfl

def storeWord (mem : ByteArray) (addr w : Nat) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w 32) addr

def answerMemory : ByteArray :=
  (storeWord ByteArray.empty 0 1)

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1566
      stack := [UInt256.ofNat input.size]
      memory := answerMemory
      activeWords := UInt256.ofNat 1
      halt := .Returned
      hReturn := MachineState.readPadded answerMemory 31 1 }

theorem answerMemory_read :
    MachineState.readPadded answerMemory 31 1 = Precompile.natToBytes 1 1 := by
  decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.V2.State
