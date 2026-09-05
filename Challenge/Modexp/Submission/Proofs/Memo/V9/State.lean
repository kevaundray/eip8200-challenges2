import Challenge.Modexp.Submission.Proofs.Memo.Dispatch
import Challenge.Modexp.Submission.Proofs.Memo.V9.Data

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V9.State

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
  UInt256.xor (MachineState.readWord input 0) (32 : UInt256)

def chunk0 : List (Nat × UInt256) := (Data.checks.drop 1).take 4
def acc1 (input : ByteArray) : UInt256 := scanDiff input chunk0 (acc0 input)

def chunk1 : List (Nat × UInt256) := (Data.checks.drop 5).take 1
def acc2 (input : ByteArray) : UInt256 := scanDiff input chunk1 (acc1 input)

theorem acc2_eq_guardDiff (input : ByteArray) :
    acc2 input = guardDiff Data.checks input := by rfl

def storeWord (mem : ByteArray) (addr w : Nat) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w 32) addr

def answerMemory : ByteArray :=
  (storeWord ByteArray.empty 0 6720979588572738974916628410083100159223021409556719026881700545747062357561)

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 2455
      stack := [UInt256.ofNat input.size]
      memory := answerMemory
      activeWords := UInt256.ofNat 1
      halt := .Returned
      hReturn := MachineState.readPadded answerMemory 0 32 }

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = Precompile.natToBytes 6720979588572738974916628410083100159223021409556719026881700545747062357561 32 := by
  decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.V9.State
