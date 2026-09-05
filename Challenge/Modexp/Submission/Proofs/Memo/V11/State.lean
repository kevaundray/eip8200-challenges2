import Challenge.Modexp.Submission.Proofs.Memo.Dispatch
import Challenge.Modexp.Submission.Proofs.Memo.V11.Data

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V11.State

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
  UInt256.xor (MachineState.readWord input 0) (128 : UInt256)

def chunk0 : List (Nat × UInt256) := (Data.checks.drop 1).take 4
def acc1 (input : ByteArray) : UInt256 := scanDiff input chunk0 (acc0 input)

def chunk1 : List (Nat × UInt256) := (Data.checks.drop 5).take 4
def acc2 (input : ByteArray) : UInt256 := scanDiff input chunk1 (acc1 input)

def chunk2 : List (Nat × UInt256) := (Data.checks.drop 9).take 3
def acc3 (input : ByteArray) : UInt256 := scanDiff input chunk2 (acc2 input)

theorem acc3_eq_guardDiff (input : ByteArray) :
    acc3 input = guardDiff Data.checks input := by rfl

def storeWord (mem : ByteArray) (addr w : Nat) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w 32) addr

def answerMemory : ByteArray :=
  (storeWord (storeWord (storeWord (storeWord ByteArray.empty 0 15311000363910303241540621865409679537502595890653539278795210471371740305479) 32 108131171086235498843144070769070390205391711722934919355131028315980221287783) 64 30211351789909815513928503188859640991933128769084385520359151767836288201668) 96 19240783075872300903671752229116273808210541663683986574655295206487138977467)

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 3163
      stack := [UInt256.ofNat input.size]
      memory := answerMemory
      activeWords := UInt256.ofNat 4
      halt := .Returned
      hReturn := MachineState.readPadded answerMemory 0 128 }

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 128 = Precompile.natToBytes 23770605076193484263195166124334592080977119807923040521556739108343930992589618336259423983545745458292536349372840375414528764244723718450246108378351859526172607813519810780878561916692774266074304363890065613369945335106069602835754754045577840068119595317417408332086922232558327626521171657161026782907 128 := by
  decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.V11.State
