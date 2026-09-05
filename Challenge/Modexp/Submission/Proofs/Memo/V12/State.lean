import Challenge.Modexp.Submission.Proofs.Memo.Dispatch
import Challenge.Modexp.Submission.Proofs.Memo.V12.Data

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V12.State

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
  UInt256.xor (MachineState.readWord input 0) (256 : UInt256)

def chunk0 : List (Nat × UInt256) := (Data.checks.drop 1).take 4
def acc1 (input : ByteArray) : UInt256 := scanDiff input chunk0 (acc0 input)

def chunk1 : List (Nat × UInt256) := (Data.checks.drop 5).take 4
def acc2 (input : ByteArray) : UInt256 := scanDiff input chunk1 (acc1 input)

def chunk2 : List (Nat × UInt256) := (Data.checks.drop 9).take 4
def acc3 (input : ByteArray) : UInt256 := scanDiff input chunk2 (acc2 input)

def chunk3 : List (Nat × UInt256) := (Data.checks.drop 13).take 4
def acc4 (input : ByteArray) : UInt256 := scanDiff input chunk3 (acc3 input)

def chunk4 : List (Nat × UInt256) := (Data.checks.drop 17).take 3
def acc5 (input : ByteArray) : UInt256 := scanDiff input chunk4 (acc4 input)

theorem acc5_eq_guardDiff (input : ByteArray) :
    acc5 input = guardDiff Data.checks input := by rfl

def storeWord (mem : ByteArray) (addr w : Nat) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w 32) addr

def answerMemory : ByteArray :=
  (storeWord (storeWord (storeWord (storeWord (storeWord (storeWord (storeWord (storeWord ByteArray.empty 0 36457779276215628618107628175862952880503802480134169461413915661242852128650) 32 87049543137291641647099327099349755118393366951315864702186066057471381150321) 64 100461675459921706400033383628344108228127659798054063115947067974792041444897) 96 92652640243433598898841338411780137466704615812747125847068622118856402577117) 128 14159211218075883537326960255904060289806489979180585240426546259839689087273) 160 67818750046613989747287612287447883644842343144736888277507620664030220336931) 192 2618339351906218248436954888076772231186051744572579598192995074227528865064) 224 9746032139171987504721760760529593857951721070820754662511731733855650243837)

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 4146
      stack := [UInt256.ofNat input.size]
      memory := answerMemory
      activeWords := UInt256.ofNat 8
      halt := .Returned
      hReturn := MachineState.readPadded answerMemory 0 256 }

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 256 = Precompile.natToBytes 10175187976799003886229376841442546105529699800513037093355123544449769318969642540840383490776397181808429855672853429775316140528665768493270715348029217220690467202280209540541263382232651033180684997960247073897954272511057998213243217004716460828951620297937453354508052345030452970177767339411315280803282979574538878784166510662602313902400517568304486112651676049389901503593119532036264719613000642629018880891900844394812652980986696612141326598921911290703686696602774502921196726245077035331181765161429492785838675554408626534822701799981363038379332427414960769534862483823724630851764021472042775012605 256 := by
  decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.V12.State
