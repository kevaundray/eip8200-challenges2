import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputState

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactState

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputState

def referenceWord (input : ByteArray) : UInt256 :=
  MachineState.readWord input 0

def loopAcc (input : ByteArray) : Nat → UInt256
  | 0 => UInt256.xor (referenceWord input) KnownInputData.fullWord
  | n + 1 => UInt256.lor
      (UInt256.xor (MachineState.readWord input (32 * (n + 1)))
        (referenceWord input))
      (loopAcc input n)

def finalAcc (input : ByteArray) : UInt256 :=
  UInt256.lor
    (UInt256.xor
      (UInt256.shiftRight (MachineState.readWord input 992) (UInt256.ofNat 192))
      (UInt256.shiftRight (referenceWord input) (UInt256.ofNat 192)))
    (loopAcc input 30)

def loopState (s : State) (input : ByteArray) (i n : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x12f6
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n,
      referenceWord input, DriverTrace.messageOffsetWord i,
      UInt256.ofNat 0x436, DriverTrace.blockOffsetWord i,
      Padding.paddedWord input] }

def loopExitState (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x130b
    stack := [UInt256.ofNat 992, loopAcc input 30,
      referenceWord input, DriverTrace.messageOffsetWord i,
      UInt256.ofNat 0x436, DriverTrace.blockOffsetWord i,
      Padding.paddedWord input] }

def bodyEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x131f
    stack := [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x436,
      DriverTrace.blockOffsetWord i, Padding.paddedWord input] }

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactState
