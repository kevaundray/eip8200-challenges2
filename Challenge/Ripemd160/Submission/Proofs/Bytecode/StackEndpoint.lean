import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackBlockModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailTemplate

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackEndpoint

open EvmSemantics EvmSemantics.EVM
open StackBlockModel

def initialWorking (s : State) : Compression.EvmWorking :=
  CompressionCorrect.evmWorkingOfHash (StackMemory.hashAt s.memory)

def leftWorking (s : State) (input : ByteArray) (i : Nat) : Compression.EvmWorking :=
  StackCompression.leftRounds (blockWords input i) 80 (initialWorking s)

def rightWorking (s : State) (input : ByteArray) (i : Nat) : Compression.EvmWorking :=
  StackCompression.rightRounds (blockWords input i) 80 (initialWorking s)

theorem initialWorking_scheduled (s : State) (input : ByteArray) (i : Nat) :
    initialWorking (scheduledState s input i) = initialWorking s := by
  unfold initialWorking
  rw [scheduledState_hash]

theorem tailResult_eq_resultState (s : State) (input : ByteArray) (i : Nat) :
    StackTail.tailResult (scheduledState s input i)
      (leftWorking s input i) (rightWorking s input i)
      (UInt256.ofNat 0x436) (driverRest input i) = resultState s input i := by
  simp only [StackTail.tailResult, StackTail.preJumpResult, StackTail.combined,
    resultState, resultHash, StackCompression.compress, leftWorking, rightWorking,
    initialWorking, scheduledState_hash]

theorem quadTailResult_eq_resultState (s : State) (input : ByteArray) (i : Nat) :
    QuadTailTemplate.finalResult (scheduledState s input i)
      (leftWorking s input i) (rightWorking s input i)
      (UInt256.ofNat 0x436) (driverRest input i) = resultState s input i :=
  tailResult_eq_resultState s input i

theorem rightPC_last : QuadLayout.rightPC 20 = UInt256.ofNat 0x9a9 := by
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackEndpoint
