import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

/-!
# Pure output observations

These definitions describe the five chaining-word slots.  They contain no
output opcode trace and can therefore be used by the compression interface.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.OutputTrace

open EvmSemantics
open EvmSemantics.EVM

def hOffset (i : Nat) : Nat := 0x20 + 32 * i

def hWord (s : State) (i : Nat) : UInt256 :=
  MachineState.readWord s.memory (hOffset i)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.OutputTrace
