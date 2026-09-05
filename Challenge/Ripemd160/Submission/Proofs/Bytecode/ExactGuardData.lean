import Challenge.EvmProof.Bytes
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputData

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

/-!
# Exact-guard data for the public `1000 a's` scoring vector

The last `CALLDATALOAD` starts at byte 992, so its low 24 bytes are the EVM's
zero padding rather than calldata.  Keeping that padded word explicit makes the
data usable directly by a bytecode trace.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardData

open EvmSemantics
open EvmSemantics.EVM

/-- The public scoring input consisting of one thousand ASCII `a` bytes. -/
def targetInput : ByteArray :=
  ByteArray.mk (Array.replicate 1000 (0x61 : UInt8))

/-- A complete 32-byte chunk of the target calldata. -/
def fullWord : UInt256 :=
  0x6161616161616161616161616161616161616161616161616161616161616161

/-- The final eight `a` bytes followed by 24 bytes of `CALLDATALOAD` padding. -/
def tailWord : UInt256 :=
  0x6161616161616161000000000000000000000000000000000000000000000000

/-- The expected padded word at a block index in the 32-word guard. -/
def expectedWord (block : Nat) : UInt256 :=
  if block < 31 then fullWord else tailWord

/-- All 32 word checks, covering offsets 0, 32, ..., 992. -/
def checks : List (Nat × UInt256) :=
  (List.range 32).map (fun block => (32 * block, expectedWord block))

@[simp] theorem targetInput_size : targetInput.size = 1000 := by decide

theorem checks_length : checks.length = 32 := by decide

theorem check_mem (block : Nat) (hblock : block < 32) :
    (32 * block, expectedWord block) ∈ checks := by
  rw [checks]
  apply List.mem_map.mpr
  exact ⟨block, List.mem_range.mpr hblock, rfl⟩

/-- The hardcoded guard words are exactly the target input's padded reads. -/
theorem targetInput_readWord (block : Nat) (hblock : block < 32) :
    MachineState.readWord targetInput (32 * block) = expectedWord block := by
  exact KnownInputData.targetInput_readWord block hblock

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardData
