import Challenge.EvmProof.Meter
import Challenge.Ripemd160.Submission.Bytecode
import Challenge.Ripemd160.Spec

set_option warningAsError true

/-!
# Exact gas schedule for the RIPEMD-160 reference

This file records the closed form measured for the frozen reference bytecode
and proves its arithmetic properties.  Memory expansion is kept as
`MachineState.memCost`, the same potential used by `Challenge.EvmProof.Meter`,
so a completed `GasSteps` trace can telescope its memory charges directly into
the final term below.

The remaining bytecode-specific obligation is deliberately isolated by
`gasSchedule_correct_of_trace`: the full execution proof must supply a trace
whose `cost` is `referenceGas input`.  No separate execution or gas model is
introduced here.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.GasCost

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

/-- Number of 64-byte compression blocks after RIPEMD-160 padding. -/
def blockCount (inputSize : Nat) : Nat := (inputSize + 72) / 64

/-- Number of words copied by `CALLDATACOPY`. -/
def calldataWords (inputSize : Nat) : Nat := (inputSize + 31) / 32

/-- Final memory high-water mark, in 32-byte words. Padding itself ends at
`64 + 2 * blockCount`; the final block's last schedule `MLOAD` reaches one
additional word. -/
def finalActiveWords (inputSize : Nat) : Nat := 65 + 2 * blockCount inputSize

/-- Exact gas consumed by the frozen RIPEMD-160 reference for `inputSize`
bytes of calldata. -/
def referenceGasForSize (inputSize : Nat) : Nat :=
  3698 + 120620 * blockCount inputSize + 3 * calldataWords inputSize +
    MachineState.memCost (finalActiveWords inputSize)

/-- Byte-array form of `referenceGasForSize`, convenient for execution traces. -/
def referenceGas (input : ByteArray) : Nat := referenceGasForSize input.size

@[simp] theorem blockCount_eq (inputSize : Nat) :
    blockCount inputSize = (inputSize + 72) / 64 := rfl

@[simp] theorem calldataWords_eq (inputSize : Nat) :
    calldataWords inputSize = (inputSize + 31) / 32 := rfl

@[simp] theorem finalActiveWords_eq (inputSize : Nat) :
    finalActiveWords inputSize = 65 + 2 * ((inputSize + 72) / 64) := rfl

/-- The schedule with the EVM memory-cost definition made explicit. -/
theorem referenceGasForSize_expanded (inputSize : Nat) :
    referenceGasForSize inputSize =
      3698 + 120620 * ((inputSize + 72) / 64) +
        3 * ((inputSize + 31) / 32) +
        (3 * (65 + 2 * ((inputSize + 72) / 64)) +
          (65 + 2 * ((inputSize + 72) / 64)) ^ 2 / 512) := by
  rfl

theorem blockCount_monotone : Monotone blockCount := by
  intro left right hle
  exact Nat.div_le_div_right (Nat.add_le_add_right hle 72)

theorem calldataWords_monotone : Monotone calldataWords := by
  intro left right hle
  exact Nat.div_le_div_right (Nat.add_le_add_right hle 31)

theorem finalActiveWords_monotone : Monotone finalActiveWords := by
  intro left right hle
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 (blockCount_monotone hle)) 65

/-- Larger calldata never makes the exact reference schedule smaller. -/
theorem referenceGasForSize_monotone : Monotone referenceGasForSize := by
  intro left right hle
  unfold referenceGasForSize
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add_left
        (Nat.mul_le_mul_left 120620 (blockCount_monotone hle)) 3698)
      (Nat.mul_le_mul_left 3 (calldataWords_monotone hle)))
    (Challenge.EvmProof.Meter.memCost_monotone
      (finalActiveWords_monotone hle))

/-! The scorer checkpoints are kernel-checked consequences of the formula. -/

@[simp] theorem referenceGasForSize_zero :
    referenceGasForSize 0 = 124527 := by decide

@[simp] theorem referenceGasForSize_three :
    referenceGasForSize 3 = 124530 := by decide

@[simp] theorem referenceGasForSize_55 :
    referenceGasForSize 55 = 124533 := by decide

@[simp] theorem referenceGasForSize_56 :
    referenceGasForSize 56 = 245160 := by decide

@[simp] theorem referenceGasForSize_64 :
    referenceGasForSize 64 = 245160 := by decide

@[simp] theorem referenceGasForSize_120 :
    referenceGasForSize 120 = 365792 := by decide

@[simp] theorem referenceGasForSize_256 :
    referenceGasForSize 256 = 607057 := by decide

/-- Boundary regression: here the corrected final high-water mark crosses a
memory-cost quotient boundary, so it distinguishes `65 + 2 * blocks` from
the padded-memory endpoint `64 + 2 * blocks`. -/
@[simp] theorem referenceGasForSize_376 :
    referenceGasForSize 376 = 848323 := by decide

@[simp] theorem referenceGasForSize_1000 :
    referenceGasForSize 1000 = 1934023 := by decide

/-- Schedule-level strengthening of the minimal challenge statement. -/
def CorrectWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  ∀ input : ByteArray, CalldataFits input → ∀ gas : Nat,
    schedule input.size ≤ gas →
    Eval (initialState code input gas) (.returned (spec input))

theorem correct_of_schedule {code : ByteArray} {schedule : Nat → Nat}
    (hcorrect : CorrectWithSchedule code schedule) : Correct code := by
  intro input hfit
  exact ⟨schedule input.size, fun gas hgas => hcorrect input hfit gas hgas⟩

@[simp] theorem withGas_initialState_zero
    (code input : ByteArray) (gas : Nat) :
    withGas (initialState code input 0) gas = initialState code input gas := by
  rfl

/--
Turn the completed functional `GasSteps` certificate into the exact gas
schedule theorem.  To close the gas proof for the reference, instantiate this
with the final halted state and the same full trace used for correctness, then
prove `hcost` by telescoping the per-block `Meter` potential equations.
-/
theorem gasSchedule_correct_of_trace
    (finalState : ∀ input : ByteArray, CalldataFits input → State)
    (fullTrace : ∀ (input : ByteArray) (hfit : CalldataFits input),
      GasSteps (initialState submissionBytecode input 0)
        (finalState input hfit))
    (hcost : ∀ (input : ByteArray) (hfit : CalldataFits input),
      (fullTrace input hfit).cost = referenceGas input)
    (hdone : ∀ (input : ByteArray) (hfit : CalldataFits input),
      (finalState input hfit).isDone = true)
    (hresult : ∀ (input : ByteArray) (hfit : CalldataFits input),
      (finalState input hfit).toResult = .returned (spec input)) :
    CorrectWithSchedule submissionBytecode referenceGasForSize := by
  intro input hfit gas hgas
  let trace := fullTrace input hfit
  have htraceCost : trace.cost = referenceGas input := hcost input hfit
  have hsteps : Steps (initialState submissionBytecode input gas)
      (withGas (finalState input hfit) (gas - referenceGas input)) := by
    have hs := trace.trace gas (by
      rw [htraceCost]
      exact hgas)
    simpa [trace, htraceCost] using hs
  have heval := Challenge.EvmProof.eval_of_steps hsteps (by
    change (finalState input hfit).isDone = true
    exact hdone input hfit)
  have hfinal :
      (withGas (finalState input hfit) (gas - referenceGas input)).toResult =
        .returned (spec input) := by
    change (finalState input hfit).toResult = .returned (spec input)
    exact hresult input hfit
  simpa [hfinal] using heval

end Challenge.Ripemd160.Submission.Proofs.Bytecode.GasCost
