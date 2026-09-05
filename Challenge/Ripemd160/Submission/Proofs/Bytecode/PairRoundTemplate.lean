import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
import YulEvmCompiler.Instr

set_option warningAsError true
set_option maxRecDepth 30000

/-!
# H27 paired round helper templates

The pair helper receives
`[p0, return-PC, 32 - r0, p1, 32 - r1, A, B, C, D, E]`.
The final `JUMP` is outside the before-jump template.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

def pairDup7 : Instr := .op (.Dup ⟨6, by decide⟩)
def pairDup8 : Instr := .op (.Dup ⟨7, by decide⟩)
def pairDup9 : Instr := .op (.Dup ⟨8, by decide⟩)
def pairDup10 : Instr := .op (.Dup ⟨9, by decide⟩)

def pairSwap5 : Instr := .op (.Swap ⟨4, by decide⟩)
def pairSwap6 : Instr := .op (.Swap ⟨5, by decide⟩)
def pairSwap7 : Instr := .op (.Swap ⟨6, by decide⟩)

def qrot : List Instr :=
  [.push ⟨5, by decide⟩ (UInt256.ofNat 0x0100000001), op .MUL, swap1, op .SHR]

def cfold : List Instr :=
  [.push ⟨5, by decide⟩ (UInt256.ofNat 0x0100000001), op .MUL,
    push1 c22, op .SHR]

/-! The first round has the H22 Boolean depths increased by two. -/
def pairFirstBooleanOps (j : Nat) : List Instr :=
  match j with
  | 0 => [pairDup7, pairDup9, op .XOR, pairDup10, op .XOR]
  | 1 => [pairDup8, pairDup10, op .XOR, pairDup8, op .AND,
      pairDup10, op .XOR]
  | 2 => [pairDup8, op .NOT, pairDup8, op .OR, pairDup10, op .XOR]
  | 3 => [pairDup7, pairDup9, op .XOR, pairDup10, op .AND,
      pairDup9, op .XOR]
  | _ => [pairDup9, op .NOT, pairDup9, op .OR, pairDup8, op .XOR]

/-! Boolean depths for the second round after the first round's fold. -/
def pairSecondBooleanOps (j : Nat) : List Instr :=
  match j with
  | 0 => [dup6, dup6, op .XOR, dup3, op .XOR]
  | 1 => [dup5, dup3, op .XOR, pairDup7, op .AND, dup3, op .XOR]
  | 2 => [dup5, op .NOT, pairDup7, op .OR, dup3, op .XOR]
  | 3 => [dup6, dup6, op .XOR, dup3, op .AND, dup6, op .XOR]
  | _ => [dup2, op .NOT, dup6, op .OR, pairDup7, op .XOR]

def pairBeforeJumpTemplate (j : Nat) (constant : UInt256) : List Instr :=
  [op .JUMPDEST, op .MLOAD] ++ pairFirstBooleanOps j ++
    [op .ADD, swap1, pairSwap5, op .ADD] ++
    (if j = 0 then [] else [push4 constant, op .ADD]) ++
    [push4 mask, op .AND] ++ qrot ++
    [pairDup8, op .ADD, push4 mask, op .AND, pairSwap5] ++ cfold ++
    [swap1, op .MLOAD] ++ pairSecondBooleanOps j ++
    [op .ADD, swap1, pairSwap7, op .ADD] ++
    (if j = 0 then [] else [push4 constant, op .ADD]) ++
    [push4 mask, op .AND] ++ qrot ++
    [dup5, op .ADD, push4 mask, op .AND, swap2] ++ cfold ++
    [swap4, swap1]

def pairTemplate (j : Nat) (constant : UInt256) : List Instr :=
  pairBeforeJumpTemplate j constant ++ [op .JUMP]

@[simp] theorem pairBeforeJumpTemplate_length_0 (constant : UInt256) :
    (pairBeforeJumpTemplate 0 constant).length = 54 := by
  rfl

@[simp] theorem pairBeforeJumpTemplate_length_1 (constant : UInt256) :
    (pairBeforeJumpTemplate 1 constant).length = 62 := by
  rfl

@[simp] theorem pairBeforeJumpTemplate_length_2 (constant : UInt256) :
    (pairBeforeJumpTemplate 2 constant).length = 60 := by
  rfl

@[simp] theorem pairBeforeJumpTemplate_length_3 (constant : UInt256) :
    (pairBeforeJumpTemplate 3 constant).length = 62 := by
  rfl

@[simp] theorem pairBeforeJumpTemplate_length_4 (constant : UInt256) :
    (pairBeforeJumpTemplate 4 constant).length = 60 := by
  rfl

@[simp] theorem pairTemplate_length_0 (constant : UInt256) :
    (pairTemplate 0 constant).length = 55 := by
  rw [pairTemplate, List.length_append,
    pairBeforeJumpTemplate_length_0]
  rfl

@[simp] theorem pairTemplate_length_1 (constant : UInt256) :
    (pairTemplate 1 constant).length = 63 := by
  rw [pairTemplate, List.length_append,
    pairBeforeJumpTemplate_length_1]
  rfl

@[simp] theorem pairTemplate_length_2 (constant : UInt256) :
    (pairTemplate 2 constant).length = 61 := by
  rw [pairTemplate, List.length_append,
    pairBeforeJumpTemplate_length_2]
  rfl

@[simp] theorem pairTemplate_length_3 (constant : UInt256) :
    (pairTemplate 3 constant).length = 63 := by
  rw [pairTemplate, List.length_append,
    pairBeforeJumpTemplate_length_3]
  rfl

@[simp] theorem pairTemplate_length_4 (constant : UInt256) :
    (pairTemplate 4 constant).length = 61 := by
  rw [pairTemplate, List.length_append,
    pairBeforeJumpTemplate_length_4]
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
