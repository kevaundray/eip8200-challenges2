import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate

set_option warningAsError true
set_option maxRecDepth 30000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTemplate

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTemplate

def d (index : Fin 16) : Instr := .op (.Dup ⟨index⟩)
def w (index : Fin 16) : Instr := .op (.Swap ⟨index⟩)
def factor : UInt256 := UInt256.ofNat 0x100000001

-- Four future control words remain between the current controls and working words.
def firstBoolean (j : Nat) : List Instr :=
  match j with
  | 0 => [d 10, d 12, op .XOR, d 13, op .XOR]
  | 1 => [d 11, d 13, op .XOR, d 11, op .AND, d 13, op .XOR]
  | 2 => [d 11, op .NOT, d 11, op .OR, d 13, op .XOR]
  | 3 => [d 10, d 12, op .XOR, d 13, op .AND, d 12, op .XOR]
  | _ => [d 12, op .NOT, d 12, op .OR, d 11, op .XOR]

def secondBoolean (j : Nat) : List Instr :=
  match j with
  | 0 => [d 9, d 9, op .XOR, d 2, op .XOR]
  | 1 => [d 8, d 2, op .XOR, d 10, op .AND, d 2, op .XOR]
  | 2 => [d 8, op .NOT, d 10, op .OR, d 2, op .XOR]
  | 3 => [d 9, d 9, op .XOR, d 2, op .AND, d 9, op .XOR]
  | _ => [d 1, op .NOT, d 9, op .OR, d 10, op .XOR]

def firstFTemplate (j : Nat) (constant : UInt256) : List Instr :=
  [op .JUMPDEST, op .MLOAD] ++ firstBoolean j ++
    [op .ADD, w 0, w 8, op .ADD] ++
    (if j = 0 then [] else [push4 constant, op .ADD]) ++
    [push4 mask, op .AND, d 13, op .MUL, w 0, op .SHR,
     d 11, op .ADD, push4 mask, op .AND, w 8,
     d 12, op .MUL, push1 c22, op .SHR, w 0, op .MLOAD] ++
    secondBoolean j ++ [op .ADD, w 0, w 10, op .ADD] ++
    (if j = 0 then [] else [push4 constant, op .ADD]) ++
    [push4 mask, op .AND, d 11, op .MUL, w 0, op .SHR,
     d 8, op .ADD, push4 mask, op .AND, w 5,
     d 10, op .MUL, push1 c22, op .SHR, w 7, w 4]

@[simp] theorem firstFTemplate_length_0 (constant : UInt256) :
    (firstFTemplate 0 constant).length = 54 := by rfl
@[simp] theorem firstFTemplate_length_1 (constant : UInt256) :
    (firstFTemplate 1 constant).length = 62 := by rfl
@[simp] theorem firstFTemplate_length_2 (constant : UInt256) :
    (firstFTemplate 2 constant).length = 60 := by rfl
@[simp] theorem firstFTemplate_length_3 (constant : UInt256) :
    (firstFTemplate 3 constant).length = 62 := by rfl
@[simp] theorem firstFTemplate_length_4 (constant : UInt256) :
    (firstFTemplate 4 constant).length = 60 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTemplate
