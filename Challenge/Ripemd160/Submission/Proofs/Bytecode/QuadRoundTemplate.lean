import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# H30b factor-cache templates

The cached-tail template is the H27 pair body after its leading `JUMPDEST`.
Its four factor literals are replaced by cache reads.  The cache is the final
suffix word `F = 0x100000001`; the operation order and every other
instruction are unchanged.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate

def factor : UInt256 := UInt256.ofNat 0x100000001

def cachedDup10 : Instr := .op (.Dup ⟨9, by decide⟩)
def cachedDup9 : Instr := .op (.Dup ⟨8, by decide⟩)
def cachedDup8 : Instr := .op (.Dup ⟨7, by decide⟩)
def cachedDup7 : Instr := .op (.Dup ⟨6, by decide⟩)

def cachedQrot10 : List Instr :=
  [cachedDup10, op .MUL, swap1, op .SHR]

def cachedCfold9 : List Instr :=
  [cachedDup9, op .MUL, push1 c22, op .SHR]

def cachedQrot8 : List Instr :=
  [cachedDup8, op .MUL, swap1, op .SHR]

def cachedCfold7 : List Instr :=
  [cachedDup7, op .MUL, push1 c22, op .SHR]

/-- The H27 pair body with its first `JUMPDEST` removed and the four factor
cache reads at depths 10, 9, 8, and 7. -/
def cachedTailFTemplate (j : Nat) (constant : UInt256) : List Instr :=
  [op .MLOAD] ++ pairFirstBooleanOps j ++
    [op .ADD, swap1, pairSwap5, op .ADD] ++
    (if j = 0 then [] else [push4 constant, op .ADD]) ++
    [push4 mask, op .AND] ++ cachedQrot10 ++
    [pairDup8, op .ADD, push4 mask, op .AND, pairSwap5] ++
    cachedCfold9 ++
    [swap1, op .MLOAD] ++ pairSecondBooleanOps j ++
    [op .ADD, swap1, pairSwap7, op .ADD] ++
    (if j = 0 then [] else [push4 constant, op .ADD]) ++
    [push4 mask, op .AND] ++ cachedQrot8 ++
    [dup5, op .ADD, push4 mask, op .AND, swap2] ++
    cachedCfold7 ++
    [swap4, swap1]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
