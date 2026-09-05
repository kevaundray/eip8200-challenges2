import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# H30b cached-factor tail template

H30b keeps one factor word below the five left working words.  The tail
therefore uses the ten native DUP depths `4,9,6,11,2,12,3,13,4,9` and
removes eleven words before the final dynamic `JUMP`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailTemplate

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail

def factor : UInt256 := UInt256.ofNat 0x100000001

def tailStartPC : UInt256 := UInt256.ofNat 0x9a9
def tailJumpPC : UInt256 := UInt256.ofNat 0xa04

def dup4H : Instr := .op (.Dup ⟨3, by decide⟩)
def dup9H : Instr := .op (.Dup ⟨8, by decide⟩)
def dup6H : Instr := .op (.Dup ⟨5, by decide⟩)
def dup11H : Instr := .op (.Dup ⟨10, by decide⟩)
def dup2H : Instr := .op (.Dup ⟨1, by decide⟩)
def dup12H : Instr := .op (.Dup ⟨11, by decide⟩)
def dup3H : Instr := .op (.Dup ⟨2, by decide⟩)
def dup13H : Instr := .op (.Dup ⟨12, by decide⟩)

def c0Instructions : List Instr :=
  [ dup4H, dup9H,
    push1 (UInt256.ofNat 0x40), op .MLOAD, op .ADD, op .ADD,
    push4 mask, op .AND ]

def c1Instructions : List Instr :=
  [ dup6H, dup11H,
    push1 (UInt256.ofNat 0x60), op .MLOAD, op .ADD, op .ADD,
    push4 mask, op .AND,
    push1 (UInt256.ofNat 0x40), op .MSTORE ]

def c2Instructions : List Instr :=
  [ dup2H, dup12H,
    push1 (UInt256.ofNat 0x80), op .MLOAD, op .ADD, op .ADD,
    push4 mask, op .AND,
    push1 (UInt256.ofNat 0x60), op .MSTORE ]

def c3Instructions : List Instr :=
  [ dup3H, dup13H,
    push1 (UInt256.ofNat 0xa0), op .MLOAD, op .ADD, op .ADD,
    push4 mask, op .AND,
    push1 (UInt256.ofNat 0x80), op .MSTORE ]

def c4Instructions : List Instr :=
  [ dup4H, dup9H,
    push1 (UInt256.ofNat 0x20), op .MLOAD, op .ADD, op .ADD,
    push4 mask, op .AND,
    push1 (UInt256.ofNat 0xa0), op .MSTORE ]

def storeH0Instructions : List Instr :=
  [ push1 (UInt256.ofNat 0x20), op .MSTORE ]

def cleanupInstructions : List Instr :=
  [ op .POP, op .POP, op .POP, op .POP, op .POP,
    op .POP, op .POP, op .POP, op .POP, op .POP, op .POP ]

def quadTailBeforeJumpTemplate : List Instr :=
  c0Instructions ++ c1Instructions ++ c2Instructions ++ c3Instructions ++
    c4Instructions ++ storeH0Instructions ++ cleanupInstructions

def quadTailTemplate : List Instr :=
  quadTailBeforeJumpTemplate ++ [op .JUMP]

def workingStack (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [ right.a, right.b, right.c, right.d, right.e,
    factor, left.b, left.c, left.d, left.e, left.a, ret ] ++ rest

def tailEntry (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := tailStartPC
    stack := workingStack left right ret rest }

def beforeJumpResult (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) : State :=
  { StackTail.preJumpResult s left right ret rest with
    pc := tailJumpPC }

def finalResult (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) : State :=
  { beforeJumpResult s left right ret rest with
    pc := ret
    stack := rest }

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailTemplate
