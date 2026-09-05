import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
import Challenge.EvmProof.Stepper
import YulEvmCompiler.Instr

set_option warningAsError true
set_option maxRecDepth 30000

/-!
# H10 direct stack-round templates

The H10 compressor emits one straight-line instruction template for each
Boolean form.  This file keeps the templates independent of a concrete
artifact.  A `GenericRoundSite` supplies the instruction lookup and the
instruction-boundary PC facts for one concrete occurrence.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof

abbrev Located (artifact : ProgramArtifact) (fork : Fork) :=
  Challenge.EvmProof.Stepper.Located artifact fork

def op (o : Operation) : Instr := .op o

def push0 : Instr := .push ⟨0, by decide⟩ (UInt256.ofNat 0)

def push1 (value : UInt256) : Instr :=
  .push ⟨1, by decide⟩ value

def push2 (value : UInt256) : Instr :=
  .push ⟨2, by decide⟩ value

def push4 (value : UInt256) : Instr :=
  .push ⟨4, by decide⟩ value

def dup1 : Instr := .op (.Dup ⟨0, by decide⟩)
def dup2 : Instr := .op (.Dup ⟨1, by decide⟩)
def dup3 : Instr := .op (.Dup ⟨2, by decide⟩)
def dup4 : Instr := .op (.Dup ⟨3, by decide⟩)
def dup5 : Instr := .op (.Dup ⟨4, by decide⟩)
def dup6 : Instr := .op (.Dup ⟨5, by decide⟩)

def swap1 : Instr := .op (.Swap ⟨0, by decide⟩)
def swap2 : Instr := .op (.Swap ⟨1, by decide⟩)
def swap3 : Instr := .op (.Swap ⟨2, by decide⟩)
def swap4 : Instr := .op (.Swap ⟨3, by decide⟩)

def mask : UInt256 := UInt256.ofNat 0xffffffff

def c10 : UInt256 := UInt256.ofNat 10
def c22 : UInt256 := UInt256.ofNat 22

/-! ## Instruction templates -/

def f0Template (xAddress : UInt256) (rotation : Nat) : List Instr :=
  [ dup2, dup4, op .XOR, dup5, op .XOR,
    op .ADD, push2 xAddress, op .MLOAD, op .ADD,
    push4 mask, op .AND,
    dup1, push1 (UInt256.ofNat rotation), op .SHL,
    dup2, push1 (UInt256.ofNat (32 - rotation)), op .SHR,
    op .OR, dup6, op .ADD, push4 mask, op .AND,
    swap1, op .POP,
    dup3, dup1, push1 c10, op .SHL,
    dup2, push1 c22, op .SHR, op .OR,
    swap1, op .POP, push4 mask, op .AND,
    swap1, swap2, swap3, op .POP, swap3, swap4 ]

def f1Template (xAddress : UInt256) (rotation : Nat) (constant : UInt256) : List Instr :=
  [ dup3, dup5, op .XOR, dup3, op .AND, dup5, op .XOR,
    op .ADD, push2 xAddress, op .MLOAD, op .ADD, push4 constant, op .ADD,
    push4 mask, op .AND,
    dup1, push1 (UInt256.ofNat rotation), op .SHL,
    dup2, push1 (UInt256.ofNat (32 - rotation)), op .SHR,
    op .OR, dup6, op .ADD, push4 mask, op .AND,
    swap1, op .POP,
    dup3, dup1, push1 c10, op .SHL,
    dup2, push1 c22, op .SHR, op .OR,
    swap1, op .POP, push4 mask, op .AND,
    swap1, swap2, swap3, op .POP, swap3, swap4 ]

def f2Template (xAddress : UInt256) (rotation : Nat) (constant : UInt256) : List Instr :=
  [ dup3, op .NOT, dup3, op .OR, dup5, op .XOR,
    push4 mask, op .AND,
    op .ADD, push2 xAddress, op .MLOAD, op .ADD, push4 constant, op .ADD,
    push4 mask, op .AND,
    dup1, push1 (UInt256.ofNat rotation), op .SHL,
    dup2, push1 (UInt256.ofNat (32 - rotation)), op .SHR,
    op .OR, dup6, op .ADD, push4 mask, op .AND,
    swap1, op .POP,
    dup3, dup1, push1 c10, op .SHL,
    dup2, push1 c22, op .SHR, op .OR,
    swap1, op .POP, push4 mask, op .AND,
    swap1, swap2, swap3, op .POP, swap3, swap4 ]

def f3Template (xAddress : UInt256) (rotation : Nat) (constant : UInt256) : List Instr :=
  [ dup2, dup4, op .XOR, dup5, op .AND, dup4, op .XOR,
    op .ADD, push2 xAddress, op .MLOAD, op .ADD, push4 constant, op .ADD,
    push4 mask, op .AND,
    dup1, push1 (UInt256.ofNat rotation), op .SHL,
    dup2, push1 (UInt256.ofNat (32 - rotation)), op .SHR,
    op .OR, dup6, op .ADD, push4 mask, op .AND,
    swap1, op .POP,
    dup3, dup1, push1 c10, op .SHL,
    dup2, push1 c22, op .SHR, op .OR,
    swap1, op .POP, push4 mask, op .AND,
    swap1, swap2, swap3, op .POP, swap3, swap4 ]

def f4Template (xAddress : UInt256) (rotation : Nat) (constant : UInt256) : List Instr :=
  [ dup4, op .NOT, dup4, op .OR, dup3, op .XOR,
    push4 mask, op .AND,
    op .ADD, push2 xAddress, op .MLOAD, op .ADD, push4 constant, op .ADD,
    push4 mask, op .AND,
    dup1, push1 (UInt256.ofNat rotation), op .SHL,
    dup2, push1 (UInt256.ofNat (32 - rotation)), op .SHR,
    op .OR, dup6, op .ADD, push4 mask, op .AND,
    swap1, op .POP,
    dup3, dup1, push1 c10, op .SHL,
    dup2, push1 c22, op .SHR, op .OR,
    swap1, op .POP, push4 mask, op .AND,
    swap1, swap2, swap3, op .POP, swap3, swap4 ]

inductive StraightLine : Instr → Prop where
  | push (width : Fin 33) (value : UInt256) : StraightLine (.push width value)
  | add : StraightLine (.op .ADD)
  | and : StraightLine (.op .AND)
  | or : StraightLine (.op .OR)
  | xor : StraightLine (.op .XOR)
  | not : StraightLine (.op .NOT)
  | shl : StraightLine (.op .SHL)
  | shr : StraightLine (.op .SHR)
  | pop : StraightLine (.op .POP)
  | mload : StraightLine (.op .MLOAD)
  | dup (operation : Operation.DupOp) : StraightLine (.op (.Dup operation))
  | swap (operation : Operation.SwapOp) : StraightLine (.op (.Swap operation))

theorem f0Template_straight (xAddress : UInt256) (rotation : Nat) :
  ∀ instruction ∈ f0Template xAddress rotation, StraightLine instruction := by
  intro instruction hmem
  simp only [f0Template, List.mem_cons] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor

theorem f1Template_straight (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) :
  ∀ instruction ∈ f1Template xAddress rotation constant, StraightLine instruction := by
  intro instruction hmem
  simp only [f1Template, List.mem_cons] at hmem
  rcases hmem with
  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | hnil
  all_goals first | constructor | contradiction

theorem f2Template_straight (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) :
  ∀ instruction ∈ f2Template xAddress rotation constant, StraightLine instruction := by
  intro instruction hmem
  simp only [f2Template, List.mem_cons] at hmem
  rcases hmem with
  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | hnil
  all_goals first | constructor | contradiction

theorem f3Template_straight (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) :
  ∀ instruction ∈ f3Template xAddress rotation constant, StraightLine instruction := by
  intro instruction hmem
  simp only [f3Template, List.mem_cons] at hmem
  rcases hmem with
  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | hnil
  all_goals first | constructor | contradiction

theorem f4Template_straight (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) :
  ∀ instruction ∈ f4Template xAddress rotation constant, StraightLine instruction := by
  intro instruction hmem
  simp only [f4Template, List.mem_cons] at hmem
  rcases hmem with
  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | hnil
  all_goals first | constructor | contradiction

@[simp] theorem f0Template_length (xAddress : UInt256) (rotation : Nat) :
    (f0Template xAddress rotation).length = 42 := by
  rfl

@[simp] theorem f1Template_length (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) :
    (f1Template xAddress rotation constant).length = 46 := by
  rfl

@[simp] theorem f2Template_length (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) :
    (f2Template xAddress rotation constant).length = 47 := by
  rfl

@[simp] theorem f3Template_length (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) :
    (f3Template xAddress rotation constant).length = 46 := by
  rfl

@[simp] theorem f4Template_length (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) :
    (f4Template xAddress rotation constant).length = 47 := by
  rfl

/-! ## Artifact locations and PCs -/

structure LocatedSite (artifact : ProgramArtifact) (fork : Fork) where
  located : Located artifact fork
  pc : UInt256
  pc_eq : pc.toNat = artifact.instructionPC located.index

def LocatedSite.path {artifact : ProgramArtifact} {fork : Fork}
    (sites : List (LocatedSite artifact fork)) : List (Located artifact fork) :=
  sites.map LocatedSite.located

def headPC {artifact : ProgramArtifact} {fork : Fork}
    : List (LocatedSite artifact fork) → Option UInt256
  | [] => none
  | site :: _ => some site.pc

def afterPC {artifact : ProgramArtifact} {fork : Fork}
    : List (LocatedSite artifact fork) → Option UInt256
  | [] => none
  | [site] => some (site.pc + UInt256.ofNat site.located.instruction.size)
  | _ :: rest => afterPC rest

def Contiguous {artifact : ProgramArtifact} {fork : Fork}
    : List (LocatedSite artifact fork) → Prop
  | [] => True
  | [_] => True
  | first :: next :: rest =>
      next.pc = first.pc + UInt256.ofNat first.located.instruction.size ∧
        Contiguous (next :: rest)

structure GenericRoundSite (artifact : ProgramArtifact) (fork : Fork)
    (template : List Instr) where
  startPC : UInt256
  endPC : UInt256
  sites : List (LocatedSite artifact fork)
  head_eq : headPC sites = some startPC
  end_eq : afterPC sites = some endPC
  instruction_eq : sites.map (fun site => site.located.instruction) = template
  contiguous : Contiguous sites

def GenericRoundSite.path {artifact : ProgramArtifact} {fork : Fork}
    {template : List Instr} (site : GenericRoundSite artifact fork template) :
    List (Located artifact fork) :=
  LocatedSite.path site.sites

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
