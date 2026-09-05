import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCallTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-! Common metadata and builders for the H30b four-round sites. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

abbrev Artifact := Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout.A

abbrev leftWrapperIndex := QuadLayout.leftWrapperIndex
abbrev leftPC := QuadLayout.leftPC
abbrev leftJumpPC := QuadLayout.leftJumpPC
abbrev leftReturnPC := QuadLayout.leftReturnPC
abbrev leftHelperStartIndex := QuadLayout.leftHelperStartIndex
abbrev leftHelperJumpIndex := QuadLayout.leftHelperJumpIndex

abbrev rightWrapperIndex := QuadLayout.rightWrapperIndex
abbrev rightPC := QuadLayout.rightPC
abbrev rightJumpPC := QuadLayout.rightJumpPC
abbrev rightReturnPC := QuadLayout.rightReturnPC
abbrev rightHelperStartIndex := QuadLayout.rightHelperStartIndex
abbrev rightHelperJumpIndex := QuadLayout.rightHelperJumpIndex

abbrev leftStartPC : UInt256 := leftPC 0
abbrev leftEndPC : UInt256 := leftPC 20
abbrev rightStartPC : UInt256 := rightPC 0
abbrev rightEndPC : UInt256 := rightPC 20

abbrev leftHelperPCOfGroup (group : Nat) : UInt256 :=
  UInt256.ofNat (QuadLayout.leftHelperPCNat group)

abbrev rightHelperPCOfGroup (group : Nat) : UInt256 :=
  UInt256.ofNat (QuadLayout.rightHelperPCNat group)

abbrev leftHelperPC (k : Nat) : UInt256 :=
  leftHelperPCOfGroup (k / 4)

abbrev rightHelperPC (k : Nat) : UInt256 :=
  rightHelperPCOfGroup (k / 4)

theorem pc_toNat_instructionPC (index : Nat) :
    (UInt256.ofNat (Artifact.instructionPC index)).toNat =
      Artifact.instructionPC index := by
  exact QuadLayout.pc_toNat_instructionPC index

def leftAddress0 (k : Fin 20) : UInt256 :=
  StackRoundData.leftAddress (4 * k.val)

def leftAddress1 (k : Fin 20) : UInt256 :=
  StackRoundData.leftAddress (4 * k.val + 1)

def leftAddress2 (k : Fin 20) : UInt256 :=
  StackRoundData.leftAddress (4 * k.val + 2)

def leftAddress3 (k : Fin 20) : UInt256 :=
  StackRoundData.leftAddress (4 * k.val + 3)

def rightAddress0 (k : Fin 20) : UInt256 :=
  StackRoundData.rightAddress (4 * k.val)

def rightAddress1 (k : Fin 20) : UInt256 :=
  StackRoundData.rightAddress (4 * k.val + 1)

def rightAddress2 (k : Fin 20) : UInt256 :=
  StackRoundData.rightAddress (4 * k.val + 2)

def rightAddress3 (k : Fin 20) : UInt256 :=
  StackRoundData.rightAddress (4 * k.val + 3)

def leftRotation0 (k : Fin 20) : Nat :=
  StackRoundData.leftRotation (4 * k.val)

def leftRotation1 (k : Fin 20) : Nat :=
  StackRoundData.leftRotation (4 * k.val + 1)

def leftRotation2 (k : Fin 20) : Nat :=
  StackRoundData.leftRotation (4 * k.val + 2)

def leftRotation3 (k : Fin 20) : Nat :=
  StackRoundData.leftRotation (4 * k.val + 3)

def rightRotation0 (k : Fin 20) : Nat :=
  StackRoundData.rightRotation (4 * k.val)

def rightRotation1 (k : Fin 20) : Nat :=
  StackRoundData.rightRotation (4 * k.val + 1)

def rightRotation2 (k : Fin 20) : Nat :=
  StackRoundData.rightRotation (4 * k.val + 2)

def rightRotation3 (k : Fin 20) : Nat :=
  StackRoundData.rightRotation (4 * k.val + 3)

def leftConstant (k : Fin 20) : UInt256 :=
  StackRoundData.leftConstant (16 * (k.val / 4))

def rightConstant (k : Fin 20) : UInt256 :=
  StackRoundData.rightConstant (16 * (k.val / 4))

def quadWrapperTemplate (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat) : List Instr :=
  QuadCallTrace.quadCallPushes returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3 ++
    [op .JUMP, op .JUMPDEST]

def leftWrapperTemplate (k : Fin 20) : List Instr :=
  quadWrapperTemplate (leftReturnPC k.val)
    (leftAddress0 k) (leftAddress1 k) (leftAddress2 k) (leftAddress3 k)
    (leftHelperPC k.val) (leftRotation0 k) (leftRotation1 k)
    (leftRotation2 k) (leftRotation3 k)

def rightWrapperTemplate (k : Fin 20) : List Instr :=
  quadWrapperTemplate (rightReturnPC k.val)
    (rightAddress0 k) (rightAddress1 k) (rightAddress2 k) (rightAddress3 k)
    (rightHelperPC k.val) (rightRotation0 k) (rightRotation1 k)
    (rightRotation2 k) (rightRotation3 k)

def leftHelperTemplate (group : Fin 5) : List Instr :=
  QuadRoundState.quadBeforeJumpTemplate group.val
    (StackRoundData.leftConstant (16 * group.val))

def rightHelperTemplate (group : Fin 5) : List Instr :=
  QuadRoundState.quadBeforeJumpTemplate (4 - group.val)
    (StackRoundData.rightConstant (16 * group.val))

theorem getElem_of_slice {artifact : ProgramArtifact}
    (startIndex : Nat) (template : List Instr)
    (hslice : (artifact.instructions.drop startIndex).take template.length = template)
    (offset : Nat) (hoffset : offset < template.length) :
    artifact.instructions[startIndex + offset]? = some template[offset] := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) hslice
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs.trans (List.getElem?_eq_getElem hoffset)

def castTemplate {artifact : ProgramArtifact} {fork : Fork}
    {first second : List Instr}
    (site : GenericRoundSite artifact fork first) (h : first = second) :
    GenericRoundSite artifact fork second where
  startPC := site.startPC
  endPC := site.endPC
  sites := site.sites
  head_eq := site.head_eq
  end_eq := site.end_eq
  instruction_eq := site.instruction_eq.trans h
  contiguous := site.contiguous

theorem castTemplate_start {artifact : ProgramArtifact} {fork : Fork}
    {first second : List Instr}
    (site : GenericRoundSite artifact fork first) (h : first = second) :
    (castTemplate site h).startPC = site.startPC := rfl

theorem castTemplate_end {artifact : ProgramArtifact} {fork : Fork}
    {first second : List Instr}
    (site : GenericRoundSite artifact fork first) (h : first = second) :
    (castTemplate site h).endPC = site.endPC := rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites
