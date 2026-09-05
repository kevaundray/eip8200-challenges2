import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-!
# H27 paired-round site certificate base

This module contains the exact H27 pair metadata and the generic builders used
by the independent left and right certificate modules.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairSites

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

abbrev Artifact := Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact.submissionArtifact

theorem pc_toNat_instructionPC (index : Nat) :
    (UInt256.ofNat (Artifact.instructionPC index)).toNat =
      Artifact.instructionPC index := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hle :=
    Challenge.EvmProof.ProgramArtifact.instructionPC_le_code_size Artifact index
  have hcode := StackRoundData.artifact_code_bound
  exact Nat.lt_of_le_of_lt hle hcode

def leftWrapperIndex (k : Nat) : Nat := 930 + 8 * k

def rightWrapperIndex (k : Nat) : Nat := 1260 + 8 * k

def leftPC (k : Nat) : UInt256 :=
  UInt256.ofNat (Artifact.instructionPC (leftWrapperIndex k))

def rightPC (k : Nat) : UInt256 :=
  UInt256.ofNat (Artifact.instructionPC (rightWrapperIndex k))

def leftStartPC : UInt256 := leftPC 0

def leftEndPC : UInt256 := leftPC 40

def rightStartPC : UInt256 := rightPC 0

def rightEndPC : UInt256 := rightPC 40

def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (Artifact.instructionPC (leftWrapperIndex k + 6))

def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (Artifact.instructionPC (rightWrapperIndex k + 6))

def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (Artifact.instructionPC (leftWrapperIndex k + 7))

def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (Artifact.instructionPC (rightWrapperIndex k + 7))

def leftHelperPCOfGroup : Nat → UInt256
  | 0 => UInt256.ofNat 0xb3d
  | 1 => UInt256.ofNat 0xb9a
  | 2 => UInt256.ofNat 0xc07
  | 3 => UInt256.ofNat 0xc72
  | _ => UInt256.ofNat 0xcdf

def rightHelperPCOfGroup : Nat → UInt256
  | 0 => UInt256.ofNat 0xd4a
  | 1 => UInt256.ofNat 0xdb5
  | 2 => UInt256.ofNat 0xe22
  | 3 => UInt256.ofNat 0xe8d
  | _ => UInt256.ofNat 0xefa

def leftHelperPC (k : Nat) : UInt256 := leftHelperPCOfGroup (k / 8)

def rightHelperPC (k : Nat) : UInt256 := rightHelperPCOfGroup (k / 8)

def leftHelperStartIndex : Nat → Nat
  | 0 => 1641
  | 1 => 1696
  | 2 => 1759
  | 3 => 1820
  | _ => 1883

def rightHelperStartIndex : Nat → Nat
  | 0 => 1944
  | 1 => 2005
  | 2 => 2068
  | 3 => 2129
  | _ => 2192

def leftHelperJumpIndex : Nat → Nat
  | 0 => 1695
  | 1 => 1758
  | 2 => 1819
  | 3 => 1882
  | _ => 1943

def rightHelperJumpIndex : Nat → Nat
  | 0 => 2004
  | 1 => 2067
  | 2 => 2128
  | 3 => 2191
  | _ => 2246

def leftAddress0 (k : Fin 40) : UInt256 :=
  StackRoundData.leftAddress (2 * k.val)

def leftAddress1 (k : Fin 40) : UInt256 :=
  StackRoundData.leftAddress (2 * k.val + 1)

def rightAddress0 (k : Fin 40) : UInt256 :=
  StackRoundData.rightAddress (2 * k.val)

def rightAddress1 (k : Fin 40) : UInt256 :=
  StackRoundData.rightAddress (2 * k.val + 1)

def leftRotation0 (k : Fin 40) : Nat :=
  StackRoundData.leftRotation (2 * k.val)

def leftRotation1 (k : Fin 40) : Nat :=
  StackRoundData.leftRotation (2 * k.val + 1)

def rightRotation0 (k : Fin 40) : Nat :=
  StackRoundData.rightRotation (2 * k.val)

def rightRotation1 (k : Fin 40) : Nat :=
  StackRoundData.rightRotation (2 * k.val + 1)

def leftConstant (k : Fin 40) : UInt256 :=
  StackRoundData.leftConstant (16 * (k.val / 8))

def rightConstant (k : Fin 40) : UInt256 :=
  StackRoundData.rightConstant (16 * (k.val / 8))

def pairWrapperTemplate (returnPC p0 p1 helperPC : UInt256)
    (r0 r1 : Nat) : List Instr :=
  PairRoundState.pairCallPushes returnPC p0 p1 helperPC r0 r1 ++
    [op .JUMP, op .JUMPDEST]

def leftWrapperTemplate (k : Fin 40) : List Instr :=
  pairWrapperTemplate (leftReturnPC k.val) (leftAddress0 k) (leftAddress1 k)
    (leftHelperPC k.val) (leftRotation0 k) (leftRotation1 k)

def rightWrapperTemplate (k : Fin 40) : List Instr :=
  pairWrapperTemplate (rightReturnPC k.val) (rightAddress0 k) (rightAddress1 k)
    (rightHelperPC k.val) (rightRotation0 k) (rightRotation1 k)

def leftHelperTemplate (group : Fin 5) : List Instr :=
  pairBeforeJumpTemplate group.val
    (StackRoundData.leftConstant (16 * group.val))

def rightHelperTemplate (group : Fin 5) : List Instr :=
  pairBeforeJumpTemplate (4 - group.val)
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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairSites
