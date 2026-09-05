import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSliceCertificates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSites

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StackRoundData StackRoundTemplate

def leftPC (i : Nat) : UInt256 :=
  UInt256.ofNat (Artifact.submissionArtifact.instructionPC (leftStartIndex i))

def rightPC (i : Nat) : UInt256 :=
  UInt256.ofNat (Artifact.submissionArtifact.instructionPC (rightStartIndex i))

def leftSite (i : Fin 80) :
    GenericRoundSite Artifact.submissionArtifact .Osaka (leftTemplate i.val) :=
  StackSiteBuilder.ofSlice (leftTemplate i.val) (leftStartIndex i.val)
    (StackSliceCertificates.leftFacts i).slice
    (StackSliceCertificates.leftFacts i).fits artifact_code_bound
    (templateWellFormed_mem (StackSliceCertificates.leftFacts i).wellFormed)
    (StackSliceCertificates.leftFacts i).nonempty

@[simp] theorem leftSite_start (i : Fin 80) :
    (leftSite i).startPC = leftPC i.val := rfl

@[simp] theorem leftSite_end (i : Fin 80) :
    (leftSite i).endPC = leftPC (i.val + 1) := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC
    (leftStartIndex i.val + (leftTemplate i.val).length)) = _
  rw [(StackSliceCertificates.leftFacts i).next]
  rfl

theorem leftSite_chain (i : Fin 80) (hi : i.val < 79) :
    (leftSite ⟨i.val + 1, by omega⟩).startPC = (leftSite i).endPC := by
  rw [leftSite_start, leftSite_end]

def rightSite (i : Fin 80) :
    GenericRoundSite Artifact.submissionArtifact .Osaka (rightTemplate i.val) :=
  StackSiteBuilder.ofSlice (rightTemplate i.val) (rightStartIndex i.val)
    (StackSliceCertificates.rightFacts i).slice
    (StackSliceCertificates.rightFacts i).fits artifact_code_bound
    (templateWellFormed_mem (StackSliceCertificates.rightFacts i).wellFormed)
    (StackSliceCertificates.rightFacts i).nonempty

@[simp] theorem rightSite_start (i : Fin 80) :
    (rightSite i).startPC = rightPC i.val := rfl

@[simp] theorem rightSite_end (i : Fin 80) :
    (rightSite i).endPC = rightPC (i.val + 1) := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC
    (rightStartIndex i.val + (rightTemplate i.val).length)) = _
  rw [(StackSliceCertificates.rightFacts i).next]
  rfl

theorem rightSite_chain (i : Fin 80) (hi : i.val < 79) :
    (rightSite ⟨i.val + 1, by omega⟩).startPC = (rightSite i).endPC := by
  rw [rightSite_start, rightSite_end]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSites

