import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLeftSlices0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLeftSlices1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLeftSlices2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLeftSlices3
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLeftSlices4
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRightSlices0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRightSlices1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRightSlices2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRightSlices3
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRightSlices4

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSliceCertificates

open YulEvmCompiler StackRoundData

structure SliceFacts (startIndex : Nat) (instructions : List Instr) (nextIndex : Nat) : Prop where
  slice : (Artifact.submissionArtifact.instructions.drop startIndex).take instructions.length =
    instructions
  wellFormed : TemplateWellFormed instructions
  nonempty : instructions ≠ []
  fits : startIndex + instructions.length ≤ Artifact.submissionArtifact.instructions.length
  next : startIndex + instructions.length = nextIndex

private theorem all80 (P : Nat → Prop)
    (h0 : ∀ j : Fin 16, P (0 + j.val))
    (h1 : ∀ j : Fin 16, P (16 + j.val))
    (h2 : ∀ j : Fin 16, P (32 + j.val))
    (h3 : ∀ j : Fin 16, P (48 + j.val))
    (h4 : ∀ j : Fin 16, P (64 + j.val)) (i : Fin 80) : P i.val := by
  by_cases h16 : i.val < 16
  · simpa only [Nat.zero_add] using h0 ⟨i.val, h16⟩
  by_cases h32 : i.val < 32
  · simpa only [show 16 + (i.val - 16) = i.val by omega] using
      h1 ⟨i.val - 16, by omega⟩
  by_cases h48 : i.val < 48
  · simpa only [show 32 + (i.val - 32) = i.val by omega] using
      h2 ⟨i.val - 32, by omega⟩
  by_cases h64 : i.val < 64
  · simpa only [show 48 + (i.val - 48) = i.val by omega] using
      h3 ⟨i.val - 48, by omega⟩
  · simpa only [show 64 + (i.val - 64) = i.val by omega] using
      h4 ⟨i.val - 64, by omega⟩

theorem leftFacts (i : Fin 80) :
    SliceFacts (leftStartIndex i.val) (leftTemplate i.val)
      (leftStartIndex (i.val + 1)) := by
  apply all80 (fun j => SliceFacts (leftStartIndex j) (leftTemplate j)
    (leftStartIndex (j + 1))) 
    (fun j => ⟨StackLeftSlices0.slice j, StackLeftSlices0.wellFormed j,
      StackLeftSlices0.nonempty j, StackLeftSlices0.fits j, StackLeftSlices0.nextIndex j⟩) 
    (fun j => ⟨StackLeftSlices1.slice j, StackLeftSlices1.wellFormed j,
      StackLeftSlices1.nonempty j, StackLeftSlices1.fits j, StackLeftSlices1.nextIndex j⟩) 
    (fun j => ⟨StackLeftSlices2.slice j, StackLeftSlices2.wellFormed j,
      StackLeftSlices2.nonempty j, StackLeftSlices2.fits j, StackLeftSlices2.nextIndex j⟩) 
    (fun j => ⟨StackLeftSlices3.slice j, StackLeftSlices3.wellFormed j,
      StackLeftSlices3.nonempty j, StackLeftSlices3.fits j, StackLeftSlices3.nextIndex j⟩) 
    (fun j => ⟨StackLeftSlices4.slice j, StackLeftSlices4.wellFormed j,
      StackLeftSlices4.nonempty j, StackLeftSlices4.fits j, StackLeftSlices4.nextIndex j⟩)
    i

theorem rightFacts (i : Fin 80) :
    SliceFacts (rightStartIndex i.val) (rightTemplate i.val)
      (rightStartIndex (i.val + 1)) := by
  apply all80 (fun j => SliceFacts (rightStartIndex j) (rightTemplate j)
    (rightStartIndex (j + 1))) 
    (fun j => ⟨StackRightSlices0.slice j, StackRightSlices0.wellFormed j,
      StackRightSlices0.nonempty j, StackRightSlices0.fits j, StackRightSlices0.nextIndex j⟩) 
    (fun j => ⟨StackRightSlices1.slice j, StackRightSlices1.wellFormed j,
      StackRightSlices1.nonempty j, StackRightSlices1.fits j, StackRightSlices1.nextIndex j⟩) 
    (fun j => ⟨StackRightSlices2.slice j, StackRightSlices2.wellFormed j,
      StackRightSlices2.nonempty j, StackRightSlices2.fits j, StackRightSlices2.nextIndex j⟩) 
    (fun j => ⟨StackRightSlices3.slice j, StackRightSlices3.wellFormed j,
      StackRightSlices3.nonempty j, StackRightSlices3.fits j, StackRightSlices3.nextIndex j⟩) 
    (fun j => ⟨StackRightSlices4.slice j, StackRightSlices4.wellFormed j,
      StackRightSlices4.nonempty j, StackRightSlices4.fits j, StackRightSlices4.nextIndex j⟩)
    i

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSliceCertificates

