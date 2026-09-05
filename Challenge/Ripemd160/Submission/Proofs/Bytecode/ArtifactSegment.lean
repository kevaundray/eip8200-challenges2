import Challenge.EvmProof.Program

set_option warningAsError true

/-!
# Local instruction segments

These lemmas remove a certified prefix and suffix before concrete instruction
or PC reduction. The complete artifact and its exact-byte certificate remain
unchanged.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactSegment

open Challenge.EvmProof
open YulEvmCompiler

theorem assemble_append (left right : List Instr) :
    assemble (left ++ right) = assemble left ++ assemble right := by
  apply ByteArray.ext
  simp [assemble, assembleBytes_append, List.append_toArray]

theorem getElem?_segment (p : ProgramArtifact) (before segment after : List Instr)
    (hsplit : p.instructions = before ++ segment ++ after)
    (i : Nat) (hi : i < segment.length) :
    p.instructions[before.length + i]? = segment[i]? := by
  rw [hsplit, List.append_assoc, List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact List.getElem?_append_left hi

theorem instructionPC_segment (p : ProgramArtifact)
    (before segment after : List Instr)
    (hsplit : p.instructions = before ++ segment ++ after)
    (i : Nat) (hi : i ≤ segment.length) :
    p.instructionPC (before.length + i) =
      (assembleBytes before).length + (assembleBytes (segment.take i)).length := by
  unfold ProgramArtifact.instructionPC
  rw [hsplit, List.append_assoc, List.take_append,
    List.take_of_length_le (by omega : before.length ≤ before.length + i)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.take_append_of_le_length hi, assembleBytes_append, List.length_append]

theorem instructionPC_segment_of_bounds (p : ProgramArtifact)
    (before segment after : List Instr) (startIndex startPC : Nat)
    (hsplit : p.instructions = before ++ segment ++ after)
    (hindex : before.length = startIndex)
    (hpc : (assembleBytes before).length = startPC)
    (i : Nat) (hi : i ≤ segment.length) :
    p.instructionPC (startIndex + i) =
      startPC + (assembleBytes (segment.take i)).length := by
  simpa only [hindex, hpc] using
    instructionPC_segment p before segment after hsplit i hi

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactSegment
