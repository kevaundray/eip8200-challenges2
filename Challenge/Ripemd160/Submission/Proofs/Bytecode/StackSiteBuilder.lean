import Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactSegment
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

set_option warningAsError true
set_option maxRecDepth 30000

/-!
# Generic instruction-site certificates

The constructor below uses an instruction slice and `ProgramArtifact.instructionPC`.
It does not inspect a concrete bytecode literal or reduce prefix encodings.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Stepper
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

private theorem getElem_slice {artifact : ProgramArtifact} (startIndex : Nat)
    (template : List Instr)
    (hslice : (artifact.instructions.drop startIndex).take template.length = template)
    (i : Nat) (hi : i < template.length) :
    artifact.instructions[startIndex + i]? = some template[i] := by
  have hs := congrArg (fun xs : List Instr => xs[i]?) hslice
  rw [List.getElem?_take, if_pos hi, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs.trans (List.getElem?_eq_getElem hi)

private theorem instructionPC_succ (artifact : ProgramArtifact) (index : Nat)
    (hi : index < artifact.instructions.length) :
    artifact.instructionPC (index + 1) =
      artifact.instructionPC index + artifact.instructions[index].size := by
  unfold ProgramArtifact.instructionPC
  rw [← List.take_append_getElem hi, assembleBytes_append]
  simp [Instr.size]

private theorem headPC_finRange_map
    : ∀ {artifact : ProgramArtifact} {fork : Fork} (n : Nat)
      (f : Fin n → LocatedSite artifact fork), ∀ (hn : 0 < n),
      headPC ((List.finRange n).map f) =
        some (f ⟨0, by omega⟩).pc := by
  intro artifact fork n
  cases n with
  | zero =>
      intro f hn
      omega
  | succ n =>
      intro f hn
      rw [List.finRange_succ, List.map_cons]
      change some (f 0).pc = some (f ⟨0, by omega⟩).pc
      rfl

private theorem contiguous_finRange_map
    : ∀ {artifact : ProgramArtifact} {fork : Fork} (n : Nat)
      (f : Fin n → LocatedSite artifact fork),
      (∀ (i : Fin n) (hi : i.val + 1 < n),
        (f ⟨i.val + 1, hi⟩).pc =
          (f i).pc + UInt256.ofNat (f i).located.instruction.size) →
      Contiguous ((List.finRange n).map f) := by
  intro artifact fork n
  induction n with
  | zero =>
      intro f hstep
      simp [Contiguous]
  | succ n ih =>
      intro f hstep
      cases n with
      | zero =>
          simp [List.finRange_succ, Contiguous]
      | succ n =>
          let g : Fin (n + 1) → LocatedSite artifact fork := fun i => f i.succ
          have htail : (List.finRange (n + 1)).map g =
              g 0 :: (List.finRange n).map (fun i => g i.succ) := by
            rw [List.finRange_succ, List.map_cons, List.map_map]
            simp [g, Function.comp_def]
          rw [List.finRange_succ, List.map_cons, List.map_map]
          change Contiguous (f 0 :: (List.finRange (n + 1)).map g)
          rw [htail]
          change (g 0).pc = (f 0).pc +
              UInt256.ofNat (f 0).located.instruction.size ∧
            Contiguous (g 0 :: (List.finRange n).map (fun i => g i.succ))
          constructor
          · have hzero : (0 : Nat) + 1 < n + 1 + 1 := by omega
            have hs := hstep (0 : Fin (n + 1 + 1)) hzero
            simpa [g] using hs
          · have hih := ih g (by
              intro i hi
              have hi' : (i.succ : Fin (n + 1 + 1)).val + 1 < n + 1 + 1 := by
                dsimp
                omega
              have hs := hstep i.succ hi'
              simpa [g] using hs)
            rw [htail] at hih
            exact hih

private theorem afterPC_finRange_map_last
    : ∀ {artifact : ProgramArtifact} {fork : Fork} (n : Nat)
      (f : Fin n → LocatedSite artifact fork), ∀ (hn : 0 < n),
      afterPC ((List.finRange n).map f) =
        some ((f ⟨n - 1, by omega⟩).pc +
          UInt256.ofNat (f ⟨n - 1, by omega⟩).located.instruction.size) := by
  intro artifact fork n
  induction n with
  | zero =>
      intro f hn
      omega
  | succ n ih =>
      intro f hn
      cases n with
      | zero =>
          simp [List.finRange_succ, afterPC]
      | succ n =>
          let g : Fin (n + 1) → LocatedSite artifact fork := fun i => f i.succ
          have htail : (List.finRange (n + 1)).map g =
              g 0 :: (List.finRange n).map (fun i => g i.succ) := by
            rw [List.finRange_succ, List.map_cons, List.map_map]
            simp [g, Function.comp_def]
          rw [List.finRange_succ, List.map_cons, List.map_map]
          change afterPC (f 0 :: (List.finRange (n + 1)).map g) = _
          have hih := ih g (by omega)
          rw [htail] at hih
          rw [htail]
          change afterPC (f 0 :: g 0 ::
            (List.finRange n).map (fun i => g i.succ)) = _
          rw [show afterPC (f 0 :: g 0 ::
              (List.finRange n).map (fun i => g i.succ)) =
              afterPC (g 0 :: (List.finRange n).map (fun i => g i.succ)) by rfl]
          simpa [g] using hih

def ofSlice {artifact : ProgramArtifact} {fork : Fork}
    (template : List Instr) (startIndex : Nat)
    (hslice : (artifact.instructions.drop startIndex).take template.length = template)
    (hbounds : startIndex + template.length ≤ artifact.instructions.length)
    (hcode : artifact.code.size < 2 ^ 256)
    (hwell : ∀ instruction ∈ template, WellFormed fork instruction)
    (hnonempty : template ≠ []) :
    GenericRoundSite artifact fork template := by
  have hpc_lt (index : Nat) : artifact.instructionPC index < 2 ^ 256 := by
    have hle := artifact.instructionPC_le_code_size index
    omega
  have hlenne : template.length ≠ 0 := by
    intro hzero
    apply hnonempty
    exact List.length_eq_zero_iff.mp hzero
  have hlenpos : 0 < template.length := Nat.pos_of_ne_zero hlenne
  have hlast : template.length - 1 < template.length := by omega
  let mkSite : Fin template.length → LocatedSite artifact fork := fun i =>
    { located :=
        { index := startIndex + i.val
          instruction := template[i.val]
          atIndex := getElem_slice startIndex template hslice i.val i.isLt
          wellFormed := hwell _ (List.getElem_mem i.isLt) }
      pc := UInt256.ofNat (artifact.instructionPC (startIndex + i.val))
      pc_eq := by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat]
        exact Nat.mod_eq_of_lt (hpc_lt (startIndex + i.val)) }
  let sites : List (LocatedSite artifact fork) :=
    (List.finRange template.length).map mkSite
  have hstep : ∀ (i : Fin template.length) (hi : i.val + 1 < template.length),
      (mkSite ⟨i.val + 1, hi⟩).pc =
        (mkSite i).pc +
          UInt256.ofNat (mkSite i).located.instruction.size := by
    intro i hi
    have hidx : startIndex + i.val < artifact.instructions.length := by
      omega
    have hinst? := getElem_slice startIndex template hslice i.val i.isLt
    have hinst : artifact.instructions[startIndex + i.val]'hidx = template[i.val] := by
      exact Option.some.inj
        ((List.getElem?_eq_getElem hidx).symm.trans hinst?)
    have hsucc := instructionPC_succ artifact (startIndex + i.val) hidx
    dsimp [mkSite]
    calc
      UInt256.ofNat (artifact.instructionPC (startIndex + (i.val + 1))) =
          UInt256.ofNat (artifact.instructionPC (startIndex + i.val) +
            template[i.val].size) := by
        rw [show startIndex + (i.val + 1) = startIndex + i.val + 1 by omega,
          hsucc, hinst]
      _ = UInt256.ofNat (artifact.instructionPC (startIndex + i.val)) +
          UInt256.ofNat template[i.val].size :=
        (Challenge.EvmProof.Word.ofNat_add_mod _ _).symm
  have hcont : Contiguous sites := by
    exact contiguous_finRange_map template.length mkSite hstep
  have hinstruction : sites.map (fun site => site.located.instruction) = template := by
    rw [List.map_map]
    simp [mkSite, Function.comp_def]
  have hhead : headPC sites =
      some (UInt256.ofNat (artifact.instructionPC startIndex)) := by
    have hhead' := headPC_finRange_map template.length mkSite hlenpos
    simpa [sites, mkSite] using hhead'
  have hendlast :
      (mkSite ⟨template.length - 1, hlast⟩).pc +
          UInt256.ofNat
            (mkSite ⟨template.length - 1, hlast⟩).located.instruction.size =
        UInt256.ofNat (artifact.instructionPC (startIndex + template.length)) := by
    have hidx : startIndex + (template.length - 1) < artifact.instructions.length := by
      exact lt_of_lt_of_le (by omega) hbounds
    have hinst? := getElem_slice startIndex template hslice
      (template.length - 1) hlast
    have hinst : artifact.instructions[startIndex + (template.length - 1)]'hidx =
        template[template.length - 1] := by
      exact Option.some.inj
        ((List.getElem?_eq_getElem hidx).symm.trans hinst?)
    have hsucc := instructionPC_succ artifact (startIndex + (template.length - 1)) hidx
    have hsucc' : artifact.instructionPC (startIndex + template.length) =
        artifact.instructionPC (startIndex + (template.length - 1)) +
          template[template.length - 1].size := by
      calc
        artifact.instructionPC (startIndex + template.length) =
            artifact.instructionPC (startIndex + (template.length - 1) + 1) := by
              congr 1
              omega
        _ = artifact.instructionPC (startIndex + (template.length - 1)) +
            (artifact.instructions[startIndex + (template.length - 1)]'hidx).size := hsucc
        _ = artifact.instructionPC (startIndex + (template.length - 1)) +
            template[template.length - 1].size := by rw [hinst]
    dsimp [mkSite]
    calc
      UInt256.ofNat (artifact.instructionPC (startIndex + (template.length - 1))) +
          UInt256.ofNat template[template.length - 1].size =
          UInt256.ofNat (artifact.instructionPC (startIndex + (template.length - 1)) +
            template[template.length - 1].size) :=
        Challenge.EvmProof.Word.ofNat_add_mod _ _
      _ = UInt256.ofNat (artifact.instructionPC (startIndex + template.length)) := by
        rw [hsucc']
  have hend : afterPC sites =
      some (UInt256.ofNat (artifact.instructionPC (startIndex + template.length))) := by
    have hlast := afterPC_finRange_map_last template.length mkSite (by
      have hlenne : template.length ≠ 0 := by
        intro hzero
        apply hnonempty
        exact List.length_eq_zero_iff.mp hzero
      omega)
    rw [hendlast] at hlast
    simpa [sites] using hlast
  exact
    { startPC := UInt256.ofNat (artifact.instructionPC startIndex)
      endPC := UInt256.ofNat (artifact.instructionPC (startIndex + template.length))
      sites := sites
      head_eq := hhead
      end_eq := hend
      instruction_eq := hinstruction
      contiguous := hcont }

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
