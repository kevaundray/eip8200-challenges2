import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
import Challenge.EvmProof.Meter
import YulEvmCompiler.LowerDefs

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# H10 direct stack-round traces

The evaluator theorem in this file is generic in `ProgramArtifact`.  The
caller supplies only a `GenericRoundSite`; no large artifact literal is
reduced while proving a round.  The f0 theorem is the first direct trace and
its gas theorem lifts the same successful evaluator result through the actual
semantic stepper.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

abbrev Located (artifact : ProgramArtifact) (fork : Fork) :=
  Challenge.EvmProof.Stepper.Located artifact fork

def roundWorking (a b c d e : UInt256) : Compression.EvmWorking :=
  { a := a, b := b, c := c, d := d, e := e }

def roundWord (s : State) (xAddress : UInt256) : UInt256 :=
  MachineState.readWord s.memory xAddress.toNat

def roundResult (s : State) (j : Nat)
    (a b c d e xAddress : UInt256) (rotation : Nat) (constant : UInt256) :
    Compression.EvmWorking :=
  stackRound (roundWorking a b c d e) j (roundWord s xAddress)
    rotation constant

def roundWords (x : Compression.EvmWorking) : List UInt256 :=
  [x.a, x.b, x.c, x.d, x.e]

def roundEntry (s : State) (startPC : UInt256)
    (a b c d e : UInt256) (rest : List UInt256) : State :=
  { s with pc := startPC, stack := [a, b, c, d, e] ++ rest }

def roundReturned (s : State) (endPC : UInt256) (j : Nat)
    (a b c d e xAddress : UInt256) (rotation : Nat) (constant : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := endPC
    stack := roundWords
      (roundResult s j a b c d e xAddress rotation constant) ++ rest
    memory := s.memory
    activeWords := s.activeWordsAfterUInt256 xAddress.toNat 32 }

def runInstrSeq : List Instr → State → Option State
  | [], s => some s
  | instruction :: rest, s =>
      match Challenge.EvmProof.Stepper.runInstr instruction s with
      | none => none
      | some next =>
          match rest with
          | [] => some next
          | _ :: _ =>
              match next.halt with
              | .Running => runInstrSeq rest next
              | _ => none

def pcAfter (pc : UInt256) : List Instr → UInt256
  | [] => pc
  | instruction :: rest =>
      pcAfter (pc + UInt256.ofNat instruction.size) rest

theorem endPC_eq_pcAfter_sites
    {artifact : ProgramArtifact} {fork : Fork}
    (sites : List (LocatedSite artifact fork)) (startPC endPC : UInt256)
    (hhead : headPC sites = some startPC)
    (hend : afterPC sites = some endPC)
    (hcont : Contiguous sites) :
    endPC = pcAfter startPC (sites.map (fun site => site.located.instruction)) := by
  induction sites generalizing startPC endPC with
  | nil =>
      simp [headPC] at hhead
  | cons first rest ih =>
      cases rest with
      | nil =>
          have hstart : first.pc = startPC := by
            simpa [headPC] using hhead
          have hend' : endPC = first.pc +
              UInt256.ofNat first.located.instruction.size := by
            simpa [afterPC] using hend.symm
          calc
            endPC = first.pc + UInt256.ofNat first.located.instruction.size := hend'
            _ = startPC + UInt256.ofNat first.located.instruction.size := by rw [hstart]
            _ = pcAfter startPC [first.located.instruction] := by rfl
      | cons second tail =>
          rcases hcont with ⟨hnext, htail⟩
          have hstart : first.pc = startPC := by
            simpa [headPC] using hhead
          have hheadTail : headPC (second :: tail) = some second.pc := by
            rfl
          have hendTail : afterPC (second :: tail) = some endPC := by
            simpa [afterPC] using hend
          have htailPC := ih (startPC := second.pc) (endPC := endPC)
            hheadTail hendTail htail
          calc
            endPC = pcAfter second.pc
                ((second :: tail).map (fun site => site.located.instruction)) := htailPC
            _ = pcAfter (first.pc + UInt256.ofNat first.located.instruction.size)
                ((second :: tail).map (fun site => site.located.instruction)) := by
                  rw [hnext]
            _ = pcAfter (startPC + UInt256.ofNat first.located.instruction.size)
                ((second :: tail).map (fun site => site.located.instruction)) := by
                  rw [hstart]
            _ = pcAfter startPC
                ((first :: second :: tail).map
                  (fun site => site.located.instruction)) := by
                  rfl

private theorem runInstr_pc_binary {instruction : Instr} {s t : State}
    (hform : instruction = .op .ADD ∨ instruction = .op .AND ∨
      instruction = .op .OR ∨ instruction = .op .XOR ∨
      instruction = .op .SHL ∨ instruction = .op .SHR)
    (hresult : Challenge.EvmProof.Stepper.runInstr instruction s = some t) :
    t.pc = s.pc.succ := by
  rcases hform with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    by_cases hcap : s.stack.length < 1024
    · rw [Challenge.EvmProof.Stepper.runInstr, if_pos hcap] at hresult
      cases hs : s.stack with
      | nil => simp [hs] at hresult
      | cons a tail =>
          cases ht : tail with
          | nil => simp [hs, ht] at hresult
          | cons b rest =>
              simp [hs, ht] at hresult
              subst t
              rfl
    · simp [Challenge.EvmProof.Stepper.runInstr, hcap] at hresult

private theorem runInstr_pc_unary {instruction : Instr} {s t : State}
    (hform : instruction = .op .NOT ∨ instruction = .op .POP ∨
      instruction = .op .MLOAD)
    (hresult : Challenge.EvmProof.Stepper.runInstr instruction s = some t) :
    t.pc = s.pc.succ := by
  rcases hform with rfl | rfl | rfl
  all_goals
    by_cases hcap : s.stack.length < 1024
    · rw [Challenge.EvmProof.Stepper.runInstr, if_pos hcap] at hresult
      cases hs : s.stack with
      | nil => simp [hs] at hresult
      | cons a rest =>
          simp [hs] at hresult
          subst t
          rfl
    · simp [Challenge.EvmProof.Stepper.runInstr, hcap] at hresult

private theorem runInstr_pc_push {width : Fin 33} {value : UInt256}
    {s t : State}
    (hresult : Challenge.EvmProof.Stepper.runInstr (.push width value) s = some t) :
    t.pc = s.pc + UInt256.ofNat (Instr.push width value).size := by
  by_cases hcap : s.stack.length < 1024
  · rw [Challenge.EvmProof.Stepper.runInstr, if_pos hcap] at hresult
    by_cases hwidth : width.val = 0
    · simp [hwidth] at hresult
      cases hresult
      rw [Instr.size_push]
      change s.pc.succ = s.pc + UInt256.ofNat (1 + width.val)
      rw [hwidth]
      rfl
    · simp [hwidth] at hresult
      cases hresult
      rw [Instr.size_push]
      change s.pc + UInt256.ofNat (width.val + 1) =
        s.pc + UInt256.ofNat (1 + width.val)
      rw [Nat.add_comm (width.val) 1]
  · simp [Challenge.EvmProof.Stepper.runInstr, hcap] at hresult

private theorem runInstr_pc_dup {operation : Operation.DupOp} {s t : State}
    (hresult : Challenge.EvmProof.Stepper.runInstr (.op (.Dup operation)) s = some t) :
    t.pc = s.pc.succ := by
  by_cases hcap : s.stack.length < 1024
  · rw [Challenge.EvmProof.Stepper.runInstr, if_pos hcap] at hresult
    split at hresult
    · cases hresult
      rfl
    · simp_all
  · simp [Challenge.EvmProof.Stepper.runInstr, hcap] at hresult

private theorem runInstr_pc_swap {operation : Operation.SwapOp} {s t : State}
    (hresult : Challenge.EvmProof.Stepper.runInstr (.op (.Swap operation)) s = some t) :
    t.pc = s.pc.succ := by
  by_cases hcap : s.stack.length < 1024
  · rw [Challenge.EvmProof.Stepper.runInstr, if_pos hcap] at hresult
    split at hresult
    · cases hresult
      rfl
    · simp_all
  · simp [Challenge.EvmProof.Stepper.runInstr, hcap] at hresult

theorem runInstr_pc_of_straight {instruction : Instr} {s t : State}
    (hstraight : StraightLine instruction)
    (hresult : Challenge.EvmProof.Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  cases hstraight with
  | push width value => exact runInstr_pc_push hresult
  | add =>
      change t.pc = s.pc.add (UInt256.ofNat 1)
      exact runInstr_pc_binary (hform := Or.inl rfl) hresult
  | and =>
      change t.pc = s.pc.add (UInt256.ofNat 1)
      exact runInstr_pc_binary (hform := Or.inr (Or.inl rfl)) hresult
  | or =>
      change t.pc = s.pc.add (UInt256.ofNat 1)
      exact runInstr_pc_binary (hform := Or.inr (Or.inr (Or.inl rfl))) hresult
  | xor =>
      change t.pc = s.pc.add (UInt256.ofNat 1)
      exact runInstr_pc_binary
        (hform := Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hresult
  | shl =>
      change t.pc = s.pc.add (UInt256.ofNat 1)
      exact runInstr_pc_binary
        (hform := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hresult
  | shr =>
      change t.pc = s.pc.add (UInt256.ofNat 1)
      exact runInstr_pc_binary
        (hform := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hresult
  | not =>
      change t.pc = s.pc.add (UInt256.ofNat 1)
      exact runInstr_pc_unary (hform := Or.inl rfl) hresult
  | pop =>
      change t.pc = s.pc.add (UInt256.ofNat 1)
      exact runInstr_pc_unary (hform := Or.inr (Or.inl rfl)) hresult
  | mload =>
      change t.pc = s.pc.add (UInt256.ofNat 1)
      exact runInstr_pc_unary (hform := Or.inr (Or.inr rfl)) hresult
  | dup operation =>
      change t.pc = s.pc.add (UInt256.ofNat 1)
      exact runInstr_pc_dup hresult
  | swap operation =>
      change t.pc = s.pc.add (UInt256.ofNat 1)
      exact runInstr_pc_swap hresult

theorem runLocatedBlock_eq_runInstrSeq
    {artifact : ProgramArtifact} {fork : Fork}
    (sites : List (LocatedSite artifact fork)) (template : List Instr)
    (hinst : sites.map (fun site => site.located.instruction) = template)
    (hcont : Contiguous sites) (s : State)
    (hhead : headPC sites = some s.pc)
    (hadvance : ∀ site, site ∈ sites →
      ∀ {u v : State},
        Challenge.EvmProof.Stepper.runInstr site.located.instruction u = some v →
          v.pc = u.pc + UInt256.ofNat site.located.instruction.size) :
    Challenge.EvmProof.Stepper.runLocatedBlock (LocatedSite.path sites) s =
      runInstrSeq template s := by
  induction sites generalizing template s with
  | nil =>
      simp [headPC] at hhead
  | cons first rest ih =>
      cases rest with
      | nil =>
          have hpc : s.pc = first.pc := by
            simpa [headPC] using hhead.symm
          have htemplate : template = [first.located.instruction] := by
            simpa [LocatedSite.path] using hinst.symm
          subst template
          have hrun : Challenge.EvmProof.Stepper.runLocated first.located s =
              Challenge.EvmProof.Stepper.runInstr first.located.instruction s := by
            simp [Challenge.EvmProof.Stepper.runLocated, first.pc_eq, hpc]
          change (match Challenge.EvmProof.Stepper.runLocated first.located s with
            | none => none
            | some next => some next) =
            (match Challenge.EvmProof.Stepper.runInstr first.located.instruction s with
            | none => none
            | some next => some next)
          rw [hrun]
      | cons second tail =>
          have hpc : s.pc = first.pc := by
            simpa [headPC] using hhead.symm
          have hrun : ∀ {u v : State},
              Challenge.EvmProof.Stepper.runInstr first.located.instruction u = some v →
                v.pc = u.pc + UInt256.ofNat first.located.instruction.size := by
            intro u v hresult
            exact hadvance first (by simp) hresult
          rcases hcont with ⟨hnextPC, htailCont⟩
          have htemplate : template = first.located.instruction ::
              (second :: tail).map (fun site => site.located.instruction) := by
            simpa using hinst.symm
          subst template
          have hadvanceTail : ∀ site, site ∈ second :: tail →
              ∀ {u v : State},
                Challenge.EvmProof.Stepper.runInstr site.located.instruction u = some v →
                  v.pc = u.pc + UInt256.ofNat site.located.instruction.size := by
            intro site hmem u v hresult
            exact hadvance site (by simp [hmem]) hresult
          cases hrunFirst :
              Challenge.EvmProof.Stepper.runInstr first.located.instruction s with
          | none =>
              simp [LocatedSite.path, Challenge.EvmProof.Stepper.runLocatedBlock,
                runInstrSeq, Challenge.EvmProof.Stepper.runLocated,
                first.pc_eq, hpc, hrunFirst]
          | some next =>
              have hnextPC' : next.pc = second.pc := by
                calc
                  next.pc = s.pc + UInt256.ofNat first.located.instruction.size :=
                    hrun hrunFirst
                  _ = first.pc + UInt256.ofNat first.located.instruction.size := by
                    rw [hpc]
                  _ = second.pc := hnextPC.symm
              have hheadTail : headPC (second :: tail) = some next.pc := by
                simp [headPC, hnextPC']
              have htail := ih (template := (second :: tail).map
                (fun site => site.located.instruction)) (by rfl) htailCont next
                hheadTail hadvanceTail
              cases hhalt : next.halt with
              | Running =>
                  have hloc :
                      Challenge.EvmProof.Stepper.runLocated first.located s = some next := by
                    simp [Challenge.EvmProof.Stepper.runLocated, first.pc_eq, hpc, hrunFirst]
                  change (match Challenge.EvmProof.Stepper.runLocated first.located s with
                    | none => none
                    | some next' =>
                        match (second :: tail).map (fun site => site.located) with
                        | [] => some next'
                        | _ :: _ =>
                            match next'.halt with
                            | .Running => Challenge.EvmProof.Stepper.runLocatedBlock
                                ((second :: tail).map (fun site => site.located)) next'
                            | _ => none) =
                    runInstrSeq (first.located.instruction ::
                      (second :: tail).map (fun site => site.located.instruction)) s
                  rw [hloc]
                  simp only [runInstrSeq, List.map]
                  rw [hrunFirst]
                  simp only [hhalt]
                  exact htail
              | Success =>
                  simp [LocatedSite.path,
                    Challenge.EvmProof.Stepper.runLocatedBlock,
                    runInstrSeq, Challenge.EvmProof.Stepper.runLocated,
                    first.pc_eq, hpc, hrunFirst, hhalt]
              | Returned =>
                  simp [LocatedSite.path,
                    Challenge.EvmProof.Stepper.runLocatedBlock,
                    runInstrSeq, Challenge.EvmProof.Stepper.runLocated,
                    first.pc_eq, hpc, hrunFirst, hhalt]
              | Reverted =>
                  simp [LocatedSite.path,
                    Challenge.EvmProof.Stepper.runLocatedBlock,
                    runInstrSeq, Challenge.EvmProof.Stepper.runLocated,
                    first.pc_eq, hpc, hrunFirst, hhalt]
              | Exception error =>
                  simp [LocatedSite.path,
                    Challenge.EvmProof.Stepper.runLocatedBlock,
                    runInstrSeq, Challenge.EvmProof.Stepper.runLocated,
                    first.pc_eq, hpc, hrunFirst, hhalt]

theorem runLocatedBlock_eq_runInstrSeq_site
    {artifact : ProgramArtifact} {fork : Fork} {template : List Instr}
    (site : GenericRoundSite artifact fork template) (s : State)
    (hhead : s.pc = site.startPC)
    (hadvance : ∀ located, located ∈ site.sites →
      ∀ {u v : State},
        Challenge.EvmProof.Stepper.runInstr located.located.instruction u = some v →
          v.pc = u.pc + UInt256.ofNat located.located.instruction.size) :
    Challenge.EvmProof.Stepper.runLocatedBlock site.path s =
      runInstrSeq template s := by
  apply runLocatedBlock_eq_runInstrSeq site.sites template
    site.instruction_eq site.contiguous s
  · rw [site.head_eq]
    exact congrArg some hhead.symm
  · exact hadvance

/-! ## Direct f0 evaluator trace -/

private theorem maskedRotateAdd (q e r r' : UInt256) :
    UInt256.land mask
        (UInt256.add
          (((mask.land q).shiftLeft r).lor
            ((mask.land q).shiftRight r')) e) =
      UInt256.land
        (UInt256.add
          (((q.land mask).shiftLeft r).lor
            ((q.land mask).shiftRight r')) e) mask := by
  rw [Word.land_comm mask q]
  exact Word.land_comm _ _

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_f0 (s : State) (startPC : UInt256)
    (a b c d e xAddress : UInt256) (rotation : Nat) (rest : List UInt256)
    (hstack : rest.length < 1015) (hrun : s.halt = .Running) :
    runInstrSeq (f0Template xAddress rotation)
        (roundEntry s startPC a b c d e rest) =
      some (roundReturned s
        (pcAfter startPC (f0Template xAddress rotation))
        0 a b c d e xAddress rotation 0 rest) := by
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by
    omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  have hswap2 (u v w : UInt256) (rho : List UInt256) :
      (u :: v :: w :: rho).exchange 0 2 = some (w :: v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u w [v] rho
  have hswap3 (u v w z : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: rho).exchange 0 3 =
        some (z :: v :: w :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u z [v, w] rho
  have hswap4 (u v w z q : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: rho).exchange 0 4 =
        some (q :: v :: w :: z :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u q [v, w, z] rho
  have hadd (u v : UInt256) : u + v = u.add v := by
    rfl
  have hzero (u : UInt256) : u.add (0 : UInt256) = u := by
    apply Word.word_ext
    change (u.val + (0 : UInt256).val).val = u.val.val
    rw [Fin.val_add]
    change (u.val.val + 0) % UInt256.size = u.val.val
    rw [Nat.add_zero, Nat.mod_eq_of_lt u.val.isLt]
  have hcomm (u v : UInt256) : u.add v = v.add u := by
    exact Word.word_add_comm u v
  have hxorcomm (u v : UInt256) : u.xor v = v.xor u := by
    exact BooleanSelect.xor_comm u v
  have hfxor : d.xor (c.xor b) = d.xor (b.xor c) := by
    exact congrArg (fun u => d.xor u) (hxorcomm c b)
  simp (config := { maxSteps := 2000000 })
    [f0Template, op, push1, push2, push4, dup1, dup2, dup3, dup4, dup5,
      dup6, swap1, swap2, swap3, swap4, mask, c10, c22,
      runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      roundEntry, roundReturned, roundWords, roundResult, roundWorking,
      roundWord, pcAfter, StackRound.stackRound, StackRound.stackF,
      StackRound.stackSum, StackRound.stackRawRot, StackRound.stackC10,
      Word.mask32, List.exchange, hrun, hcap, hswap1, hswap2, hswap3,
      hswap4, UInt256.succ, Instr.size, Instr.size_push, Instr.size_op,
      Nat.add_assoc, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, Word.land_comm, Word.lor_comm,
      BooleanSelect.xor_comm, State.activeWordsAfterUInt256, hadd, hzero,
      hfxor]
  constructor
  · rw [hcomm e]
    rw [hcomm (MachineState.readWord s.memory xAddress.toNat)
      ((d.xor (b.xor c)).add a)]
    let q : UInt256 :=
      ((d.xor (b.xor c)).add a).add
        (MachineState.readWord s.memory xAddress.toNat)
    change
      UInt256.land (UInt256.ofNat 4294967295)
          (UInt256.add
            (UInt256.lor
              (UInt256.shiftLeft
                (UInt256.land (UInt256.ofNat 4294967295) q)
                (UInt256.ofNat rotation))
              (UInt256.shiftRight
                (UInt256.land (UInt256.ofNat 4294967295) q)
                (UInt256.ofNat (32 - rotation)))) e) =
        UInt256.land
          (UInt256.add
            (UInt256.lor
              (UInt256.shiftLeft
                (UInt256.land q (UInt256.ofNat 4294967295))
                (UInt256.ofNat rotation))
              (UInt256.shiftRight
                (UInt256.land q (UInt256.ofNat 4294967295))
                (UInt256.ofNat (32 - rotation)))) e)
          (UInt256.ofNat 4294967295)
    rw [Word.land_comm (UInt256.ofNat 4294967295) q]
    exact Word.land_comm _ _
  · exact Word.land_comm _ _

theorem runLocatedBlock_f0
    {artifact : ProgramArtifact} {fork : Fork}
    (xAddress : UInt256) (rotation : Nat)
    (site : GenericRoundSite artifact fork (f0Template xAddress rotation))
    (s : State) (a b c d e : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock site.path
        (roundEntry s site.startPC a b c d e rest) =
      some (roundReturned s site.endPC
        0 a b c d e xAddress rotation 0 rest) := by
  have hpc : site.endPC =
      pcAfter site.startPC (f0Template xAddress rotation) := by
    calc
      site.endPC = pcAfter site.startPC
          (site.sites.map (fun q => q.located.instruction)) :=
        endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
          site.head_eq site.end_eq site.contiguous
      _ = pcAfter site.startPC (f0Template xAddress rotation) := by
        rw [site.instruction_eq]
  have hadvance : ∀ located, located ∈ site.sites →
      ∀ {u v : State},
        Challenge.EvmProof.Stepper.runInstr located.located.instruction u = some v →
      v.pc = u.pc + UInt256.ofNat located.located.instruction.size := by
    intro located hmem u v hresult
    have hstraight : StraightLine located.located.instruction := by
      apply f0Template_straight
      rw [← site.instruction_eq]
      exact List.mem_map_of_mem hmem
    exact runInstr_pc_of_straight hstraight hresult
  calc
    Challenge.EvmProof.Stepper.runLocatedBlock site.path
        (roundEntry s site.startPC a b c d e rest) =
        runInstrSeq (f0Template xAddress rotation)
          (roundEntry s site.startPC a b c d e rest) :=
      runLocatedBlock_eq_runInstrSeq_site site
        (roundEntry s site.startPC a b c d e rest) rfl hadvance
    _ = some (roundReturned s
        (pcAfter site.startPC (f0Template xAddress rotation))
        0 a b c d e xAddress rotation 0 rest) :=
      runInstrSeq_f0 s site.startPC a b c d e xAddress rotation rest
        hstack hrun
    _ = some (roundReturned s site.endPC
        0 a b c d e xAddress rotation 0 rest) := by
      rw [hpc]

def gasSteps_f0
    {artifact : ProgramArtifact} {fork : Fork}
    (xAddress : UInt256) (rotation : Nat)
    (site : GenericRoundSite artifact fork (f0Template xAddress rotation))
    (s : State) (a b c d e : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015)
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (roundEntry s site.startPC a b c d e rest)
      (roundReturned s site.endPC
        0 a b c d e xAddress rotation 0 rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound artifact fork site.path
  · simpa [roundEntry] using hcode
  · simpa [roundEntry] using hfork
  · exact runLocatedBlock_f0 xAddress rotation site s a b c d e rest hstack hrun
  · simpa [roundEntry] using hrun
  · simpa [roundEntry] using hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
