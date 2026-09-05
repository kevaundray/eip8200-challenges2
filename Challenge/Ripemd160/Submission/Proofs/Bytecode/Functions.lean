import Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import YulEvmCompiler.LowerDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# Direct traces for RIPEMD-160 helper functions

The Yul compiler gives value-returning helpers an explicit zero result slot
and return destination.  These reusable traces expose that convention while
remaining parametric in the caller's stack suffix.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Functions

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def rotlPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨2, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨5, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨7, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨8, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨9, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨10, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨11, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨12, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨13, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨14, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨15, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def rotlValue (x n : UInt256) : UInt256 :=
  Challenge.EvmProof.Word.mask32
    (UInt256.shiftLeft x n |||
      UInt256.shiftRight x (UInt256.ofNat 32 - n))

def rotlEntry (s : State) (x n returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4
           stack := [x, n, 0, returnDest] ++ rest }

def rotlReturned (s : State) (x n returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := returnDest
           stack := rotlValue x n :: rest }

def rotlReady (s : State) (x n returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 21
           stack := [rotlValue x n, returnDest] ++ rest }

def rotlBodyPath := rotlPath.take 12
def rotlReturnPath := rotlPath.drop 12

@[simp] private theorem rotlPC (i : Nat) (hlo : 2 ≤ i) (hhi : i ≤ 19) :
    Artifact.instructionPC i =
      [4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 19, 20, 21, 22, 23, 24, 25, 26][i - 2]! := by
  interval_cases i <;> rfl

@[simp] private theorem rotlRefPC (i : Nat) (hlo : 2 ≤ i) (hhi : i ≤ 19) :
    Artifact.submissionArtifact.instructionPC i =
      [4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 19, 20, 21, 22, 23, 24, 25, 26][i - 2]! := by
  interval_cases i <;> rfl

set_option linter.unnecessarySeqFocus false in
set_option linter.unusedSimpArgs false in
theorem run_rotlBody (s : State) (x n returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rotlBodyPath
      (rotlEntry s x n returnDest rest) =
        some (rotlReady s x n returnDest rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hswap3 (a b c d : UInt256) (rho : List UInt256) :
      (a :: b :: c :: d :: rho).exchange 0 3 =
        some (d :: b :: c :: a :: rho) := by
    simpa using YulEvmCompiler.exchange_swap a d [b, c] rho
  simp [rotlBodyPath, rotlPath, Word.land_comm, Word.lor_comm, List.exchange,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rotlEntry, rotlReady, rotlValue, Challenge.EvmProof.Word.mask32,
    hc3, hc4, hc5, hc6, hc7, hc8, hrun,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, hswap3]
  exact Word.land_comm _ _

set_option linter.unusedSimpArgs false in
theorem run_rotlReturn (s : State) (x n returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock rotlReturnPath
      (rotlReady s x n returnDest rest) =
        some (rotlReturned s x n returnDest rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hswap (a b : UInt256) (rho : List UInt256) :
      (a :: b :: rho).exchange 0 1 = some (b :: a :: rho) := by
    simpa using YulEvmCompiler.exchange_swap a b ([] : List UInt256) rho
  simp [rotlReturnPath, rotlPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rotlReady, rotlReturned, hc2, hc3, hrun, hcode, hvalid, hswap,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat]

def gasSteps_rotl (s : State) (x n returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (rotlEntry s x n returnDest rest)
      (rotlReturned s x n returnDest rest) := by
  have hcodeEntry :
      (rotlEntry s x n returnDest rest).executionEnv.code = submissionBytecode := by
    simpa [rotlEntry] using hcode
  have hforkEntry : (rotlEntry s x n returnDest rest).fork = .Osaka := by
    simpa [rotlEntry] using hfork
  have hrunEntry : (rotlEntry s x n returnDest rest).halt = .Running := by
    simpa [rotlEntry] using hrun
  have hnpEntry : Precompile.isPrecompileWithConfig (rotlEntry s x n returnDest rest).executionEnv.precompileConfig (rotlEntry s x n returnDest rest).executionEnv.fork
      (rotlEntry s x n returnDest rest).executionEnv.codeAddr = false := by
    simpa [rotlEntry] using hnp
  have gbody := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka rotlBodyPath hcodeEntry hforkEntry
      (run_rotlBody s x n returnDest rest hstack hrun) hrunEntry hnpEntry
  have hcodeReady :
      (rotlReady s x n returnDest rest).executionEnv.code = submissionBytecode := by
    simpa [rotlReady] using hcode
  have hforkReady : (rotlReady s x n returnDest rest).fork = .Osaka := by
    simpa [rotlReady] using hfork
  have hrunReady : (rotlReady s x n returnDest rest).halt = .Running := by
    simpa [rotlReady] using hrun
  have hnpReady : Precompile.isPrecompileWithConfig (rotlReady s x n returnDest rest).executionEnv.precompileConfig (rotlReady s x n returnDest rest).executionEnv.fork
      (rotlReady s x n returnDest rest).executionEnv.codeAddr = false := by
    simpa [rotlReady] using hnp
  have greturn := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka rotlReturnPath hcodeReady hforkReady
      (run_rotlReturn s x n returnDest rest (by omega) hcode hrun hvalid)
      hrunReady hnpReady
  exact gbody.trans greturn

theorem rotlValue_ofUInt32 (x : UInt32) (n : Nat)
    (hn0 : 0 < n) (hn : n < 32) :
    rotlValue (Challenge.EvmProof.Word.ofUInt32 x) (UInt256.ofNat n) =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.rotl32 x n) := by
  unfold rotlValue
  rw [Challenge.EvmProof.Word.ofNat_sub_ofNat
    (a := 32) (b := n) (by omega) (by norm_num)]
  exact Challenge.EvmProof.Word.evm_rotl32 x n hn0 hn

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Functions
