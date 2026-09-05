import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleActiveWords
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Schedule
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackBlockModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLoadTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

/-!
# H30b compression frame

This module certifies the frame around the scheduled compression body.  The
compression body itself starts at the load-entry seam.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackFrame

open Challenge.Ripemd160
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Stepper
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def prefixPath : List Located :=
  [⟨913, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨914, .push ⟨2, by decide⟩ (UInt256.ofNat 0x523), by rfl, by decide⟩,
   ⟨915, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨916, .push ⟨2, by decide⟩ (UInt256.ofNat 0x109f), by rfl, by decide⟩,
   ⟨917, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def exitPath : List Located :=
  [⟨919, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨920, .push ⟨5, by decide⟩ QuadRoundTemplate.factor, by rfl, by decide⟩]

def loadSite987 : GenericRoundSite Artifact.submissionArtifact .Osaka
    StackLoadTrace.loadTemplate :=
  StackSiteBuilder.ofSlice (artifact := Artifact.submissionArtifact) (fork := .Osaka)
    StackLoadTrace.loadTemplate 921 (by rfl) (by decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := StackLoadTrace.loadTemplate) (by decide))
    (by simp [StackLoadTrace.loadTemplate])

def loadSite1238 : GenericRoundSite Artifact.submissionArtifact .Osaka
    StackLoadTrace.loadTemplate :=
  StackSiteBuilder.ofSlice (artifact := Artifact.submissionArtifact) (fork := .Osaka)
    StackLoadTrace.loadTemplate 1172 (by rfl) (by decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := StackLoadTrace.loadTemplate) (by decide))
    (by simp [StackLoadTrace.loadTemplate])

@[simp] theorem loadSite987_startPC : loadSite987.startPC = UInt256.ofNat 0x52a := by
  rfl

@[simp] theorem loadSite1238_startPC : loadSite1238.startPC = UInt256.ofNat 0x76a := by
  rfl

def frameRest (input : ByteArray) (i : Nat) : List UInt256 :=
  UInt256.ofNat 0x436 :: StackBlockModel.driverRest input i

def frameLoadEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  StackLoadTrace.loadEntry (StackBlockModel.scheduledState s input i)
    (UInt256.ofNat 0x52a) (QuadRoundTemplate.factor :: frameRest input i)

theorem frameLoadEntry_eq_loadSite987 (s : State) (input : ByteArray) (i : Nat) :
    frameLoadEntry s input i =
      StackLoadTrace.loadEntry (StackBlockModel.scheduledState s input i)
        loadSite987.startPC (QuadRoundTemplate.factor :: frameRest input i) := by
  simp [frameLoadEntry]

theorem run_prefix (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock prefixPath (DriverTrace.compressEntry s input i) =
      some (DenseScheduleTemplate.scheduleEntry s
        PackedScheduleSite.packedScheduleSite.startPC
        (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x523)
        (StackBlockModel.scheduleRest input i)) := by
  have hpc979 : Artifact.submissionArtifact.instructionPC 913 = 0x519 := by rfl
  have hpc980 : Artifact.submissionArtifact.instructionPC 914 = 0x51a := by rfl
  have hpc981 : Artifact.submissionArtifact.instructionPC 915 = 0x51d := by rfl
  have hpc982 : Artifact.submissionArtifact.instructionPC 916 = 0x51e := by rfl
  have hpc983 : Artifact.submissionArtifact.instructionPC 917 = 0x521 := by rfl
  have hdest12ac : Decode.isValidJumpDest submissionBytecode 0x109f = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2686 (by rfl)
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  simp [prefixPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    DriverTrace.compressEntry, DenseScheduleTemplate.scheduleEntry,
    PackedScheduleSite.packedScheduleSite_startPC, StackBlockModel.scheduleRest,
    StackBlockModel.driverRest, hcode, hrun, hpc979, hpc980, hpc981, hpc982, hpc983,
    hdest12ac, hswap1]

theorem run_exit (s : State) (input : ByteArray) (i : Nat)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock exitPath
        (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
          (UInt256.ofNat 0x523) (StackBlockModel.scheduleRest input i)) =
      some (frameLoadEntry s input i) := by
  have hpc985 : Artifact.submissionArtifact.instructionPC 919 = 0x523 := by rfl
  have hpc986 : Artifact.submissionArtifact.instructionPC 920 = 0x524 := by rfl
  simp [exitPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    frameLoadEntry, Schedule.scheduleReturned, StackBlockModel.scheduledState,
    StackBlockModel.scheduleRest, StackBlockModel.driverRest, frameRest,
    StackLoadTrace.loadEntry, QuadRoundTemplate.factor,
    hrun, hpc985, hpc986]

def gasSteps_prefix (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.compressEntry s input i) 
      (DenseScheduleTemplate.scheduleEntry s
        PackedScheduleSite.packedScheduleSite.startPC
        (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x523)
        (StackBlockModel.scheduleRest input i)) := by
  apply Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka prefixPath
  · exact hcode
  · exact hfork
  · exact run_prefix s input i hcode hrun
  · exact hrun
  · exact hnp

def gasSteps_schedule (s : State) (input : ByteArray) (i : Nat)
    (_hfit : CalldataFits input)
    (_hi : i < DriverTrace.blockCount input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
        (DenseScheduleTemplate.scheduleEntry s
          PackedScheduleSite.packedScheduleSite.startPC
          (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x523)
          (StackBlockModel.scheduleRest input i))
        (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
          (UInt256.ofNat 0x523) (StackBlockModel.scheduleRest input i)) := by
  let rest := StackBlockModel.scheduleRest input i
  have hstate :
      Schedule.scheduleReturned
          (DenseScheduleTemplate.denseExpectedState s
            PackedScheduleSite.packedScheduleSite.startPC
            (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x523) rest)
          (UInt256.ofNat 0x523) rest =
        Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
          (UInt256.ofNat 0x523) rest := by
    simpa [StackBlockModel.scheduledState, StackBlockModel.withMemory,
      StackBlockModel.withActiveWords] using
      (DenseScheduleState.returned_eq_schedule_with_memory_active s
        PackedScheduleSite.packedScheduleSite.startPC
        (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x523) rest
        (DenseScheduleTemplate.denseExpectedMemory s
          (DriverTrace.messageOffsetWord i)) rfl)
  have hstack1023 : rest.length < 1023 := by
    simp [rest, StackBlockModel.scheduleRest, StackBlockModel.driverRest]
  have hstack1017 : rest.length < 1017 := by
    simp [rest, StackBlockModel.scheduleRest, StackBlockModel.driverRest]
  have hraw :
      StackRoundTrace.runInstrSeq DenseScheduleTemplate.denseBeforeJumpTemplate
        (DenseScheduleTemplate.scheduleEntry s
          PackedScheduleSite.packedScheduleSite.startPC
          (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x523) rest) =
        some (DenseScheduleTemplate.denseExpectedState s
          PackedScheduleSite.packedScheduleSite.startPC
          (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x523) rest) := by
    exact DenseScheduleTrace.runInstrSeq_denseBeforeJump s
      PackedScheduleSite.packedScheduleSite.startPC
      (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x523) rest
      hstack1017 hrun
  have hartifactCode : s.executionEnv.code = Artifact.submissionArtifact.code := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  have hvalid :
      Decode.isValidJumpDest s.executionEnv.code
        (UInt256.ofNat 0x523).toNat = true := by
    rw [hcode]
    exact Artifact.submissionArtifact.isValidJumpDest_index 919 (by rfl)
  have hpacked := PackedScheduleSite.gasSteps_packedSchedule s
    (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x523) rest
    hartifactCode hfork hrun hnp hstack1023 hvalid
    hraw
  exact hpacked.cast rfl hstate

def gasSteps_exit (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
        (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
          (UInt256.ofNat 0x523) (StackBlockModel.scheduleRest input i))
        (frameLoadEntry s input i) := by
  have hqcode :
      (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
        (UInt256.ofNat 0x523) (StackBlockModel.scheduleRest input i)).executionEnv.code =
        submissionBytecode := by
    simp [StackBlockModel.scheduledState, Schedule.scheduleReturned, hcode]
  have hqfork :
      (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
        (UInt256.ofNat 0x523) (StackBlockModel.scheduleRest input i)).fork = .Osaka := by
    simpa [StackBlockModel.scheduledState, Schedule.scheduleReturned, State.fork] using hfork
  have hqrun :
      (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
        (UInt256.ofNat 0x523) (StackBlockModel.scheduleRest input i)).halt = .Running := by
    simp [StackBlockModel.scheduledState, Schedule.scheduleReturned, hrun]
  have hqnp :
      Precompile.isPrecompileWithConfig
          (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
            (UInt256.ofNat 0x523) (StackBlockModel.scheduleRest input i)).executionEnv.precompileConfig
          (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
            (UInt256.ofNat 0x523) (StackBlockModel.scheduleRest input i)).executionEnv.fork
          (Schedule.scheduleReturned (StackBlockModel.scheduledState s input i)
            (UInt256.ofNat 0x523) (StackBlockModel.scheduleRest input i)).executionEnv.codeAddr = false := by
    simpa [StackBlockModel.scheduledState, Schedule.scheduleReturned] using hnp
  apply Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka exitPath
  · exact hqcode
  · exact hqfork
  · exact run_exit s input i hrun
  · exact hqrun
  · exact hqnp

def gasSteps_frame (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.compressEntry s input i) (frameLoadEntry s input i) :=
  (gasSteps_prefix s input i hcode hfork hrun hnp).trans <|
    (gasSteps_schedule s input i hfit hi hcode hfork hrun hnp).trans <|
      gasSteps_exit s input i hcode hfork hrun hnp

def savedLeft (left : Compression.EvmWorking) : List UInt256 :=
  [left.b, left.c, left.d, left.e, left.a]

def routeEntry (s : State) (left : Compression.EvmWorking)
    (rest : List UInt256) : State :=
  StackRoundTrace.roundEntry s (UInt256.ofNat 0x769)
    left.a left.b left.c left.d left.e (QuadRoundTemplate.factor :: rest)

def routeReturned (s : State) (left : Compression.EvmWorking)
    (rest : List UInt256) : State :=
  StackLoadTrace.loadEntry s (UInt256.ofNat 0x76a)
    (QuadRoundTemplate.factor :: (savedLeft left ++ rest))

def routePath : List Located :=
  [⟨1171, .op (.Swap ⟨4, by decide⟩), by rfl,
    wfOp (by decide) trivial rfl⟩]

theorem run_route (s : State) (left : Compression.EvmWorking)
    (rest : List UInt256) (hstack : rest.length < 1007)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock routePath (routeEntry s left rest) =
      some (routeReturned s left rest) := by
  have hpc : Artifact.submissionArtifact.instructionPC 1171 = 0x769 := by rfl
  have hcap : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hswap :
      (left.a :: left.b :: left.c :: left.d :: left.e ::
        QuadRoundTemplate.factor :: rest).exchange 0 5 =
      some (QuadRoundTemplate.factor :: left.b :: left.c :: left.d :: left.e ::
        left.a :: rest) := by
    simpa using YulEvmCompiler.exchange_swap left.a QuadRoundTemplate.factor
      [left.b, left.c, left.d, left.e] rest
  simp [routePath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    routeEntry, routeReturned, StackRoundTrace.roundEntry,
    StackLoadTrace.loadEntry, savedLeft, hpc, hrun, hcap, hswap]

def gasSteps_route (s : State) (left : Compression.EvmWorking)
    (rest : List UInt256) (hstack : rest.length < 1007)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (routeEntry s left rest) (routeReturned s left rest) := by
  apply Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka routePath
  · exact hcode
  · exact hfork
  · exact run_route s left rest hstack hrun
  · exact hrun
  · exact hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackFrame
