import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackEndpoint

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLoadSeams

open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM
open StackBlockModel StackEndpoint

theorem firstLoad_end : StackFrame.loadSite987.endPC = QuadLayout.leftPC 0 := rfl

theorem secondLoad_start : StackFrame.loadSite1238.startPC = UInt256.ofNat 0x76a := rfl

theorem secondLoad_end : StackFrame.loadSite1238.endPC = QuadLayout.rightPC 0 := rfl

theorem loadReturned_eq_roundEntry (s : State) (pc : UInt256) (rest : List UInt256) :
    StackLoadTrace.loadReturned s pc rest =
      StackRoundTrace.roundEntry s pc (initialWorking s).a (initialWorking s).b
        (initialWorking s).c (initialWorking s).d (initialWorking s).e rest := rfl

theorem loadEntry_eq_roundEntry (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (rest : List UInt256) :
    StackLoadTrace.loadEntry s pc (StackRoundTrace.roundWords w ++ rest) =
      StackRoundTrace.roundEntry s pc w.a w.b w.c w.d w.e rest := rfl

theorem tailEntry_eq_roundEntry (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) :
    QuadTailTemplate.tailEntry s left right ret rest =
      StackRoundTrace.roundEntry s (UInt256.ofNat 0x9a9)
        right.a right.b right.c right.d right.e
        (QuadRoundTemplate.factor :: (StackFrame.savedLeft left ++ ret :: rest)) := rfl

theorem firstLoad_entry (s : State) (input : ByteArray) (i : Nat) :
    StackLoadTrace.loadEntry (scheduledState s input i) StackFrame.loadSite987.startPC
      (QuadRoundTemplate.factor :: StackFrame.frameRest input i) =
        StackFrame.frameLoadEntry s input i := by
  rw [StackFrame.loadSite987_startPC]
  rfl

theorem firstLoad_returned (s : State) (rest : List UInt256) :
    StackLoadTrace.loadReturned s StackFrame.loadSite987.endPC rest =
      StackRoundTrace.roundEntry s (QuadLayout.leftPC 0)
        (initialWorking s).a (initialWorking s).b (initialWorking s).c
        (initialWorking s).d (initialWorking s).e rest := by
  rw [firstLoad_end]
  exact loadReturned_eq_roundEntry s _ rest

theorem routeEntry_atLanePC (s : State) (left : Compression.EvmWorking)
    (rest : List UInt256) :
    StackFrame.routeEntry s left rest =
      StackRoundTrace.roundEntry s (QuadLayout.leftPC 20)
        left.a left.b left.c left.d left.e (QuadRoundTemplate.factor :: rest) := rfl

theorem secondLoad_entry (s : State) (left : Compression.EvmWorking)
    (rest : List UInt256) :
    StackLoadTrace.loadEntry s StackFrame.loadSite1238.startPC
      (QuadRoundTemplate.factor :: (StackFrame.savedLeft left ++ rest)) =
      StackFrame.routeReturned s left rest := by
  rw [secondLoad_start]
  rfl

theorem secondLoad_returned (s : State) (rest : List UInt256) :
    StackLoadTrace.loadReturned s StackFrame.loadSite1238.endPC rest =
      StackRoundTrace.roundEntry s (QuadLayout.rightPC 0)
        (initialWorking s).a (initialWorking s).b (initialWorking s).c
        (initialWorking s).d (initialWorking s).e rest := by
  rw [secondLoad_end]
  exact loadReturned_eq_roundEntry s _ rest

theorem tailEntry_atLanePC (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) :
    QuadTailTemplate.tailEntry s left right ret rest =
      StackRoundTrace.roundEntry s (QuadLayout.rightPC 20)
        right.a right.b right.c right.d right.e
        (QuadRoundTemplate.factor :: (StackFrame.savedLeft left ++ ret :: rest)) := by
  rw [StackEndpoint.rightPC_last]
  exact tailEntry_eq_roundEntry s left right ret rest

theorem compressReturned_eq_self (s : State) (input : ByteArray) (i : Nat)
    (hpc : s.pc = UInt256.ofNat 0x436) (hstack : s.stack = driverRest input i) :
    DriverTrace.compressReturned s input i = s := by
  change {s with pc := UInt256.ofNat 0x436, stack := driverRest input i} = s
  rw [← hpc, ← hstack]

theorem resultState_returned (s : State) (input : ByteArray) (i : Nat) :
    resultState s input i = DriverTrace.compressReturned (resultState s input i) input i :=
  (compressReturned_eq_self (resultState s input i) input i rfl rfl).symm

theorem scheduled_words_memory (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (ctx : StackRunBridge.BlockContext s input i h)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input)
    (k : Nat) (hk : k < 16) :
    Challenge.EvmProof.Word.toUInt32
      (MachineState.readWord (scheduledState s input i).memory (644 + 4 * k)) =
      blockWords input i k :=
  scheduledState_words s input i h ctx hfit hi k hk

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLoadSeams
