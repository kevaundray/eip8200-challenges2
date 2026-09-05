import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Schedule

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleState

open EvmSemantics
open EvmSemantics.EVM

private theorem loopState_unchanged (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    s.gasAvailable = (Schedule.loopState s msgOff returnDest rest i).gasAvailable ∧
    s.returnData = (Schedule.loopState s msgOff returnDest rest i).returnData ∧
    s.hReturn = (Schedule.loopState s msgOff returnDest rest i).hReturn ∧
    s.accountMap = (Schedule.loopState s msgOff returnDest rest i).accountMap ∧
    s.substate = (Schedule.loopState s msgOff returnDest rest i).substate ∧
    s.executionEnv = (Schedule.loopState s msgOff returnDest rest i).executionEnv ∧
    s.execLength = (Schedule.loopState s msgOff returnDest rest i).execLength ∧
    s.halt = (Schedule.loopState s msgOff returnDest rest i).halt ∧
    s.callStack = (Schedule.loopState s msgOff returnDest rest i).callStack := by
  induction i with
  | zero =>
      simp [Schedule.loopState, Schedule.loopAt]
  | succ i ih =>
      simpa [Schedule.loopState, Schedule.afterIteration,
        Schedule.afterStore, Schedule.afterRead] using ih

private theorem state_frame_of_components (s q : State)
    (newPC : UInt256) (newStack : List UInt256)
    (hgas : s.gasAvailable = q.gasAvailable)
    (hreturnData : s.returnData = q.returnData)
    (hhReturn : s.hReturn = q.hReturn)
    (haccountMap : s.accountMap = q.accountMap)
    (hsubstate : s.substate = q.substate)
    (hexecutionEnv : s.executionEnv = q.executionEnv)
    (hexecLength : s.execLength = q.execLength)
    (hhalt : s.halt = q.halt)
    (hcallStack : s.callStack = q.callStack) :
    { s with
      pc := newPC
      stack := newStack
      memory := q.memory
      activeWords := q.activeWords } =
      { q with
        pc := newPC
        stack := newStack } := by
  cases s with
  | mk sShared sPC sStack sExec sHalt sCall =>
      cases q with
      | mk qShared qPC qStack qExec qHalt qCall =>
          cases sShared with
          | mk sMachine sAccount sSubstate sExecutionEnv =>
              cases qShared with
              | mk qMachine qAccount qSubstate qExecutionEnv =>
                  cases sMachine with
                  | mk sGas sActive sMemory sReturnData sHReturn =>
                      cases qMachine with
                      | mk qGas qActive qMemory qReturnData qHReturn =>
                          simp_all

private theorem loopState_frame_override (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat)
    (newPC : UInt256) (newStack : List UInt256) :
    { s with
      pc := newPC
      stack := newStack
      memory := (Schedule.loopState s msgOff returnDest rest i).memory
      activeWords := (Schedule.loopState s msgOff returnDest rest i).activeWords } =
      { Schedule.loopState s msgOff returnDest rest i with
        pc := newPC
        stack := newStack } := by
  rcases loopState_unchanged s msgOff returnDest rest i with
    ⟨hgas, hreturnData, hhReturn, haccountMap, hsubstate, hexecutionEnv,
      hexecLength, hhalt, hcallStack⟩
  exact state_frame_of_components s (Schedule.loopState s msgOff returnDest rest i)
    newPC newStack hgas hreturnData hhReturn haccountMap hsubstate hexecutionEnv
    hexecLength hhalt hcallStack

theorem returned_eq_schedule_of_memory_active (s : State)
    (startPC p ret : UInt256) (rest : List UInt256)
    (hmemory :
      PackedScheduleTemplate.expectedMemory s p =
        (Schedule.loopState s p ret rest 16).memory)
    (hactive :
      PackedScheduleTemplate.expectedActiveWords s p =
        (Schedule.loopState s p ret rest 16).activeWords) :
    Schedule.scheduleReturned
        (PackedScheduleTemplate.expectedState s startPC p ret rest) ret rest =
      Schedule.scheduleReturned
        (Schedule.loopState s p ret rest 16) ret rest := by
  unfold Schedule.scheduleReturned PackedScheduleTemplate.expectedState
  rw [hmemory, hactive]
  exact loopState_frame_override s p ret rest 16 ret rest

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleState
