import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputGuardPaths
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputSelectorPaths
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputBodyPaths0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputBodyPaths1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputBodyPaths2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputBodyPaths3

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath (i : Nat) : List Located :=
  match i with
  | 0 => bodyPath0
  | 1 => bodyPath1
  | 2 => bodyPath2
  | 3 => bodyPath3
  | 4 => bodyPath4
  | 5 => bodyPath5
  | 6 => bodyPath6
  | 7 => bodyPath7
  | 8 => bodyPath8
  | 9 => bodyPath9
  | 10 => bodyPath10
  | 11 => bodyPath11
  | 12 => bodyPath12
  | 13 => bodyPath13
  | 14 => bodyPath14
  | _ => bodyPath15

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
