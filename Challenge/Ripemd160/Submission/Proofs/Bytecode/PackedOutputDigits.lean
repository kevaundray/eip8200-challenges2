import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputDigits

def pack (n0 n1 n2 n3 n4 : Nat) : Nat :=
  ((((n0 * 2 ^ 32 + n1) * 2 ^ 32 + n2) * 2 ^ 32 + n3) * 2 ^ 32 + n4)

def expected (n0 n1 n2 n3 n4 j : Nat) : Nat :=
  match j with
  | 3 => n0
  | 4 => n1
  | 5 => n2
  | 6 => n3
  | 7 => n4
  | _ => 0

theorem extract (n0 n1 n2 n3 n4 j : Nat)
    (h0 : n0 < 2 ^ 32) (h1 : n1 < 2 ^ 32) (h2 : n2 < 2 ^ 32)
    (h3 : n3 < 2 ^ 32) (h4 : n4 < 2 ^ 32) (hj : j < 8) :
    (pack n0 n1 n2 n3 n4 / 2 ^ (32 * (7 - j))) % 2 ^ 32 =
      expected n0 n1 n2 n3 n4 j := by
  interval_cases j <;> norm_num [pack, expected] at * <;> omega

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputDigits
