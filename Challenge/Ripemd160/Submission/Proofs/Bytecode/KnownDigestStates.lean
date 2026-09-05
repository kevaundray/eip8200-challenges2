import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestD

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestStates

open KnownInputDigest

def knownAt (i : Nat) : Array UInt32 :=
  match i with
  | 0 => H0
  | 1 => H1
  | 2 => H2
  | 3 => H3
  | 4 => H4
  | 5 => H5
  | 6 => H6
  | 7 => H7
  | 8 => H8
  | 9 => H9
  | 10 => H10
  | 11 => H11
  | 12 => H12
  | 13 => H13
  | 14 => H14
  | 15 => H15
  | _ => H16

theorem paddedMessage_split :
    Padding.paddedMessage KnownInputData.targetInput =
      KnownInputData.targetInput ++
        (ByteArray.mk #[0x80] ++ Padding.zeroBytes KnownInputData.targetInput.size ++
          Padding.lengthBytes KnownInputData.targetInput) := by
  unfold Padding.paddedMessage
  simp only [ByteArray.append_assoc]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestStates
