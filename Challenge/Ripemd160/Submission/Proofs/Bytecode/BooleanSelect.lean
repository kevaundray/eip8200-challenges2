import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Init.Data.BitVec.Lemmas

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanSelect

open EvmSemantics

theorem xor_comm (a b : UInt256) : a ^^^ b = b ^^^ a := by
  apply Challenge.EvmProof.Word.word_ext
  change (Fin.xor a.val b.val).val = (Fin.xor b.val a.val).val
  simp [Fin.xor, Nat.xor_comm]

theorem select1 (x y z : UInt256) :
    (x &&& y) ||| (~~~x &&& z) = ((y ^^^ z) &&& x) ^^^ z := by
  have h (a b c : BitVec 256) :
      (a &&& b) ||| (~~~a &&& c) = ((b ^^^ c) &&& a) ^^^ c := by
    ext i
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not,
      BitVec.getElem_xor]
    generalize a[i] = av, b[i] = bv, c[i] = cv
    cases av <;> cases bv <;> cases cv <;> rfl
  have h' := congrArg (fun a : BitVec 256 => UInt256.mk a.toFin)
    (h (BitVec.ofFin x.val) (BitVec.ofFin y.val) (BitVec.ofFin z.val))
  have hnot (a : UInt256) :
      (~~~(BitVec.ofFin a.val) : BitVec 256).toFin = (~~~a).val := by
    apply Fin.ext
    change (~~~(BitVec.ofFin a.val) : BitVec 256).toNat =
      (UInt256.ofNat (2 ^ 256 - 1 - a.toNat)).toNat
    rw [BitVec.toNat_not, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    rfl
  simp only [BitVec.toFin_or, BitVec.toFin_and, BitVec.toFin_xor,
    hnot] at h'
  exact h'

theorem select3 (x y z : UInt256) :
    (x &&& z) ||| (y &&& ~~~z) = ((x ^^^ y) &&& z) ^^^ y := by
  rw [show x &&& z = z &&& x from Word.land_comm _ _,
    show y &&& ~~~z = ~~~z &&& y from Word.land_comm _ _]
  exact select1 z x y

end Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanSelect
