import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleCorrect
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Memory
import Mathlib.Tactic.Ring

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleMemory

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof

/-! The dense model uses the same two-stage byte reversal as the packed
schedule.  The local definitions keep this bridge independent of any trace
module. -/

namespace DensePacked

abbrev EWord := EvmSemantics.UInt256

def shr (v : EWord) (n : Nat) : EWord :=
  UInt256.shiftRight v (UInt256.ofNat n)

def shl (v : EWord) (n : Nat) : EWord :=
  UInt256.shiftLeft v (UInt256.ofNat n)

def mask8 : EWord :=
  UInt256.ofNat 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff

def mask16 : EWord :=
  UInt256.ofNat 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff

def packed (v : EWord) : EWord :=
  let t :=
    (shr v 8).land mask8 |>.lor (shl (v.land mask8) 8)
  (shr t 16).land mask16 |>.lor (shl (t.land mask16) 16)

def le4 (v : EWord) (j : Nat) : EWord :=
  let b0 := UInt256.byteAt (UInt256.ofNat (4 * j + 0)) v
  let b1 := UInt256.byteAt (UInt256.ofNat (4 * j + 1)) v
  let b2 := UInt256.byteAt (UInt256.ofNat (4 * j + 2)) v
  let b3 := UInt256.byteAt (UInt256.ofNat (4 * j + 3)) v
  (b0.lor (shl b1 8)).lor (shl b2 16 |>.lor (shl b3 24))

private theorem shr_toNat (v : EWord) (n : Nat) (hn : n < 256) :
    (shr v n).toNat = v.toNat >>> n := by
  exact Challenge.EvmProof.Word.shiftRight_toNat v hn

private theorem shl_toNat (v : EWord) (n : Nat) (hn : n < 256) :
    (shl v n).toNat = (v.toNat <<< n) % 2 ^ 256 := by
  unfold shl UInt256.shiftLeft
  have hshift : (UInt256.ofNat n).toNat = n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [if_neg (by omega), hshift,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [show UInt256.size = 2 ^ 256 by rfl, Nat.mod_mod]

private theorem lor_toNat (a b : EWord) :
    (a.lor b).toNat = a.toNat ||| b.toNat := by
  exact Challenge.EvmProof.Word.word_toNat_lor a b

private theorem land_toNat (a b : EWord) :
    (a.land b).toNat = a.toNat &&& b.toNat := by
  exact Challenge.EvmProof.Word.word_toNat_land a b

private theorem mask8_toNat : mask8.toNat =
    0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff := by
  unfold mask8
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (by norm_num)

private theorem mask16_toNat : mask16.toNat =
    0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff := by
  unfold mask16
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (by norm_num)

private theorem shr8_toNat (v : EWord) : (shr v 8).toNat = v.toNat >>> 8 := by
  exact shr_toNat v 8 (by norm_num)

private theorem shr16_toNat (v : EWord) : (shr v 16).toNat = v.toNat >>> 16 := by
  exact shr_toNat v 16 (by norm_num)

private theorem shl8_toNat (v : EWord) :
    (shl v 8).toNat = (v.toNat <<< 8) % 2 ^ 256 := by
  exact shl_toNat v 8 (by norm_num)

private theorem shl16_toNat (v : EWord) :
    (shl v 16).toNat = (v.toNat <<< 16) % 2 ^ 256 := by
  exact shl_toNat v 16 (by norm_num)

private theorem shl24_toNat (v : EWord) :
    (shl v 24).toNat = (v.toNat <<< 24) % 2 ^ 256 := by
  exact shl_toNat v 24 (by norm_num)

private theorem byteAt_toNat (v : EWord) (i : Nat) (hi : i < 32) :
    (UInt256.byteAt (UInt256.ofNat i) v).toNat =
      (v.toNat >>> (8 * (31 - i))) &&& 0xff := by
  unfold UInt256.byteAt
  have hi256 : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans hi (by norm_num))
  rw [hi256, if_neg (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat]
  have hlow :
      (v.toNat >>> (8 * (31 - i))) &&& 0xff ≤ 0xff := Nat.and_le_right
  exact Nat.mod_eq_of_lt (by omega)

theorem packed_extract (v : EWord) (j : Nat) (hj : j < 8) :
    Challenge.EvmProof.Word.mask32 (shr (packed v) (32 * (7 - j))) =
      Challenge.EvmProof.Word.mask32 (le4 v j) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.mask32_toNat,
    Challenge.EvmProof.Word.mask32_toNat]
  rw [show 0xffffffff = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 32
  · simp only [Nat.testBit_mod_two_pow, hk, decide_true, Bool.true_and]
    simp only [packed, le4]
    rw [shr_toNat _ _ (by omega)]
    repeat
      first
      | rw [lor_toNat]
      | rw [land_toNat]
      | rw [shr8_toNat]
      | rw [shr16_toNat]
      | rw [shl8_toNat]
      | rw [shl16_toNat]
      | rw [shl24_toNat]
      | rw [mask8_toNat]
      | rw [mask16_toNat]
    rw [byteAt_toNat v (4 * j + 0) (by omega),
      byteAt_toNat v (4 * j + 1) (by omega),
      byteAt_toNat v (4 * j + 2) (by omega),
      byteAt_toNat v (4 * j + 3) (by omega)]
    simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_or,
      Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
    interval_cases j <;> interval_cases k <;>
      norm_num [Nat.testBit_eq_decide_div_mod_eq]
  · simp only [Nat.testBit_mod_two_pow, hk, decide_false, Bool.false_and]

theorem le4_readWord_offset (bytes : ByteArray) (offset j : Nat) (hj : j < 8) :
    le4 (MachineState.readWord bytes offset) j =
      le4 (MachineState.readWord bytes (offset + 4 * j)) 0 := by
  simp only [le4, Nat.mul_zero, Nat.zero_add]
  rw [Challenge.EvmProof.Bytes.byteAt_readWord bytes offset (4 * j + 0) (by omega),
    Challenge.EvmProof.Bytes.byteAt_readWord bytes offset (4 * j + 1) (by omega),
    Challenge.EvmProof.Bytes.byteAt_readWord bytes offset (4 * j + 2) (by omega),
    Challenge.EvmProof.Bytes.byteAt_readWord bytes offset (4 * j + 3) (by omega),
    Challenge.EvmProof.Bytes.byteAt_readWord bytes (offset + 4 * j) 0 (by omega),
    Challenge.EvmProof.Bytes.byteAt_readWord bytes (offset + 4 * j) 1 (by omega),
    Challenge.EvmProof.Bytes.byteAt_readWord bytes (offset + 4 * j) 2 (by omega),
    Challenge.EvmProof.Bytes.byteAt_readWord bytes (offset + 4 * j) 3 (by omega)]
  have h0 : offset + (4 * j + 0) = offset + 4 * j + 0 := by omega
  have h1 : offset + (4 * j + 1) = offset + 4 * j + 1 := by omega
  have h2 : offset + (4 * j + 2) = offset + 4 * j + 2 := by omega
  have h3 : offset + (4 * j + 3) = offset + 4 * j + 3 := by omega
  rw [h0, h1, h2, h3]

private theorem shr_zero (v : EWord) : shr v 0 = v := by
  apply Challenge.EvmProof.Word.word_ext
  unfold shr UInt256.shiftRight
  have hz : (UInt256.ofNat 0).toNat = 0 := by
    rfl
  rw [hz]
  split
  · omega
  change (v.val >>> (UInt256.ofNat 0).val).val = v.val.val
  rw [Fin.shiftRight_val]
  rw [show (UInt256.ofNat 0).val.val = 0 by rfl, Nat.shiftRight_zero]

theorem mask32_shr224 (v : EWord) :
    Challenge.EvmProof.Word.mask32 (shr v 224) = shr v 224 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.mask32_toNat]
  rw [show 0xffffffff = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  rw [shr_toNat v 224 (by norm_num)]
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftRight_eq_div_pow]
  apply (Nat.div_lt_iff_lt_mul (by positivity)).2
  calc
    v.toNat < 2 ^ 256 := v.val.isLt
    _ = 2 ^ 32 * 2 ^ 224 := by rw [← Nat.pow_add]

end DensePacked

def naturalp (p : Nat) : UInt256 := UInt256.ofNat p

def packedBytes (value : UInt256) : ByteArray :=
  Data.Bytes.natToBytesPadded value.toNat 32

def writePacked (memory : ByteArray) (value : UInt256) (start : Nat) : ByteArray :=
  MachineState.writeBytes memory (packedBytes value) start

theorem writePacked_comm_672_704 (bs : ByteArray) (first second : UInt256) :
    writePacked (writePacked bs second 704) first 672 =
      writePacked (writePacked bs first 672) second 704 := by
  have hfirstSize : (packedBytes first).size = 32 := by
    simp only [packedBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  have hsecondSize : (packedBytes second).size = 32 := by
    simp only [packedBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  apply ByteArray.ext_getElem
  · simp only [writePacked, MachineState.writeBytes_size]
    simp only [hfirstSize, hsecondSize]
    norm_num [Nat.max_assoc, Nat.max_comm, Nat.max_left_comm]
  · intro i hleft hright
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright]
    simp only [writePacked, packedBytes,
      MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases hfirst : 672 ≤ i ∧ i < 704
    · rw [if_pos hfirst, if_neg (by omega), if_pos hfirst]
    · by_cases hsecond : 704 ≤ i ∧ i < 736
      · rw [if_neg hfirst, if_pos hsecond, if_pos hsecond]
      · rw [if_neg hfirst, if_neg hsecond, if_neg hsecond, if_neg hfirst]

def denseMemory (bs : ByteArray) (p : Nat) : ByteArray :=
  let first := DensePacked.packed (MachineState.readWord bs p)
  let second := DensePacked.packed (MachineState.readWord bs (p + 32))
  writePacked (writePacked bs first 672) second 704

def densePackedWord (bs : ByteArray) (p i : Nat) : UInt256 :=
  let h := i / 8
  let j := i % 8
  let v := DensePacked.packed
    (MachineState.readWord bs (p + 32 * h))
  if j = 0 then
    DensePacked.shr v 224
  else if j = 7 then
    Word.mask32 v
  else
    Word.mask32 (DensePacked.shr v (32 * (7 - j)))

private theorem loadOffsetWord_toNat (p i : Nat) (hi : i < 16)
    (hbound : p + 64 < 2 ^ 256) :
    (Schedule.loadOffsetWord (naturalp p) i).toNat = p + 4 * i := by
  unfold naturalp Schedule.loadOffsetWord
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide)
    (by omega : i * 2 ^ 2 < 2 ^ 256)]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

private theorem densePackedWord_base (bs : ByteArray) (p i : Nat)
    (hi : i < 16) (hbound : p + 64 < 2 ^ 256) :
    DensePacked.le4
        (MachineState.readWord bs (p + 32 * (i / 8))) (i % 8) =
      Schedule.readLEWord bs (Schedule.loadOffsetWord (naturalp p) i) := by
  have hj : i % 8 < 8 := Nat.mod_lt _ (by omega)
  have hdivmod : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
  have hsource : p + 32 * (i / 8) + 4 * (i % 8) = p + 4 * i := by
    omega
  rw [DensePacked.le4_readWord_offset bs
    (p + 32 * (i / 8)) (i % 8) hj]
  rw [hsource]
  unfold Schedule.readLEWord
  rw [loadOffsetWord_toNat p i hi hbound]
  rfl

private theorem densePackedWord_eq_expectedWord (bs : ByteArray) (p i : Nat)
    (hi : i < 16) (hbound : p + 64 < 2 ^ 256) :
    densePackedWord bs p i =
      ScheduleCorrect.expectedWord bs (naturalp p) i := by
  have hj : i % 8 < 8 := Nat.mod_lt _ (by omega)
  have hbase := densePackedWord_base bs p i hi hbound
  by_cases hj0 : i % 8 = 0
  · simp only [densePackedWord, hj0, ↓reduceIte]
    calc
      DensePacked.shr
          (DensePacked.packed
            (MachineState.readWord bs (p + 32 * (i / 8)))) 224 = Word.mask32
          (DensePacked.shr
            (DensePacked.packed
              (MachineState.readWord bs (p + 32 * (i / 8)))) 224) :=
        (DensePacked.mask32_shr224 _).symm
      _ = Word.mask32
          (DensePacked.le4
            (MachineState.readWord bs (p + 32 * (i / 8))) (i % 8)) := by
        simpa [hj0] using
          (DensePacked.packed_extract
            (MachineState.readWord bs (p + 32 * (i / 8))) (i % 8) hj)
      _ = ScheduleCorrect.expectedWord bs (naturalp p) i := by
        rw [hbase]
        rfl
  · by_cases hj7 : i % 8 = 7
    · simp only [densePackedWord, hj7, ↓reduceIte]
      calc
        Word.mask32
            (DensePacked.packed
              (MachineState.readWord bs (p + 32 * (i / 8)))) =
            Word.mask32 (DensePacked.shr
              (DensePacked.packed
                (MachineState.readWord bs (p + 32 * (i / 8))))
              (32 * (7 - (i % 8)))) := by
          simp [hj7, DensePacked.shr_zero]
        _ = Word.mask32
            (DensePacked.le4
              (MachineState.readWord bs (p + 32 * (i / 8))) (i % 8)) :=
          DensePacked.packed_extract
            (MachineState.readWord bs (p + 32 * (i / 8))) (i % 8) hj
        _ = ScheduleCorrect.expectedWord bs (naturalp p) i := by
          rw [hbase]
          rfl
    · simp only [densePackedWord, hj0, hj7, ↓reduceIte]
      calc
        Word.mask32 (DensePacked.shr
            (DensePacked.packed
              (MachineState.readWord bs (p + 32 * (i / 8))))
            (32 * (7 - (i % 8)))) = Word.mask32
            (DensePacked.le4
              (MachineState.readWord bs (p + 32 * (i / 8))) (i % 8)) :=
          DensePacked.packed_extract
            (MachineState.readWord bs (p + 32 * (i / 8))) (i % 8) hj
        _ = ScheduleCorrect.expectedWord bs (naturalp p) i := by
          rw [hbase]
          rfl

private theorem readPadded_writeBytes_window
    (memory bytes : ByteArray) (start offset : Nat)
    (hsize : bytes.size = 32) (hoff : offset + 4 ≤ 32) :
    MachineState.readPadded
        (MachineState.writeBytes memory bytes start)
        (start + offset) 4 =
      MachineState.readPadded bytes offset 4 := by
  apply ByteArray.ext_getElem
  · simp only [Challenge.EvmProof.Memory.readPadded_size]
  · intro i hi₁ hi₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₂,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD]
    have hi : i < 4 := by simpa using hi₁
    rw [if_pos hi, if_pos hi,
      MachineState.writeBytes_getElem?_getD]
    rw [if_pos (by omega)]
    rw [show (start + offset + i) - start = offset + i by omega]

private theorem bytesToNatPadded_writeBytes_window
    (memory bytes : ByteArray) (start offset : Nat)
    (hsize : bytes.size = 32) (hoff : offset + 4 ≤ 32) :
    EVM.Precompile.bytesToNatPadded
        (MachineState.writeBytes memory bytes start)
        (start + offset) 4 =
      EVM.Precompile.bytesToNatPadded bytes offset 4 := by
  unfold EVM.Precompile.bytesToNatPadded
  rw [readPadded_writeBytes_window memory bytes start offset hsize hoff]

private theorem toUInt32_readWord_eq_last4
    (bytes : ByteArray) (offset : Nat) :
    Word.toUInt32 (MachineState.readWord bytes offset) =
      Word.toUInt32 (UInt256.ofNat
        (EVM.Precompile.bytesToNatPadded bytes (offset + 28) 4)) := by
  apply UInt32.toNat_inj.mp
  rw [Word.toUInt32_toNat, Word.toUInt32_toNat,
    Challenge.EvmProof.Bytes.readWord_toNat]
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add bytes offset 28 4
  rw [show 28 + 4 = 32 by norm_num] at hsplit
  rw [hsplit]
  have htail := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
    bytes (offset + 28) 4
  have htail256 :
      EVM.Precompile.bytesToNatPadded bytes (offset + 28) 4 < 2 ^ 256 :=
    htail.trans (by norm_num)
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt htail256]
  rw [show 256 ^ 4 = 2 ^ 32 by norm_num]
  simp [Nat.add_mod]

private theorem bytesToNatPadded_natToBytes_segment
    (n k : Nat) (hk : k ≤ 28) (hn : n < 2 ^ 256) :
    EVM.Precompile.bytesToNatPadded
        (Data.Bytes.natToBytesPadded n 32) k 4 =
      (n / 256 ^ (28 - k)) % 256 ^ 4 := by
  let bytes := Data.Bytes.natToBytesPadded n 32
  have hsize : bytes.size = 32 := by
    simp [bytes, Data.Bytes.natToBytesPadded, ByteArray.size]
  have hread : MachineState.readPadded bytes 0 32 = bytes := by
    have h := Challenge.EvmProof.Memory.readPadded_zero_size bytes
    rw [hsize] at h
    exact h
  have hfull : EVM.Precompile.bytesToNatPadded bytes 0 32 = n := by
    unfold EVM.Precompile.bytesToNatPadded
    rw [hread]
    exact Challenge.EvmProof.Memory.bytesToBigEndianNat_natToBytesPadded n 32 hn
  let restWidth := 28 - k
  have hwidth : 4 + restWidth = 32 - k := by
    dsimp [restWidth]
    omega
  have hsplit0 := Challenge.EvmProof.Bytes.bytesToNatPadded_add
    bytes 0 k (32 - k)
  rw [show 0 + k = k by omega, show k + (32 - k) = 32 by omega] at hsplit0
  have hsplit1 := Challenge.EvmProof.Bytes.bytesToNatPadded_add
    bytes k 4 restWidth
  rw [hwidth] at hsplit1
  have hdecomp :
      n =
        (EVM.Precompile.bytesToNatPadded bytes 0 k * 256 ^ 4 +
          EVM.Precompile.bytesToNatPadded bytes k 4) *
            256 ^ restWidth +
          EVM.Precompile.bytesToNatPadded bytes (k + 4) restWidth := by
    rw [← hfull, hsplit0, hsplit1]
    rw [show 32 - k = 4 + restWidth by omega, Nat.pow_add]
    ring
  have hrest := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
    bytes (k + 4) restWidth
  have hdiv :
      n / 256 ^ restWidth =
        EVM.Precompile.bytesToNatPadded bytes 0 k * 256 ^ 4 +
          EVM.Precompile.bytesToNatPadded bytes k 4 := by
    rw [hdecomp]
    have hpos : 0 < 256 ^ restWidth := by positivity
    calc
      ((EVM.Precompile.bytesToNatPadded bytes 0 k * 256 ^ 4 +
          EVM.Precompile.bytesToNatPadded bytes k 4) *
            256 ^ restWidth +
          EVM.Precompile.bytesToNatPadded bytes (k + 4) restWidth) /
          256 ^ restWidth =
          (EVM.Precompile.bytesToNatPadded bytes (k + 4) restWidth +
            256 ^ restWidth *
              (EVM.Precompile.bytesToNatPadded bytes 0 k * 256 ^ 4 +
                EVM.Precompile.bytesToNatPadded bytes k 4)) /
            256 ^ restWidth := by
        congr 1
        ring
      _ = EVM.Precompile.bytesToNatPadded bytes (k + 4) restWidth /
            256 ^ restWidth +
          (EVM.Precompile.bytesToNatPadded bytes 0 k * 256 ^ 4 +
            EVM.Precompile.bytesToNatPadded bytes k 4) :=
        Nat.add_mul_div_left _ _ hpos
      _ = EVM.Precompile.bytesToNatPadded bytes 0 k * 256 ^ 4 +
            EVM.Precompile.bytesToNatPadded bytes k 4 := by
        rw [Nat.div_eq_of_lt hrest, Nat.zero_add]
  have hseg := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow bytes k 4
  change EVM.Precompile.bytesToNatPadded bytes k 4 =
    (n / 256 ^ (28 - k)) % 256 ^ 4
  have hseg' : EVM.Precompile.bytesToNatPadded bytes k 4 < 2 ^ 32 := by
    simpa [show 256 ^ 4 = 2 ^ 32 by norm_num] using hseg
  rw [hdiv]
  rw [show 256 ^ 4 = 2 ^ 32 by norm_num, Nat.add_mod,
    Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod, Nat.zero_add]
  have hmod := Nat.mod_eq_of_lt hseg'
  rw [hmod]
  exact hmod.symm

private theorem packedBytes_size (value : UInt256) :
    (packedBytes value).size = 32 := by
  simp [packedBytes, Data.Bytes.natToBytesPadded, ByteArray.size]

private theorem packedBytes_extract (value : UInt256) (j : Nat) (hj : j < 8) :
    EVM.Precompile.bytesToNatPadded (packedBytes value) (4 * j) 4 =
      (Word.mask32
        (DensePacked.shr value (32 * (7 - j)))).toNat := by
  have hsegment := bytesToNatPadded_natToBytes_segment value.toNat
    (4 * j) (by omega) value.val.isLt
  change EVM.Precompile.bytesToNatPadded
      (Data.Bytes.natToBytesPadded value.toNat 32) (4 * j) 4 = _
  rw [hsegment, Word.mask32_toNat]
  rw [show 0xffffffff = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  unfold DensePacked.shr
  rw [Challenge.EvmProof.Word.shiftRight_toNat value (by omega),
    Nat.shiftRight_eq_div_pow]
  have hpow : 2 ^ (32 * (7 - j)) = 256 ^ (28 - 4 * j) := by
    calc
      2 ^ (32 * (7 - j)) = 2 ^ (8 * (28 - 4 * j)) := by
        congr 1
        omega
      _ = (2 ^ 8) ^ (28 - 4 * j) :=
        Nat.pow_mul 2 8 (28 - 4 * j)
      _ = 256 ^ (28 - 4 * j) := by norm_num
  rw [hpow, show 2 ^ 32 = 256 ^ 4 by norm_num]

private theorem packedBytes_packed_extract
    (value : UInt256) (j : Nat) (hj : j < 8) :
    EVM.Precompile.bytesToNatPadded
        (packedBytes (DensePacked.packed value)) (4 * j) 4 =
      (Word.mask32 (DensePacked.le4 value j)).toNat := by
  rw [packedBytes_extract (DensePacked.packed value) j hj]
  exact congrArg UInt256.toNat (DensePacked.packed_extract value j hj)

private def densePackedChunk (value : UInt256) (j : Nat) : UInt256 :=
  if j = 0 then
    DensePacked.shr value 224
  else if j = 7 then
    Word.mask32 value
  else
    Word.mask32 (DensePacked.shr value (32 * (7 - j)))

private theorem packedBytes_segment_eq_chunk
    (value : UInt256) (j : Nat) (hj : j < 8) :
    UInt256.ofNat
        (EVM.Precompile.bytesToNatPadded
          (packedBytes (DensePacked.packed value)) (4 * j) 4) =
      densePackedChunk (DensePacked.packed value) j := by
  have hsegment := packedBytes_packed_extract value j hj
  have hsegment_lt :
      EVM.Precompile.bytesToNatPadded
          (packedBytes (DensePacked.packed value)) (4 * j) 4 < 2 ^ 256 := by
    exact (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
      (packedBytes (DensePacked.packed value)) (4 * j) 4).trans (by norm_num)
  have hword :
      UInt256.ofNat
          (EVM.Precompile.bytesToNatPadded
            (packedBytes (DensePacked.packed value)) (4 * j) 4) =
        Word.mask32
          (DensePacked.shr (DensePacked.packed value) (32 * (7 - j))) := by
    apply Word.word_ext
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsegment_lt]
    calc
      EVM.Precompile.bytesToNatPadded
          (packedBytes (DensePacked.packed value)) (4 * j) 4 =
          (Word.mask32 (DensePacked.le4 value j)).toNat := hsegment
      _ = (Word.mask32
          (DensePacked.shr (DensePacked.packed value) (32 * (7 - j)))).toNat :=
        congrArg UInt256.toNat (DensePacked.packed_extract value j hj).symm
  by_cases hj0 : j = 0
  · subst j
    simp only [densePackedChunk, ↓reduceIte]
    rw [hword]
    exact DensePacked.mask32_shr224 _
  · by_cases hj7 : j = 7
    · subst j
      simp only [densePackedChunk, ↓reduceIte]
      rw [hword]
      simp [DensePacked.shr_zero]
    · simp only [densePackedChunk, hj0, hj7, ↓reduceIte]
      exact hword

private theorem denseMemory_first_window (bs : ByteArray) (p i : Nat)
    (hi : i < 8) :
    MachineState.readPadded (denseMemory bs p) (672 + 4 * i) 4 =
      MachineState.readPadded (packedBytes
        (DensePacked.packed (MachineState.readWord bs p))) (4 * i) 4 := by
  unfold denseMemory writePacked
  rw [Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint
    (MachineState.writeBytes bs
      (packedBytes (DensePacked.packed (MachineState.readWord bs p))) 672)
    (packedBytes (DensePacked.packed
      (MachineState.readWord bs (p + 32)))) (672 + 4 * i) 4 704
    (Or.inl (by omega))]
  exact readPadded_writeBytes_window bs
    (packedBytes (DensePacked.packed (MachineState.readWord bs p)))
    672 (4 * i) (packedBytes_size _) (by omega)

private theorem denseMemory_second_window (bs : ByteArray) (p i : Nat)
    (hi : 8 ≤ i) (hi16 : i < 16) :
    MachineState.readPadded (denseMemory bs p) (672 + 4 * i) 4 =
      MachineState.readPadded (packedBytes
        (DensePacked.packed (MachineState.readWord bs (p + 32))))
        (4 * (i - 8)) 4 := by
  have hindex : 672 + 4 * i = 704 + 4 * (i - 8) := by omega
  rw [hindex]
  unfold denseMemory writePacked
  rw [readPadded_writeBytes_window
    (MachineState.writeBytes bs
      (packedBytes (DensePacked.packed (MachineState.readWord bs p))) 672)
    (packedBytes (DensePacked.packed
      (MachineState.readWord bs (p + 32)))) 704 (4 * (i - 8))
    (packedBytes_size _) (by omega)]

private theorem denseMemory_first_bytesToNatPadded (bs : ByteArray) (p i : Nat)
    (hi : i < 8) :
    EVM.Precompile.bytesToNatPadded (denseMemory bs p) (672 + 4 * i) 4 =
      EVM.Precompile.bytesToNatPadded
        (packedBytes (DensePacked.packed (MachineState.readWord bs p)))
        (4 * i) 4 := by
  unfold EVM.Precompile.bytesToNatPadded
  rw [denseMemory_first_window bs p i hi]

private theorem denseMemory_second_bytesToNatPadded (bs : ByteArray) (p i : Nat)
    (hi : 8 ≤ i) (hi16 : i < 16) :
    EVM.Precompile.bytesToNatPadded (denseMemory bs p) (672 + 4 * i) 4 =
      EVM.Precompile.bytesToNatPadded
        (packedBytes (DensePacked.packed (MachineState.readWord bs (p + 32))))
        (4 * (i - 8)) 4 := by
  unfold EVM.Precompile.bytesToNatPadded
  rw [denseMemory_second_window bs p i hi hi16]

private theorem denseMemory_first_word (bs : ByteArray) (p i : Nat)
    (hi : i < 8) :
    UInt256.ofNat
        (EVM.Precompile.bytesToNatPadded
          (packedBytes (DensePacked.packed (MachineState.readWord bs p)))
          (4 * i) 4) =
      densePackedWord bs p i := by
  rw [packedBytes_segment_eq_chunk (MachineState.readWord bs p) i hi]
  have hdiv : i / 8 = 0 := Nat.div_eq_of_lt (by omega)
  have hmod : i % 8 = i := Nat.mod_eq_of_lt hi
  simp [densePackedWord, densePackedChunk, hdiv, hmod]

private theorem denseMemory_second_word (bs : ByteArray) (p i : Nat)
    (hi : 8 ≤ i) (hi16 : i < 16) :
    UInt256.ofNat
        (EVM.Precompile.bytesToNatPadded
          (packedBytes (DensePacked.packed (MachineState.readWord bs (p + 32))))
          (4 * (i - 8)) 4) =
      densePackedWord bs p i := by
  have hj : i - 8 < 8 := by omega
  rw [packedBytes_segment_eq_chunk (MachineState.readWord bs (p + 32))
    (i - 8) hj]
  have hdiv : i / 8 = 1 := by omega
  have hmod : i % 8 = i - 8 := by omega
  simp [densePackedWord, densePackedChunk, hdiv, hmod]

theorem denseMemory_readWord_low32 (bs : ByteArray) (p i : Nat)
    (hi : i < 16) (hbound : p + 64 < 2 ^ 256) :
    Word.toUInt32
        (MachineState.readWord (denseMemory bs p) (644 + 4 * i)) =
      Word.toUInt32
        (ScheduleCorrect.expectedWord bs (naturalp p) i) := by
  have hlast := toUInt32_readWord_eq_last4
    (denseMemory bs p) (644 + 4 * i)
  rw [hlast, show 644 + 4 * i + 28 = 672 + 4 * i by omega]
  by_cases hi8 : i < 8
  · rw [denseMemory_first_bytesToNatPadded bs p i hi8,
      denseMemory_first_word bs p i hi8,
      densePackedWord_eq_expectedWord bs p i hi hbound]
  · have hi8' : 8 ≤ i := by omega
    rw [denseMemory_second_bytesToNatPadded bs p i hi8' hi,
      denseMemory_second_word bs p i hi8' hi,
      densePackedWord_eq_expectedWord bs p i hi hbound]

theorem denseMemory_readWord_low32_all (bs : ByteArray) (p : Nat)
    (hbound : p + 64 < 2 ^ 256) :
    ∀ i, i < 16 →
      Word.toUInt32
          (MachineState.readWord (denseMemory bs p) (644 + 4 * i)) =
        Word.toUInt32
          (ScheduleCorrect.expectedWord bs (naturalp p) i) := by
  intro i hi
  exact denseMemory_readWord_low32 bs p i hi hbound

private theorem denseMemory_readWord_first (bs : ByteArray) (p : Nat) :
    MachineState.readWord (denseMemory bs p) 672 =
      DensePacked.packed (MachineState.readWord bs p) := by
  dsimp [denseMemory]
  unfold writePacked
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    (MachineState.writeBytes bs
      (packedBytes (DensePacked.packed (MachineState.readWord bs p))) 672)
    (packedBytes (DensePacked.packed (MachineState.readWord bs (p + 32)))) 672 704
    (Or.inl (by omega))]
  exact Challenge.EvmProof.Memory.readWord_writeWord bs 672 _

private theorem readWord_writePacked_disjoint
    (memory : ByteArray) (value : UInt256) (start address : Nat)
    (houtside : address + 32 ≤ start ∨ start + 32 ≤ address) :
    MachineState.readWord (writePacked memory value start) address =
      MachineState.readWord memory address := by
  unfold writePacked
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rcases houtside with hbefore | hafter
  · exact Or.inl hbefore
  · exact Or.inr (by rw [packedBytes_size]; omega)

theorem denseMemory_readWord_outside (bs : ByteArray) (p address : Nat)
    (houtside : address + 32 ≤ 672 ∨ 736 ≤ address) :
    MachineState.readWord (denseMemory bs p) address =
      MachineState.readWord bs address := by
  dsimp [denseMemory]
  rw [readWord_writePacked_disjoint
    (writePacked bs (DensePacked.packed (MachineState.readWord bs p)) 672)
    (DensePacked.packed (MachineState.readWord bs (p + 32))) 704 address (by
      rcases houtside with hbefore | hafter
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))]
  apply readWord_writePacked_disjoint bs
    (DensePacked.packed (MachineState.readWord bs p)) 672 address
  rcases houtside with hbefore | hafter
  · exact Or.inl hbefore
  · exact Or.inr (by omega)

example :
    Word.toUInt32
        (MachineState.readWord (denseMemory ByteArray.empty 0) 644) =
      Word.toUInt32
        (ScheduleCorrect.expectedWord ByteArray.empty (naturalp 0) 0) := by
  exact denseMemory_readWord_low32 ByteArray.empty 0 0 (by decide) (by norm_num)

example :
    Word.toUInt32
        (MachineState.readWord
          (denseMemory
            (MachineState.writeBytes ByteArray.empty
              (Data.Bytes.natToBytesPadded 1 32) 0) 0) 672) ≠
      Word.toUInt32
        (MachineState.readWord
          (MachineState.writeBytes ByteArray.empty
            (Data.Bytes.natToBytesPadded 1 32) 0) 672) := by
  have hbs0 :
      MachineState.readWord
          (MachineState.writeBytes ByteArray.empty
            (Data.Bytes.natToBytesPadded 1 32) 0) 0 = UInt256.ofNat 1 := by
    exact Challenge.EvmProof.Memory.readWord_writeBytes_of_lt
      ByteArray.empty 0 1 (by norm_num)
  have hbs672 :
      MachineState.readWord
          (MachineState.writeBytes ByteArray.empty
            (Data.Bytes.natToBytesPadded 1 32) 0) 672 = UInt256.ofNat 0 := by
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
      ByteArray.empty (Data.Bytes.natToBytesPadded 1 32) 672 0
      (Or.inr (by simp [Data.Bytes.natToBytesPadded, ByteArray.size]))]
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Bytes.readWord_toNat]
    unfold EVM.Precompile.bytesToNatPadded
    simp [MachineState.readPadded, Data.Bytes.bytesToBigEndianNat,
      Challenge.EvmProof.Bytecode.toList_eq_data]
  have hpack :
      Word.toUInt32 (DensePacked.packed (UInt256.ofNat 1)) =
        UInt32.ofNat (2 ^ 24) := by
    have hp := DensePacked.packed_extract (UInt256.ofNat 1) 7 (by norm_num)
    have hp' :
        Word.mask32 (DensePacked.packed (UInt256.ofNat 1)) =
          Word.mask32 (DensePacked.le4 (UInt256.ofNat 1) 7) := by
      simpa [DensePacked.shr_zero] using hp
    have hmask (x : UInt256) :
        Word.toUInt32 (Word.mask32 x) = Word.toUInt32 x := by
      rw [Word.mask32_eq_ofUInt32, Word.toUInt32_ofUInt32]
    calc
      Word.toUInt32 (DensePacked.packed (UInt256.ofNat 1)) =
          Word.toUInt32 (Word.mask32 (DensePacked.packed (UInt256.ofNat 1))) :=
        (hmask _).symm
      _ = Word.toUInt32 (Word.mask32 (DensePacked.le4 (UInt256.ofNat 1) 7)) :=
        congrArg Word.toUInt32 hp'
      _ = Word.toUInt32 (DensePacked.le4 (UInt256.ofNat 1) 7) := hmask _
      _ = UInt32.ofNat (2 ^ 24) := by
        apply UInt32.toNat_inj.mp
        simp only [Word.toUInt32_toNat, DensePacked.le4,
          DensePacked.lor_toNat,
          DensePacked.shl_toNat _ 8 (by norm_num),
          DensePacked.shl_toNat _ 16 (by norm_num),
          DensePacked.shl_toNat _ 24 (by norm_num),
          DensePacked.byteAt_toNat _ 28 (by norm_num),
          DensePacked.byteAt_toNat _ 29 (by norm_num),
          DensePacked.byteAt_toNat _ 30 (by norm_num),
          DensePacked.byteAt_toNat _ 31 (by norm_num)]
        norm_num [Word.word_toNat_ofNat, Nat.shiftLeft_eq,
          Nat.shiftRight_eq_div_pow]
  intro h
  rw [denseMemory_readWord_first, hbs0, hbs672, hpack] at h
  have hnat := congrArg UInt32.toNat h
  norm_num [Word.toUInt32, UInt256.ofNat, UInt256.toNat] at hnat

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleMemory
