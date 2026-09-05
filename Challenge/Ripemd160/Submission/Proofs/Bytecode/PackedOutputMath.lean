import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputDigits
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Memory
import YulEvmCompiler.BytesLemmas
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputMath

open EvmSemantics
open EvmSemantics.Crypto
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleMemory

abbrev EWord := EvmSemantics.UInt256

def append32 (acc : EWord) (w : UInt32) : EWord :=
  UInt256.lor
    (UInt256.shiftLeft acc (UInt256.ofNat 32))
    (Word.ofUInt32 w)

def pack5 (h0 h1 h2 h3 h4 : UInt32) : EWord :=
  append32 (append32 (append32 (append32 (Word.ofUInt32 h0) h1) h2) h3) h4

def pack5Nat (h0 h1 h2 h3 h4 : UInt32) : Nat :=
  ((((h0.toNat * 2 ^ 32 + h1.toNat) * 2 ^ 32 + h2.toNat) * 2 ^ 32 +
      h3.toNat) * 2 ^ 32 + h4.toNat)

def packedOutput (h0 h1 h2 h3 h4 : UInt32) : ByteArray :=
  Data.Bytes.natToBytesPadded
    (DensePacked.packed (pack5 h0 h1 h2 h3 h4)).toNat 32

def expectedOutput (h0 h1 h2 h3 h4 : UInt32) : ByteArray :=
  ByteArray.mk (Array.replicate 12 0) ++
    Ripemd160.writeLE32 ByteArray.empty h0 ++
    Ripemd160.writeLE32 ByteArray.empty h1 ++
    Ripemd160.writeLE32 ByteArray.empty h2 ++
    Ripemd160.writeLE32 ByteArray.empty h3 ++
    Ripemd160.writeLE32 ByteArray.empty h4

def expectedDigest (h0 h1 h2 h3 h4 : UInt32) : ByteArray :=
  SpecBridge.emitDigest #[h0, h1, h2, h3, h4]

def littleBytes (w : UInt32) : ByteArray :=
  ByteArray.mk #[
    ((w >>> UInt32.ofNat 0) &&& 0xff).toUInt8,
    ((w >>> UInt32.ofNat 8) &&& 0xff).toUInt8,
    ((w >>> UInt32.ofNat 16) &&& 0xff).toUInt8,
    ((w >>> UInt32.ofNat 24) &&& 0xff).toUInt8]

private theorem uint32_byte (w : UInt32) (k : Nat) (hk : k < 4) :
    ((w >>> UInt32.ofNat (8 * k)) &&& 0xff).toUInt8 =
      UInt8.ofNat (w.toNat / 256 ^ k % 256) := by
  apply UInt8.toNat_inj.mp
  rw [UInt32.toUInt8_toNat, UInt32.toNat_and,
    UInt32.toNat_shiftRight, UInt32.toNat_ofNat']
  rw [show 256 = 2 ^ 8 by norm_num, Nat.shiftRight_eq_div_pow]
  have hshift : 8 * k < 32 := by omega
  have hshiftmod : 8 * k % 2 ^ 32 % 32 = 8 * k := by
    calc
      8 * k % 2 ^ 32 % 32 = (8 * k) % 32 := by
        have h : 8 * k % 2 ^ 32 = 8 * k :=
          Nat.mod_eq_of_lt (show 8 * k < 2 ^ 32 by omega)
        rw [h]
      _ = 8 * k := Nat.mod_eq_of_lt hshift
  rw [hshiftmod]
  norm_num only [show UInt32.toNat 255 = 255 by decide,
    show 2 ^ 8 = 256 by norm_num]
  rw [show 255 = 2 ^ 8 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  change (w.toNat / 2 ^ (8 * k) % 256) =
    (w.toNat / (2 ^ 8) ^ k % 2 ^ 8) % 2 ^ 8
  rw [show (2 ^ 8) ^ k = 2 ^ (8 * k) by rw [← Nat.pow_mul]]
  norm_num

private theorem littleBytes_byte (w : UInt32) (k : Nat) (hk : k < 4) :
    (littleBytes w)[k]?.getD 0 = UInt8.ofNat (w.toNat / 256 ^ k % 256) := by
  rw [Challenge.EvmProof.Memory.getD0_eq_getElem _ _ (by
    simp [littleBytes]
    exact hk)]
  interval_cases k
  · change ((w >>> UInt32.ofNat 0) &&& 0xff).toUInt8 =
      UInt8.ofNat (w.toNat / 256 ^ 0 % 256)
    exact uint32_byte w 0 (by norm_num)
  · change ((w >>> UInt32.ofNat 8) &&& 0xff).toUInt8 =
      UInt8.ofNat (w.toNat / 256 ^ 1 % 256)
    exact uint32_byte w 1 (by norm_num)
  · change ((w >>> UInt32.ofNat 16) &&& 0xff).toUInt8 =
      UInt8.ofNat (w.toNat / 256 ^ 2 % 256)
    exact uint32_byte w 2 (by norm_num)
  · change ((w >>> UInt32.ofNat 24) &&& 0xff).toUInt8 =
      UInt8.ofNat (w.toNat / 256 ^ 3 % 256)
    exact uint32_byte w 3 (by norm_num)

private theorem writeLE32_empty_eq (w : UInt32) :
    Ripemd160.writeLE32 ByteArray.empty w = littleBytes w := by
  unfold Ripemd160.writeLE32 littleBytes
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  congr 1

private theorem writeLE32_append (acc : ByteArray) (w : UInt32) :
    Ripemd160.writeLE32 acc w =
      acc ++ Ripemd160.writeLE32 ByteArray.empty w := by
  unfold Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  cases acc with
  | mk data =>
      congr 1
      apply Array.ext'
      simp [Array.toList_push, List.append_assoc]
      rfl

private theorem emitDigest_eq_littleBytes
    (h0 h1 h2 h3 h4 : UInt32) :
    SpecBridge.emitDigest #[h0, h1, h2, h3, h4] =
      littleBytes h0 ++ littleBytes h1 ++ littleBytes h2 ++
        littleBytes h3 ++ littleBytes h4 := by
  unfold SpecBridge.emitDigest
  norm_num [List.range, List.range.loop]
  conv_lhs =>
    rw [writeLE32_append]
    rw [writeLE32_append]
    rw [writeLE32_append]
    rw [writeLE32_append]
  rw [writeLE32_empty_eq, writeLE32_empty_eq, writeLE32_empty_eq,
    writeLE32_empty_eq, writeLE32_empty_eq]

private theorem group_byte (n m k : Nat) (hk : k < 4) :
    (n / 2 ^ (32 * m + 8 * k)) % 256 =
      ((n / 2 ^ (32 * m)) % 2 ^ 32 / 2 ^ (8 * k)) % 256 := by
  have hdiv : 2 ^ (8 * k) * 256 ∣ 2 ^ 32 := by
    refine ⟨2 ^ (24 - 8 * k), ?_⟩
    calc
      2 ^ 32 =
          2 ^ (8 * k) * 2 ^ 8 * 2 ^ (24 - 8 * k) := by
        rw [← Nat.pow_add, ← Nat.pow_add]
        congr 1
        omega
      _ = 2 ^ (8 * k) * 256 * 2 ^ (24 - 8 * k) := by norm_num
  have hmod :
      ((n / 2 ^ (32 * m)) % 2 ^ 32 / 2 ^ (8 * k)) % 256 =
        (n / 2 ^ (32 * m) / 2 ^ (8 * k)) % 256 := by
    calc
        ((n / 2 ^ (32 * m)) % 2 ^ 32 / 2 ^ (8 * k)) % 256 =
          ((n / 2 ^ (32 * m)) % 2 ^ 32 %
            (2 ^ (8 * k) * 256)) / 2 ^ (8 * k) :=
        (Nat.mod_mul_right_div_self
          ((n / 2 ^ (32 * m)) % 2 ^ 32) (2 ^ (8 * k)) 256).symm
      _ = (n / 2 ^ (32 * m) %
            (2 ^ (8 * k) * 256)) / 2 ^ (8 * k) := by
        rw [Nat.mod_mod_of_dvd]
        exact hdiv
      _ = (n / 2 ^ (32 * m) / 2 ^ (8 * k)) % 256 :=
        Nat.mod_mul_right_div_self (n / 2 ^ (32 * m)) (2 ^ (8 * k)) 256
  calc
    (n / 2 ^ (32 * m + 8 * k)) % 256 =
        (n / 2 ^ (32 * m) / 2 ^ (8 * k)) % 256 := by
      rw [pow_add, Nat.div_div_eq_div_mul]
    _ = ((n / 2 ^ (32 * m)) % 2 ^ 32 / 2 ^ (8 * k)) % 256 := hmod.symm

private theorem nat_append32 (n w : Nat) (hw : w < 2 ^ 32) :
    (n <<< 32) ||| w = n * 2 ^ 32 + w := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 32
  · have hpow : 2 ^ (32 - k) = 2 * 2 ^ (31 - k) := by
      rw [show 32 - k = (31 - k) + 1 by omega, pow_succ]
      ring
    have hfactor : n * 2 ^ 32 =
        2 ^ k * (2 * (n * 2 ^ (31 - k))) := by
      calc
        n * 2 ^ 32 = n * (2 ^ k * 2 ^ (32 - k)) := by
          rw [← Nat.pow_add]
          congr 2
          omega
        _ = 2 ^ k * (2 * (n * 2 ^ (31 - k))) := by
          rw [hpow]
          ring
    have hquot : (n * 2 ^ 32 + w) / 2 ^ k =
        2 * (n * 2 ^ (31 - k)) + w / 2 ^ k := by
      rw [hfactor, Nat.mul_add_div (by positivity)]
    have hleft : ((n <<< 32) ||| w).testBit k = w.testBit k := by
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      simp [hk]
    have hright : (n * 2 ^ 32 + w).testBit k = w.testBit k := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rw [hquot]
      have hmod :
          (2 * (n * 2 ^ (31 - k)) + w / 2 ^ k) % 2 =
            (w / 2 ^ k) % 2 := by
        simp [Nat.add_mod]
      rw [hmod]
      exact Nat.testBit_eq_decide_div_mod_eq.symm
    exact hleft.trans hright.symm
  · have hwk : w.testBit k = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le hw
        (Nat.pow_le_pow_right (by omega) (by omega)))]
      decide
    have hleft : ((n <<< 32) ||| w).testBit k = (n <<< 32).testBit k := by
      rw [Nat.testBit_or, hwk, Bool.or_false]
    have hright : (n * 2 ^ 32 + w).testBit k = (n <<< 32).testBit k := by
      let l := k - 32
      have hkl : k = l + 32 := by
        dsimp [l]
        omega
      rw [hkl, Nat.testBit_add]
      have hquot32 : (n * 2 ^ 32 + w) / 2 ^ 32 = n := by
        rw [show n * 2 ^ 32 = 2 ^ 32 * n by ring,
          Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hw, Nat.add_zero]
      rw [hquot32]
      rw [Nat.testBit_shiftLeft]
      simp [l]
    exact hleft.trans hright.symm

private theorem append32_ofNat (n : Nat) (w : UInt32)
    (hn : n < 2 ^ 256)
    (hresult : n * 2 ^ 32 + w.toNat < 2 ^ 256) :
    append32 (UInt256.ofNat n) w =
      UInt256.ofNat (n * 2 ^ 32 + w.toNat) := by
  have hle : n * 2 ^ 32 ≤ n * 2 ^ 32 + w.toNat := Nat.le_add_right _ _
  have hshift : n * 2 ^ 32 < 2 ^ 256 := lt_of_le_of_lt hle hresult
  apply Word.word_ext
  unfold append32
  rw [Word.shiftLeft_ofNat hn (by norm_num) hshift]
  rw [Word.word_toNat_lor, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hshift, Word.ofUInt32_toNat]
  have happ := nat_append32 n w.toNat w.toNat_lt
  rw [Nat.shiftLeft_eq] at happ
  rw [happ]
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hresult]

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

private theorem packedOutput_extract (value : UInt256) (j : Nat) (hj : j < 8) :
    EVM.Precompile.bytesToNatPadded
        (Data.Bytes.natToBytesPadded value.toNat 32) (4 * j) 4 =
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
  rw [Word.shiftRight_toNat value (by omega), Nat.shiftRight_eq_div_pow]
  have hpow : 2 ^ (32 * (7 - j)) = 256 ^ (28 - 4 * j) := by
    calc
      2 ^ (32 * (7 - j)) = 2 ^ (8 * (28 - 4 * j)) := by
        congr 1
        omega
      _ = (2 ^ 8) ^ (28 - 4 * j) :=
        Nat.pow_mul 2 8 (28 - 4 * j)
      _ = 256 ^ (28 - 4 * j) := by norm_num
  rw [hpow, show 2 ^ 32 = 256 ^ 4 by norm_num]

private theorem packedOutput_packed_extract
    (value : UInt256) (j : Nat) (hj : j < 8) :
    EVM.Precompile.bytesToNatPadded
        (Data.Bytes.natToBytesPadded (DensePacked.packed value).toNat 32)
        (4 * j) 4 =
      (Word.mask32 (DensePacked.le4 value j)).toNat := by
  rw [packedOutput_extract (DensePacked.packed value) j hj]
  exact congrArg UInt256.toNat (DensePacked.packed_extract value j hj)

private theorem natToBytesPadded_byte_of_segment
    (n j k : Nat) (hj : j < 8) (hk : k < 4) :
    n / 256 ^ (31 - (4 * j + k)) % 256 =
      ((n / 256 ^ (28 - 4 * j)) % 256 ^ 4 /
        256 ^ (3 - k)) % 256 := by
  let q := n / 256 ^ (28 - 4 * j)
  let b := 256 ^ (3 - k)
  have hindex : 31 - (4 * j + k) = (28 - 4 * j) + (3 - k) := by omega
  have hdiv : n / 256 ^ (31 - (4 * j + k)) = q / b := by
    dsimp [q, b]
    rw [hindex, pow_add, Nat.div_div_eq_div_mul]
  have hdivmod :
      (q % 256 ^ 4) / b % 256 = q / b % 256 := by
    calc
      (q % 256 ^ 4) / b % 256 =
          (q % 256 ^ 4 % (b * 256)) / b :=
        (Nat.mod_mul_right_div_self (q % 256 ^ 4) b 256).symm
      _ = (q % (b * 256)) / b := by
        rw [Nat.mod_mod_of_dvd]
        refine ⟨256 ^ k, ?_⟩
        dsimp [b]
        have hpow : 256 ^ (3 - k) * 256 * 256 ^ k = 256 ^ 4 := by
          calc
            256 ^ (3 - k) * 256 * 256 ^ k =
                (256 ^ (3 - k) * 256 ^ 1) * 256 ^ k := by norm_num
            _ = 256 ^ ((3 - k) + 1) * 256 ^ k := by rw [← pow_add]
            _ = 256 ^ (((3 - k) + 1) + k) := by rw [← pow_add]
            _ = 256 ^ 4 := by congr 1; omega
        rw [hpow]
        norm_num
      _ = q / b % 256 := Nat.mod_mul_right_div_self q b 256
  rw [hdiv]
  exact hdivmod.symm

private theorem nat_append_bits (n w width : Nat) (hw : w < 2 ^ width) :
    (n <<< width) ||| w = n * 2 ^ width + w := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < width
  · have hpow : 2 ^ (width - k) = 2 * 2 ^ (width - 1 - k) := by
      rw [show width - k = (width - 1 - k) + 1 by omega, pow_succ]
      ring
    have hfactor : n * 2 ^ width =
        2 ^ k * (2 * (n * 2 ^ (width - 1 - k))) := by
      calc
        n * 2 ^ width = n * (2 ^ k * 2 ^ (width - k)) := by
          rw [← Nat.pow_add]
          congr 2
          omega
        _ = 2 ^ k * (2 * (n * 2 ^ (width - 1 - k))) := by
          rw [hpow]
          ring
    have hquot : (n * 2 ^ width + w) / 2 ^ k =
        2 * (n * 2 ^ (width - 1 - k)) + w / 2 ^ k := by
      rw [hfactor, Nat.mul_add_div (by positivity)]
    have hleft : ((n <<< width) ||| w).testBit k = w.testBit k := by
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      simp [hk]
    have hright : (n * 2 ^ width + w).testBit k = w.testBit k := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rw [hquot]
      have hmod :
          (2 * (n * 2 ^ (width - 1 - k)) + w / 2 ^ k) % 2 =
            (w / 2 ^ k) % 2 := by
        simp [Nat.add_mod]
      rw [hmod]
      exact Nat.testBit_eq_decide_div_mod_eq.symm
    exact hleft.trans hright.symm
  · have hwk : w.testBit k = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le hw
        (Nat.pow_le_pow_right (by omega) (by omega)))]
      decide
    have hleft : ((n <<< width) ||| w).testBit k = (n <<< width).testBit k := by
      rw [Nat.testBit_or, hwk, Bool.or_false]
    have hright : (n * 2 ^ width + w).testBit k = (n <<< width).testBit k := by
      let l := k - width
      have hkl : k = l + width := by
        dsimp [l]
        omega
      rw [hkl, Nat.testBit_add]
      have hquot : (n * 2 ^ width + w) / 2 ^ width = n := by
        rw [show n * 2 ^ width = 2 ^ width * n by ring,
          Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hw, Nat.add_zero]
      rw [hquot]
      rw [Nat.testBit_shiftLeft]
      simp [l]
    exact hleft.trans hright.symm

private theorem byteAt_toNat (v : EWord) (i : Nat) (hi : i < 32) :
    (UInt256.byteAt (UInt256.ofNat i) v).toNat =
      (v.toNat >>> (8 * (31 - i))) &&& 0xff := by
  unfold UInt256.byteAt
  have hi256 : (UInt256.ofNat i).toNat = i := by
    rw [Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans hi (by norm_num))
  rw [hi256, if_neg (by omega), Word.word_toNat_ofNat]
  have hlow :
      (v.toNat >>> (8 * (31 - i))) &&& 0xff ≤ 0xff := Nat.and_le_right
  exact Nat.mod_eq_of_lt (by omega)

private theorem byteAt_lt256 (v : EWord) (i : Nat) (hi : i < 32) :
    (UInt256.byteAt (UInt256.ofNat i) v).toNat < 256 := by
  rw [byteAt_toNat v i hi]
  have hle :
      (v.toNat >>> (8 * (31 - i))) &&& 0xff ≤ 0xff := Nat.and_le_right
  omega

private theorem shl_toNat (v : EWord) (n : Nat) (hn : n < 256) :
    (DensePacked.shl v n).toNat = (v.toNat <<< n) % 2 ^ 256 := by
  unfold DensePacked.shl UInt256.shiftLeft
  have hshift : (UInt256.ofNat n).toNat = n := by
    rw [Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [if_neg (by omega), hshift, Word.word_toNat_ofNat]
  rw [show UInt256.size = 2 ^ 256 by rfl, Nat.mod_mod]

private def le4Nat (b0 b1 b2 b3 : Nat) : Nat :=
  (((b3 * 2 ^ 8 + b2) * 2 ^ 8 + b1) * 2 ^ 8 + b0)

private theorem shift8_lt_pow256 {b : Nat} (hb : b < 2 ^ 8) :
    b <<< 8 < 2 ^ 256 := by
  have h := Nat.shiftLeft_lt hb (m := 8)
  exact lt_of_lt_of_le h
    (Nat.pow_le_pow_right (n := 2) (by decide) (by norm_num))

private theorem shift16_lt_pow256 {b : Nat} (hb : b < 2 ^ 8) :
    b <<< 16 < 2 ^ 256 := by
  have h := Nat.shiftLeft_lt hb (m := 16)
  exact lt_of_lt_of_le h
    (Nat.pow_le_pow_right (n := 2) (by decide) (by norm_num))

private theorem shift24_lt_pow256 {b : Nat} (hb : b < 2 ^ 8) :
    b <<< 24 < 2 ^ 256 := by
  have h := Nat.shiftLeft_lt hb (m := 24)
  exact lt_of_lt_of_le h
    (Nat.pow_le_pow_right (n := 2) (by decide) (by norm_num))

private theorem lor_four_reorder (a b c d : Nat) :
    (a ||| b) ||| (c ||| d) = ((d ||| c) ||| b) ||| a := by
  ac_rfl

private theorem shiftLeft_shiftLeft (n a b : Nat) :
    (n <<< a) <<< b = n <<< (a + b) := by
  simp only [Nat.shiftLeft_eq]
  calc
    n * 2 ^ a * 2 ^ b = n * (2 ^ a * 2 ^ b) := by ring
    _ = n * 2 ^ (a + b) := by rw [← Nat.pow_add]

private theorem le4_toNat (v : EWord) (j : Nat) (hj : j < 8) :
    (DensePacked.le4 v j).toNat =
      le4Nat
        (UInt256.byteAt (UInt256.ofNat (4 * j + 0)) v).toNat
        (UInt256.byteAt (UInt256.ofNat (4 * j + 1)) v).toNat
        (UInt256.byteAt (UInt256.ofNat (4 * j + 2)) v).toNat
        (UInt256.byteAt (UInt256.ofNat (4 * j + 3)) v).toNat := by
  let b0 := (UInt256.byteAt (UInt256.ofNat (4 * j + 0)) v).toNat
  let b1 := (UInt256.byteAt (UInt256.ofNat (4 * j + 1)) v).toNat
  let b2 := (UInt256.byteAt (UInt256.ofNat (4 * j + 2)) v).toNat
  let b3 := (UInt256.byteAt (UInt256.ofNat (4 * j + 3)) v).toNat
  have hb0 : b0 < 2 ^ 8 := by
    dsimp [b0]
    exact byteAt_lt256 v (4 * j + 0) (by omega)
  have hb1 : b1 < 2 ^ 8 := by
    dsimp [b1]
    exact byteAt_lt256 v (4 * j + 1) (by omega)
  have hb2 : b2 < 2 ^ 8 := by
    dsimp [b2]
    exact byteAt_lt256 v (4 * j + 2) (by omega)
  have hb3 : b3 < 2 ^ 8 := by
    dsimp [b3]
    exact byteAt_lt256 v (4 * j + 3) (by omega)
  have hs1 :
      (DensePacked.shl (UInt256.byteAt (UInt256.ofNat (4 * j + 1)) v) 8).toNat =
        b1 * 2 ^ 8 := by
    rw [shl_toNat _ 8 (by norm_num), Nat.mod_eq_of_lt]
    · rw [Nat.shiftLeft_eq]
    · exact shift8_lt_pow256 hb1
  have hs2 :
      (DensePacked.shl (UInt256.byteAt (UInt256.ofNat (4 * j + 2)) v) 16).toNat =
        b2 * 2 ^ 16 := by
    rw [shl_toNat _ 16 (by norm_num), Nat.mod_eq_of_lt]
    · rw [Nat.shiftLeft_eq]
    · exact shift16_lt_pow256 hb2
  have hs3 :
      (DensePacked.shl (UInt256.byteAt (UInt256.ofNat (4 * j + 3)) v) 24).toNat =
        b3 * 2 ^ 24 := by
    rw [shl_toNat _ 24 (by norm_num), Nat.mod_eq_of_lt]
    · rw [Nat.shiftLeft_eq]
    · exact shift24_lt_pow256 hb3
  unfold DensePacked.le4
  rw [Word.word_toNat_lor, Word.word_toNat_lor, Word.word_toNat_lor,
    hs1, hs2, hs3]
  simp only [b1, b2, b3, le4Nat]
  rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq]
  have hlor := lor_four_reorder
    (UInt256.byteAt (UInt256.ofNat (4 * j + 0)) v).toNat
    ((UInt256.byteAt (UInt256.ofNat (4 * j + 1)) v).toNat <<< 8)
    ((UInt256.byteAt (UInt256.ofNat (4 * j + 2)) v).toNat <<< 16)
    ((UInt256.byteAt (UInt256.ofNat (4 * j + 3)) v).toNat <<< 24)
  rw [hlor]
  have h3shift :
      (UInt256.byteAt (UInt256.ofNat (4 * j + 3)) v).toNat <<< 24 =
        ((UInt256.byteAt (UInt256.ofNat (4 * j + 3)) v).toNat <<< 16) <<< 8 := by
    rw [shiftLeft_shiftLeft, show 16 + 8 = 24 by norm_num]
  have h2shift :
      (UInt256.byteAt (UInt256.ofNat (4 * j + 2)) v).toNat <<< 16 =
        ((UInt256.byteAt (UInt256.ofNat (4 * j + 2)) v).toNat <<< 8) <<< 8 := by
    rw [shiftLeft_shiftLeft, show 8 + 8 = 16 by norm_num]
  rw [h3shift, h2shift]
  rw [← Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_or_distrib]
  have h3shift' :
      (UInt256.byteAt (UInt256.ofNat (4 * j + 3)) v).toNat <<< 16 =
        ((UInt256.byteAt (UInt256.ofNat (4 * j + 3)) v).toNat <<< 8) <<< 8 := by
    rw [shiftLeft_shiftLeft, show 8 + 8 = 16 by norm_num]
  rw [h3shift']
  rw [← Nat.shiftLeft_or_distrib]
  have ha := nat_append_bits b3 b2 8 hb2
  have hb := nat_append_bits (b3 * 2 ^ 8 + b2) b1 8 hb1
  rw [ha, hb]
  rw [nat_append_bits _ b0 8 hb0]

private theorem le4_toNat_lt_pow32 (v : EWord) (j : Nat) (hj : j < 8) :
    (DensePacked.le4 v j).toNat < 2 ^ 32 := by
  let b0 := (UInt256.byteAt (UInt256.ofNat (4 * j + 0)) v).toNat
  let b1 := (UInt256.byteAt (UInt256.ofNat (4 * j + 1)) v).toNat
  let b2 := (UInt256.byteAt (UInt256.ofNat (4 * j + 2)) v).toNat
  let b3 := (UInt256.byteAt (UInt256.ofNat (4 * j + 3)) v).toNat
  have hb0 : b0 < 2 ^ 8 := by
    dsimp [b0]
    exact byteAt_lt256 v (4 * j + 0) (by omega)
  have hb1 : b1 < 2 ^ 8 := by
    dsimp [b1]
    exact byteAt_lt256 v (4 * j + 1) (by omega)
  have hb2 : b2 < 2 ^ 8 := by
    dsimp [b2]
    exact byteAt_lt256 v (4 * j + 2) (by omega)
  have hb3 : b3 < 2 ^ 8 := by
    dsimp [b3]
    exact byteAt_lt256 v (4 * j + 3) (by omega)
  rw [le4_toNat v j hj]
  change le4Nat b0 b1 b2 b3 < 2 ^ 32
  dsimp [le4Nat]
  norm_num at *
  omega

private theorem le4Nat_byte3 (b0 b1 b2 b3 : Nat) (hb0 : b0 < 256) :
    (le4Nat b0 b1 b2 b3 / 256 ^ (3 - 3)) % 256 = b0 := by
  simp only [Nat.sub_self, pow_zero, Nat.div_one]
  unfold le4Nat
  norm_num only [show 2 ^ 8 = 256 by norm_num]
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod,
    Nat.zero_add,
    Nat.mod_eq_of_lt hb0]
  exact Nat.mod_eq_of_lt hb0

private theorem mul256_add_div (n b : Nat) (hb : b < 256) :
    (n * 256 + b) / 256 = n := by
  rw [show n * 256 = 256 * n by ring,
    Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hb, Nat.add_zero]

private theorem mul256_add_mod (n b : Nat) (hb : b < 256) :
    (n * 256 + b) % 256 = b := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod,
    Nat.zero_add]
  rw [Nat.mod_eq_of_lt hb]
  exact Nat.mod_eq_of_lt hb

private theorem div256_sq (n : Nat) :
    n / 256 ^ 2 = n / 256 / 256 := by
  rw [show 256 ^ 2 = 256 * 256 by norm_num]
  exact (Nat.div_div_eq_div_mul n 256 256).symm

private theorem div256_cube (n : Nat) :
    n / 256 ^ 3 = n / 256 / 256 / 256 := by
  rw [show 256 ^ 3 = 256 * (256 * 256) by norm_num]
  rw [← Nat.div_div_eq_div_mul]
  rw [show 256 * 256 = 256 ^ 2 by norm_num, div256_sq]

private theorem le4Nat_byte2 (b0 b1 b2 b3 : Nat)
    (hb0 : b0 < 256) (hb1 : b1 < 256) :
    (le4Nat b0 b1 b2 b3 / 256 ^ (3 - 2)) % 256 = b1 := by
  unfold le4Nat
  norm_num only [show 2 ^ 8 = 256 by norm_num]
  rw [show ((b3 * 256 + b2) * 256 + b1) * 256 + b0 =
      256 * ((b3 * 256 + b2) * 256 + b1) + b0 by ring]
  rw [Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hb0, Nat.add_zero]
  exact mul256_add_mod _ _ hb1

private theorem le4Nat_byte1 (b0 b1 b2 b3 : Nat)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) :
    (le4Nat b0 b1 b2 b3 / 256 ^ (3 - 1)) % 256 = b2 := by
  change (le4Nat b0 b1 b2 b3 / 256 ^ 2) % 256 = b2
  rw [div256_sq]
  unfold le4Nat
  norm_num only [show 2 ^ 8 = 256 by norm_num]
  rw [show ((b3 * 256 + b2) * 256 + b1) * 256 + b0 =
      256 * (((b3 * 256 + b2) * 256 + b1)) + b0 by ring]
  rw [Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hb0, Nat.add_zero]
  rw [show (b3 * 256 + b2) * 256 + b1 =
      256 * (b3 * 256 + b2) + b1 by ring]
  rw [Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hb1, Nat.add_zero]
  exact mul256_add_mod _ _ hb2

private theorem le4Nat_byte0 (b0 b1 b2 b3 : Nat)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256) :
    (le4Nat b0 b1 b2 b3 / 256 ^ (3 - 0)) % 256 = b3 := by
  change (le4Nat b0 b1 b2 b3 / 256 ^ 3) % 256 = b3
  rw [div256_cube]
  unfold le4Nat
  norm_num only [show 2 ^ 8 = 256 by norm_num]
  rw [show ((b3 * 256 + b2) * 256 + b1) * 256 + b0 =
      256 * (((b3 * 256 + b2) * 256 + b1)) + b0 by ring]
  rw [Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hb0, Nat.add_zero]
  rw [show (b3 * 256 + b2) * 256 + b1 =
      256 * (b3 * 256 + b2) + b1 by ring]
  rw [Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hb1, Nat.add_zero]
  rw [show b3 * 256 + b2 = 256 * b3 + b2 by ring]
  rw [Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hb2, Nat.add_zero]
  exact Nat.mod_eq_of_lt hb3

private theorem le4_mask_byte (v : EWord) (j k : Nat)
    (hj : j < 8) (hk : k < 4) :
    ((Word.mask32 (DensePacked.le4 v j)).toNat / 256 ^ (3 - k)) % 256 =
      (UInt256.byteAt (UInt256.ofNat (4 * j + (3 - k))) v).toNat := by
  have hmask : (Word.mask32 (DensePacked.le4 v j)).toNat =
      (DensePacked.le4 v j).toNat := by
    rw [Word.mask32_toNat]
    rw [show 0xffffffff = 2 ^ 32 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (le4_toNat_lt_pow32 v j hj)
  rw [hmask, le4_toNat v j hj]
  interval_cases k
  · simpa using le4Nat_byte0
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 0)) v).toNat)
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 1)) v).toNat)
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 2)) v).toNat)
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 3)) v).toNat)
      (byteAt_lt256 v (4 * j + 0) (by omega))
      (byteAt_lt256 v (4 * j + 1) (by omega))
      (byteAt_lt256 v (4 * j + 2) (by omega))
      (byteAt_lt256 v (4 * j + 3) (by omega))
  · simpa using le4Nat_byte1
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 0)) v).toNat)
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 1)) v).toNat)
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 2)) v).toNat)
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 3)) v).toNat)
      (byteAt_lt256 v (4 * j + 0) (by omega))
      (byteAt_lt256 v (4 * j + 1) (by omega))
      (byteAt_lt256 v (4 * j + 2) (by omega))
  · simpa using le4Nat_byte2
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 0)) v).toNat)
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 1)) v).toNat)
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 2)) v).toNat)
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 3)) v).toNat)
      (byteAt_lt256 v (4 * j + 0) (by omega))
      (byteAt_lt256 v (4 * j + 1) (by omega))
  · simpa using le4Nat_byte3
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 0)) v).toNat)
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 1)) v).toNat)
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 2)) v).toNat)
      ((UInt256.byteAt (UInt256.ofNat (4 * j + 3)) v).toNat)
      (byteAt_lt256 v (4 * j + 0) (by omega))

private theorem packedOutput_byte (value : EWord) (j k : Nat)
    (hj : j < 8) (hk : k < 4) :
    (Data.Bytes.natToBytesPadded (DensePacked.packed value).toNat 32)[4 * j + k]?.getD 0 =
      UInt8.ofNat
        (UInt256.byteAt (UInt256.ofNat (4 * j + (3 - k))) value).toNat := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD
    (DensePacked.packed value).toNat 32 (4 * j + k) (by omega)]
  rw [natToBytesPadded_byte_of_segment
    (DensePacked.packed value).toNat j k hj hk]
  have hsegment := bytesToNatPadded_natToBytes_segment
    (DensePacked.packed value).toNat (4 * j)
    (by omega) (DensePacked.packed value).val.isLt
  have hq :
      ((DensePacked.packed value).toNat / 256 ^ (28 - 4 * j)) % 256 ^ 4 =
        (Word.mask32 (DensePacked.le4 value j)).toNat := by
    calc
      ((DensePacked.packed value).toNat / 256 ^ (28 - 4 * j)) % 256 ^ 4 =
          EVM.Precompile.bytesToNatPadded
            (Data.Bytes.natToBytesPadded (DensePacked.packed value).toNat 32)
            (4 * j) 4 := hsegment.symm
      _ = (Word.mask32 (DensePacked.le4 value j)).toNat :=
        packedOutput_packed_extract value j hj
  rw [hq]
  exact congrArg UInt8.ofNat (le4_mask_byte value j k hj hk)

private theorem nat_append32_lt {bits n : Nat} (w : Nat)
    (hn : n < 2 ^ bits) (hw : w < 2 ^ 32) :
    n * 2 ^ 32 + w < 2 ^ (bits + 32) := by
  have h := Nat.append_lt (x := w) (y := n) (n := 32) (m := bits) hw hn
  have happ := nat_append32 n w hw
  rw [happ] at h
  simpa only [show 32 + bits = bits + 32 by omega] using h

private theorem word_lt_pow256_of_lt_pow32 {w : UInt32} :
    w.toNat < 2 ^ 256 := by
  exact lt_trans w.toNat_lt (by norm_num)

private theorem pack5Nat_lt_pow160 (h0 h1 h2 h3 h4 : UInt32) :
    pack5Nat h0 h1 h2 h3 h4 < 2 ^ 160 := by
  have h0lt : h0.toNat < 2 ^ 32 := h0.toNat_lt
  have h1lt : h1.toNat < 2 ^ 32 := h1.toNat_lt
  have h2lt : h2.toNat < 2 ^ 32 := h2.toNat_lt
  have h3lt : h3.toNat < 2 ^ 32 := h3.toNat_lt
  have h4lt : h4.toNat < 2 ^ 32 := h4.toNat_lt
  have h01 : h0.toNat * 2 ^ 32 + h1.toNat < 2 ^ 64 := by
    simpa using nat_append32_lt h1.toNat h0lt h1lt
  have h012 : (h0.toNat * 2 ^ 32 + h1.toNat) * 2 ^ 32 + h2.toNat <
      2 ^ 96 := by
    simpa [show 64 + 32 = 96 by norm_num] using
      nat_append32_lt h2.toNat h01 h2lt
  have h0123 : ((h0.toNat * 2 ^ 32 + h1.toNat) * 2 ^ 32 + h2.toNat) *
      2 ^ 32 + h3.toNat < 2 ^ 128 := by
    simpa [show 96 + 32 = 128 by norm_num] using
      nat_append32_lt h3.toNat h012 h3lt
  simpa [pack5Nat, show 128 + 32 = 160 by norm_num] using
    nat_append32_lt h4.toNat h0123 h4lt

private theorem pack5_eq_ofNat (h0 h1 h2 h3 h4 : UInt32) :
    pack5 h0 h1 h2 h3 h4 = UInt256.ofNat (pack5Nat h0 h1 h2 h3 h4) := by
  have h0lt : h0.toNat < 2 ^ 256 := word_lt_pow256_of_lt_pow32
  have h1lt : h1.toNat < 2 ^ 32 := h1.toNat_lt
  have h2lt : h2.toNat < 2 ^ 32 := h2.toNat_lt
  have h3lt : h3.toNat < 2 ^ 32 := h3.toNat_lt
  have h4lt : h4.toNat < 2 ^ 32 := h4.toNat_lt
  have h01 : h0.toNat * 2 ^ 32 + h1.toNat < 2 ^ 64 := by
    simpa using nat_append32_lt h1.toNat h0.toNat_lt h1lt
  have h012 : (h0.toNat * 2 ^ 32 + h1.toNat) * 2 ^ 32 + h2.toNat <
      2 ^ 96 := by
    simpa [show 64 + 32 = 96 by norm_num] using
      nat_append32_lt h2.toNat h01 h2lt
  have h0123 : ((h0.toNat * 2 ^ 32 + h1.toNat) * 2 ^ 32 + h2.toNat) *
      2 ^ 32 + h3.toNat < 2 ^ 128 := by
    simpa [show 96 + 32 = 128 by norm_num] using
      nat_append32_lt h3.toNat h012 h3lt
  have h01234 := pack5Nat_lt_pow160 h0 h1 h2 h3 h4
  have h01_256 : h0.toNat * 2 ^ 32 + h1.toNat < 2 ^ 256 :=
    lt_trans h01 (by norm_num)
  have h012_256 : (h0.toNat * 2 ^ 32 + h1.toNat) * 2 ^ 32 + h2.toNat <
      2 ^ 256 := lt_trans h012 (by norm_num)
  have h0123_256 : ((h0.toNat * 2 ^ 32 + h1.toNat) * 2 ^ 32 + h2.toNat) *
      2 ^ 32 + h3.toNat < 2 ^ 256 := lt_trans h0123 (by norm_num)
  have h01234_256 : pack5Nat h0 h1 h2 h3 h4 < 2 ^ 256 :=
    lt_trans h01234 (by norm_num)
  change append32 (append32 (append32 (append32 (UInt256.ofNat h0.toNat) h1) h2) h3) h4 = _
  rw [append32_ofNat h0.toNat h1 h0lt h01_256]
  rw [append32_ofNat _ h2 (by exact lt_trans h01 (by norm_num)) h012_256]
  rw [append32_ofNat _ h3 (by exact lt_trans h012 (by norm_num)) h0123_256]
  rw [append32_ofNat _ h4 (by exact lt_trans h0123 (by norm_num)) h01234_256]
  rfl

theorem pack5_toNat (h0 h1 h2 h3 h4 : UInt32) :
    (pack5 h0 h1 h2 h3 h4).toNat = pack5Nat h0 h1 h2 h3 h4 := by
  rw [pack5_eq_ofNat, Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_trans (pack5Nat_lt_pow160 h0 h1 h2 h3 h4) (by norm_num))

private theorem pack5_group (h0 h1 h2 h3 h4 : UInt32) (j : Nat) (hj : j < 8) :
    (pack5Nat h0 h1 h2 h3 h4 / 2 ^ (32 * (7 - j))) % 2 ^ 32 =
      PackedOutputDigits.expected h0.toNat h1.toNat h2.toNat h3.toNat h4.toNat j := by
  have h := PackedOutputDigits.extract h0.toNat h1.toNat h2.toNat h3.toNat h4.toNat j
    h0.toNat_lt h1.toNat_lt h2.toNat_lt h3.toNat_lt h4.toNat_lt hj
  simpa [pack5Nat, PackedOutputDigits.pack] using h

private theorem pack5_group_byte (h0 h1 h2 h3 h4 : UInt32) (j k : Nat)
    (hj : j < 8) (hk : k < 4) :
    (UInt256.byteAt (UInt256.ofNat (4 * j + (3 - k)))
      (pack5 h0 h1 h2 h3 h4)).toNat =
      (PackedOutputDigits.expected h0.toNat h1.toNat h2.toNat h3.toNat h4.toNat j /
        2 ^ (8 * k)) % 256 := by
  have hi : 4 * j + (3 - k) < 32 := by omega
  rw [byteAt_toNat _ _ hi, pack5_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 0xff = 2 ^ 8 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  have hindex : 8 * (31 - (4 * j + (3 - k))) =
      32 * (7 - j) + 8 * k := by omega
  rw [hindex, group_byte (pack5Nat h0 h1 h2 h3 h4) (7 - j) k hk]
  rw [pack5_group h0 h1 h2 h3 h4 j hj]

private theorem zero12_size :
    (ByteArray.mk (Array.replicate 12 0)).size = 12 := by
  rfl

private theorem littleBytes_size (w : UInt32) : (littleBytes w).size = 4 := by
  rfl

private theorem expected_little_group_byte (h0 h1 h2 h3 h4 : UInt32)
    (j k : Nat) (hj : j < 8) (hk : k < 4) :
    (ByteArray.mk (Array.replicate 12 0) ++
        littleBytes h0 ++ littleBytes h1 ++ littleBytes h2 ++
          littleBytes h3 ++ littleBytes h4)[4 * j + k]?.getD 0 =
      UInt8.ofNat
        ((PackedOutputDigits.expected h0.toNat h1.toNat h2.toNat h3.toNat h4.toNat j /
          2 ^ (8 * k)) % 256) := by
  interval_cases j
  · simp only [Challenge.EvmProof.Memory.getElem?_getD_append,
      ByteArray.size_append, zero12_size, littleBytes_size]
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega)]
    rw [show 4 * 0 + k = k by omega]
    have hk12 : k < (Array.replicate 12 0).size := by
      simp
      omega
    rw [Challenge.EvmProof.Memory.getD0_eq_getElem _ _ (by
      rw [zero12_size]
      omega)]
    change (ByteArray.mk (Array.replicate 12 0))[k] = _
    rw [ByteArray.getElem_eq_data_getElem]
    change (Array.replicate 12 (0 : UInt8))[k]'hk12 = _
    rw [Array.getElem_replicate]
    simp [PackedOutputDigits.expected]
  · simp only [Challenge.EvmProof.Memory.getElem?_getD_append,
      ByteArray.size_append, zero12_size, littleBytes_size]
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega)]
    rw [show 4 * 1 + k = 4 + k by omega]
    have hk12 : 4 + k < (Array.replicate 12 0).size := by
      simp
      omega
    rw [Challenge.EvmProof.Memory.getD0_eq_getElem _ _ (by
      rw [zero12_size]
      omega)]
    change (ByteArray.mk (Array.replicate 12 0))[4 + k] = _
    rw [ByteArray.getElem_eq_data_getElem]
    change (Array.replicate 12 (0 : UInt8))[4 + k]'hk12 = _
    rw [Array.getElem_replicate]
    simp [PackedOutputDigits.expected]
  · simp only [Challenge.EvmProof.Memory.getElem?_getD_append,
      ByteArray.size_append, zero12_size, littleBytes_size]
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega)]
    rw [show 4 * 2 + k = 8 + k by omega]
    have hk12 : 8 + k < (Array.replicate 12 0).size := by
      simp
      omega
    rw [Challenge.EvmProof.Memory.getD0_eq_getElem _ _ (by
      rw [zero12_size]
      omega)]
    change (ByteArray.mk (Array.replicate 12 0))[8 + k] = _
    rw [ByteArray.getElem_eq_data_getElem]
    change (Array.replicate 12 (0 : UInt8))[8 + k]'hk12 = _
    rw [Array.getElem_replicate]
    simp [PackedOutputDigits.expected]
  · simp only [Challenge.EvmProof.Memory.getElem?_getD_append,
      ByteArray.size_append, zero12_size, littleBytes_size]
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_neg (by omega)]
    rw [show 4 * 3 + k - 12 = k by omega]
    rw [littleBytes_byte h0 k hk]
    simp only [PackedOutputDigits.expected]
    congr 1
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]
  · simp only [Challenge.EvmProof.Memory.getElem?_getD_append,
      ByteArray.size_append, zero12_size, littleBytes_size]
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_neg (by omega)]
    rw [show 4 * 4 + k - (12 + 4) = k by omega]
    rw [littleBytes_byte h1 k hk]
    simp only [PackedOutputDigits.expected]
    congr 1
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]
  · simp only [Challenge.EvmProof.Memory.getElem?_getD_append,
      ByteArray.size_append, zero12_size, littleBytes_size]
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)]
    rw [show 4 * 5 + k - (12 + 4 + 4) = k by omega]
    rw [littleBytes_byte h2 k hk]
    simp only [PackedOutputDigits.expected]
    congr 1
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]
  · simp only [Challenge.EvmProof.Memory.getElem?_getD_append,
      ByteArray.size_append, zero12_size, littleBytes_size]
    rw [if_pos (by omega), if_neg (by omega)]
    rw [show 4 * 6 + k - (12 + 4 + 4 + 4) = k by omega]
    rw [littleBytes_byte h3 k hk]
    simp only [PackedOutputDigits.expected]
    congr 1
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]
  · simp only [Challenge.EvmProof.Memory.getElem?_getD_append,
      ByteArray.size_append, zero12_size, littleBytes_size]
    rw [if_neg (by omega)]
    rw [show 4 * 7 + k - (12 + 4 + 4 + 4 + 4) = k by omega]
    rw [littleBytes_byte h4 k hk]
    simp only [PackedOutputDigits.expected]
    congr 1
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]

/-- The packed word serializes to the precompile's exact 32-byte result. -/
theorem packedOutput_eq_prefix_emitDigest (h0 h1 h2 h3 h4 : UInt32) :
    packedOutput h0 h1 h2 h3 h4 =
      ByteArray.mk (Array.replicate 12 0) ++
        SpecBridge.emitDigest #[h0, h1, h2, h3, h4] := by
  rw [emitDigest_eq_littleBytes]
  simp only [← ByteArray.append_assoc]
  apply ByteArray.ext_getElem
  · simp [packedOutput, YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
      zero12_size, littleBytes_size]
  · intro i hi hi'
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi']
    have hi32 : i < 32 := by
      simpa only [packedOutput, YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hi
    have hj : i / 4 < 8 := by omega
    have hk : i % 4 < 4 := Nat.mod_lt _ (by decide)
    have hindex : 4 * (i / 4) + i % 4 = i := by omega
    calc
      (packedOutput h0 h1 h2 h3 h4)[i]?.getD 0 =
          UInt8.ofNat
            ((PackedOutputDigits.expected h0.toNat h1.toNat h2.toNat
                h3.toNat h4.toNat (i / 4) / 2 ^ (8 * (i % 4))) % 256) := by
        conv_lhs => rw [← hindex]
        exact (packedOutput_byte (pack5 h0 h1 h2 h3 h4) (i / 4) (i % 4) hj hk).trans
          (congrArg UInt8.ofNat (pack5_group_byte h0 h1 h2 h3 h4
            (i / 4) (i % 4) hj hk))
      _ = (ByteArray.mk (Array.replicate 12 0) ++
          littleBytes h0 ++ littleBytes h1 ++ littleBytes h2 ++
          littleBytes h3 ++ littleBytes h4)[i]?.getD 0 := by
        simpa only [hindex] using
          (expected_little_group_byte h0 h1 h2 h3 h4 (i / 4) (i % 4) hj hk).symm

theorem pack5_lt_pow160 (h0 h1 h2 h3 h4 : UInt32) :
    (pack5 h0 h1 h2 h3 h4).toNat < 2 ^ 160 := by
  rw [pack5_toNat]
  exact pack5Nat_lt_pow160 h0 h1 h2 h3 h4

theorem pack5_shiftRight160_eq_zero (h0 h1 h2 h3 h4 : UInt32) :
    UInt256.shiftRight (pack5 h0 h1 h2 h3 h4) (UInt256.ofNat 160) = UInt256.ofNat 0 := by
  rw [pack5_eq_ofNat, Word.shiftRight_ofNat]
  · congr 1
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (pack5Nat_lt_pow160 h0 h1 h2 h3 h4)]
  · exact lt_trans (pack5Nat_lt_pow160 h0 h1 h2 h3 h4) (by norm_num)
  · norm_num

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputMath
