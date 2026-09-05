import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.InitializationCorrect
import YulEvmCompiler.BytesLemmas

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Padded-memory bridge for the RIPEMD-160 schedule

This file connects the bytecode's `MLOAD`/`BYTE` little-endian reader to the
pinned `Crypto.Ripemd160.readLE32` reader over every complete 64-byte block of
the one-pass padded image.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddedBlockBridge

open EvmSemantics
open EvmSemantics.Crypto
open EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding

private theorem readPadded_four_eq (bs : ByteArray) (off : Nat) :
    MachineState.readPadded bs off 4 = ByteArray.mk #[
      bs[off]?.getD 0, bs[off + 1]?.getD 0,
      bs[off + 2]?.getD 0, bs[off + 3]?.getD 0] := by
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    rfl
  · intro i hi₁ hi₂
    have hi : i < 4 := by simpa using hi₁
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi]
    interval_cases i <;> rfl

private theorem bytesToBigEndianNat_readPadded_four (bs : ByteArray)
    (off : Nat) :
    Data.Bytes.bytesToBigEndianNat (MachineState.readPadded bs off 4) =
      ((((bs[off]?.getD 0).toNat * 256 +
          (bs[off + 1]?.getD 0).toNat) * 256 +
          (bs[off + 2]?.getD 0).toNat) * 256) +
        (bs[off + 3]?.getD 0).toNat := by
  rw [readPadded_four_eq]
  simp [Data.Bytes.bytesToBigEndianNat,
    Challenge.EvmProof.Bytecode.toList_eq_data]

private theorem readPadded_thirtyTwo_split (bs : ByteArray) (off : Nat) :
    MachineState.readPadded bs off 32 =
      MachineState.readPadded bs off 4 ++
        MachineState.readPadded bs (off + 4) 28 := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hi₁ hi₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₂,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD]
    have hi : i < 32 := by simpa using hi₁
    rw [if_pos hi, Challenge.EvmProof.Memory.getElem?_getD_append]
    simp only [Challenge.EvmProof.Memory.readPadded_size]
    by_cases h4 : i < 4
    · rw [if_pos h4,
        Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos h4]
    · rw [if_neg h4,
        Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos (by omega)]
      congr 2
      omega

private theorem foldl_bytes (xs : List UInt8) (acc : Nat) :
    xs.foldl (fun n b => n * 256 + b.toNat) acc =
      acc * 256 ^ xs.length +
        xs.foldl (fun n b => n * 256 + b.toNat) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [ih (acc * 256 + x.toNat), ih x.toNat, Nat.pow_succ]
      ring

private theorem bytesToBigEndianNat_append (a b : ByteArray) :
    Data.Bytes.bytesToBigEndianNat (a ++ b) =
      Data.Bytes.bytesToBigEndianNat a * 256 ^ b.size +
        Data.Bytes.bytesToBigEndianNat b := by
  unfold Data.Bytes.bytesToBigEndianNat
  rw [Challenge.EvmProof.Bytecode.toList_eq_data,
    Challenge.EvmProof.Bytecode.toList_eq_data,
    Challenge.EvmProof.Bytecode.toList_eq_data]
  rw [ByteArray.data_append, Array.toList_append, List.foldl_append,
    foldl_bytes]
  rfl

private theorem foldl_bytes_lt (xs : List UInt8) :
    xs.foldl (fun n b => n * 256 + b.toNat) 0 < 256 ^ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, foldl_bytes]
      rw [List.length_cons, Nat.pow_succ]
      simp only [Nat.zero_mul, Nat.zero_add]
      have hx : x.toNat < 256 := x.toNat_lt
      calc
        x.toNat * 256 ^ xs.length +
            List.foldl (fun n b => n * 256 + b.toNat) 0 xs <
            x.toNat * 256 ^ xs.length + 256 ^ xs.length :=
          Nat.add_lt_add_left ih _
        _ = (x.toNat + 1) * 256 ^ xs.length := by ring
        _ ≤ 256 * 256 ^ xs.length :=
          Nat.mul_le_mul_right (256 ^ xs.length) (by omega)
        _ = 256 ^ xs.length * 256 := by omega

private theorem bytesToBigEndianNat_lt (bs : ByteArray) :
    Data.Bytes.bytesToBigEndianNat bs < 256 ^ bs.size := by
  unfold Data.Bytes.bytesToBigEndianNat
  rw [Challenge.EvmProof.Bytecode.toList_eq_data]
  simpa using foldl_bytes_lt bs.data.toList

/-- `BYTE 0..3` after MLOAD returns the corresponding zero-padded memory
byte. -/
theorem byteAt_readWord (bs : ByteArray) (off i : Nat) (hi : i < 4) :
    UInt256.byteAt (UInt256.ofNat i) (MachineState.readWord bs off) =
      UInt256.ofNat (bs[off + i]?.getD 0).toNat := by
  let first := Data.Bytes.bytesToBigEndianNat
    (MachineState.readPadded bs off 4)
  let rest := Data.Bytes.bytesToBigEndianNat
    (MachineState.readPadded bs (off + 4) 28)
  have hfirst : first < 256 ^ 4 := by
    simpa [first] using bytesToBigEndianNat_lt
      (MachineState.readPadded bs off 4)
  have hrest : rest < 256 ^ 28 := by
    simpa [rest] using bytesToBigEndianNat_lt
      (MachineState.readPadded bs (off + 4) 28)
  have hsplit : Data.Bytes.bytesToBigEndianNat
      (MachineState.readPadded bs off 32) = first * 256 ^ 28 + rest := by
    rw [readPadded_thirtyTwo_split, bytesToBigEndianNat_append]
    simp [first, rest]
  have hvalue : Data.Bytes.bytesToBigEndianNat
      (MachineState.readPadded bs off 32) < 2 ^ 256 := by
    rw [hsplit]
    have hpow : (256 : Nat) ^ 32 = 2 ^ 256 := by norm_num
    have hcombine : first * 256 ^ 28 + rest < 256 ^ 32 := by
      have hpowSplit : (256 : Nat) ^ 32 = 256 ^ 4 * 256 ^ 28 := by ring
      rw [hpowSplit]
      omega
    omega
  have hfirstBytes := bytesToBigEndianNat_readPadded_four bs off
  change first =
    ((((bs[off]?.getD 0).toNat * 256 +
        (bs[off + 1]?.getD 0).toNat) * 256 +
        (bs[off + 2]?.getD 0).toNat) * 256) +
      (bs[off + 3]?.getD 0).toNat at hfirstBytes
  have hb0 := (bs[off]?.getD 0).toNat_lt
  have hb1 := (bs[off + 1]?.getD 0).toNat_lt
  have hb2 := (bs[off + 2]?.getD 0).toNat_lt
  have hb3 := (bs[off + 3]?.getD 0).toNat_lt
  unfold MachineState.readWord UInt256.byteAt
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 256), if_neg (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hvalue, hsplit]
  change UInt256.ofNat
      (((first * 256 ^ 28 + rest) >>> (8 * (31 - i))) &&& 0xff) = _
  rw [show (0xff : Nat) = 2 ^ 8 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rw [hfirstBytes]
  interval_cases i
  · let tail := (((bs[off + 1]?.getD 0).toNat * 256 +
      (bs[off + 2]?.getD 0).toNat) * 256 +
      (bs[off + 3]?.getD 0).toNat) * 256 ^ 28 + rest
    have htail : tail < 256 ^ 31 := by
      dsimp [tail]
      norm_num [pow_mul] at *
      omega
    have hrearrange :
        (((((bs[off]?.getD 0).toNat * 256 +
              (bs[off + 1]?.getD 0).toNat) * 256 +
              (bs[off + 2]?.getD 0).toNat) * 256 +
              (bs[off + 3]?.getD 0).toNat) * 256 ^ 28 + rest) =
          (bs[off]?.getD 0).toNat * 256 ^ 31 + tail := by
      dsimp [tail]
      ring
    have hden : 2 ^ (8 * (31 - 0)) = 256 ^ 31 := by norm_num [pow_mul]
    rw [hden, hrearrange,
      Nat.mul_comm (bs[off]?.getD 0).toNat (256 ^ 31),
      Nat.mul_add_div (by positivity),
      Nat.div_eq_of_lt htail, Nat.add_zero,
      Nat.mod_eq_of_lt hb0]
    simp
  · let pre := (bs[off]?.getD 0).toNat * 256 +
      (bs[off + 1]?.getD 0).toNat
    let tail := ((bs[off + 2]?.getD 0).toNat * 256 +
      (bs[off + 3]?.getD 0).toNat) * 256 ^ 28 + rest
    have htail : tail < 256 ^ 30 := by
      dsimp [tail]
      norm_num [pow_mul] at *
      omega
    have hrearrange :
        (((((bs[off]?.getD 0).toNat * 256 +
              (bs[off + 1]?.getD 0).toNat) * 256 +
              (bs[off + 2]?.getD 0).toNat) * 256 +
              (bs[off + 3]?.getD 0).toNat) * 256 ^ 28 + rest) =
          pre * 256 ^ 30 + tail := by
      dsimp [pre, tail]
      ring
    have hden : 2 ^ (8 * (31 - 1)) = 256 ^ 30 := by norm_num [pow_mul]
    rw [hden, hrearrange, Nat.mul_comm pre (256 ^ 30),
      Nat.mul_add_div (by positivity),
      Nat.div_eq_of_lt htail, Nat.add_zero]
    dsimp [pre]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hb1]
  · let pre := ((bs[off]?.getD 0).toNat * 256 +
      (bs[off + 1]?.getD 0).toNat) * 256 +
      (bs[off + 2]?.getD 0).toNat
    let tail := (bs[off + 3]?.getD 0).toNat * 256 ^ 28 + rest
    have htail : tail < 256 ^ 29 := by
      dsimp [tail]
      norm_num [pow_mul] at *
      omega
    have hrearrange :
        (((((bs[off]?.getD 0).toNat * 256 +
              (bs[off + 1]?.getD 0).toNat) * 256 +
              (bs[off + 2]?.getD 0).toNat) * 256 +
              (bs[off + 3]?.getD 0).toNat) * 256 ^ 28 + rest) =
          pre * 256 ^ 29 + tail := by
      dsimp [pre, tail]
      ring
    have hden : 2 ^ (8 * (31 - 2)) = 256 ^ 29 := by norm_num [pow_mul]
    rw [hden, hrearrange, Nat.mul_comm pre (256 ^ 29),
      Nat.mul_add_div (by positivity),
      Nat.div_eq_of_lt htail, Nat.add_zero]
    dsimp [pre]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hb2]
  · let pre := (((bs[off]?.getD 0).toNat * 256 +
      (bs[off + 1]?.getD 0).toNat) * 256 +
      (bs[off + 2]?.getD 0).toNat) * 256 +
      (bs[off + 3]?.getD 0).toNat
    have hrearrange :
        (((((bs[off]?.getD 0).toNat * 256 +
              (bs[off + 1]?.getD 0).toNat) * 256 +
              (bs[off + 2]?.getD 0).toNat) * 256 +
              (bs[off + 3]?.getD 0).toNat) * 256 ^ 28 + rest) =
          pre * 256 ^ 28 + rest := by rfl
    have hden : 2 ^ (8 * (31 - 3)) = 256 ^ 28 := by norm_num [pow_mul]
    rw [hden, hrearrange, Nat.mul_comm pre (256 ^ 28),
      Nat.mul_add_div (by positivity),
      Nat.div_eq_of_lt hrest, Nat.add_zero]
    dsimp [pre]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hb3]

private theorem readLE32_eq_bytes (bs : ByteArray) (off : Nat) :
    Crypto.Ripemd160.readLE32 bs off =
      let b0 := (bs[off]?.getD 0).toUInt32
      let b1 := (bs[off + 1]?.getD 0).toUInt32
      let b2 := (bs[off + 2]?.getD 0).toUInt32
      let b3 := (bs[off + 3]?.getD 0).toUInt32
      (b0 ||| (b1 <<< UInt32.ofNat 8)) |||
        ((b2 <<< UInt32.ofNat 16) ||| (b3 <<< UInt32.ofNat 24)) := by
  unfold Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  simp only [List.range', List.foldl_cons, List.foldl_nil]
  have hbyte (i : Nat) :
      (if h : off + i < bs.size then bs[off + i].toUInt32 else 0) =
        (bs[off + i]?.getD 0).toUInt32 := by
    by_cases h : off + i < bs.size <;> simp [h]
  rw [hbyte 0, hbyte 1, hbyte 2, hbyte 3]
  norm_num
  rw [UInt32.or_assoc]
  rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.shiftLeft_zero]

@[simp] private theorem ofNat_byte_eq_ofUInt32 (b : UInt8) :
    UInt256.ofNat b.toNat = Challenge.EvmProof.Word.ofUInt32 b.toUInt32 := by
  unfold Challenge.EvmProof.Word.ofUInt32
  rw [UInt8.toNat_toUInt32]

/-- The masked EVM `MLOAD`/`BYTE` little-endian reader is exactly the
mathematical RIPEMD-160 four-byte reader. -/
theorem mask32_readLEWord_eq_readLE32 (bs : ByteArray) (off : Nat)
    (hoff : off < 2 ^ 256) :
    Challenge.EvmProof.Word.mask32
        (Schedule.readLEWord bs (UInt256.ofNat off)) =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.readLE32 bs off) := by
  unfold Schedule.readLEWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  dsimp only
  rw [show ({ val := 0 } : UInt256) = UInt256.ofNat 0 by rfl]
  rw [byteAt_readWord bs off 0 (by omega),
    byteAt_readWord bs off 1 (by omega),
    byteAt_readWord bs off 2 (by omega),
    byteAt_readWord bs off 3 (by omega)]
  simp only [Nat.add_zero, ofNat_byte_eq_ofUInt32]
  rw [Challenge.EvmProof.Word.mask32_eq_ofUInt32]
  apply congrArg Challenge.EvmProof.Word.ofUInt32
  change Challenge.EvmProof.Word.toUInt32
      ((Challenge.EvmProof.Word.ofUInt32 (bs[off]?.getD 0).toUInt32 |||
          UInt256.shiftLeft
            (Challenge.EvmProof.Word.ofUInt32 (bs[off + 1]?.getD 0).toUInt32)
            (UInt256.ofNat 8)) |||
        (UInt256.shiftLeft
            (Challenge.EvmProof.Word.ofUInt32 (bs[off + 2]?.getD 0).toUInt32)
            (UInt256.ofNat 16) |||
          UInt256.shiftLeft
            (Challenge.EvmProof.Word.ofUInt32 (bs[off + 3]?.getD 0).toUInt32)
            (UInt256.ofNat 24))) = _
  rw [Challenge.EvmProof.Word.toUInt32_or,
    Challenge.EvmProof.Word.toUInt32_or,
    Challenge.EvmProof.Word.toUInt32_or,
    Challenge.EvmProof.Word.toUInt32_ofUInt32]
  rw [Challenge.EvmProof.Word.toUInt32_shiftLeft_ofUInt32 _ 8 (by omega),
    Challenge.EvmProof.Word.toUInt32_shiftLeft_ofUInt32 _ 16 (by omega),
    Challenge.EvmProof.Word.toUInt32_shiftLeft_ofUInt32 _ 24 (by omega),
    readLE32_eq_bytes]

private theorem paddedMemory_eq_write (memory input : ByteArray)
    (hmemory : memory.size ≤ messageOffset) :
    paddedMemory memory input =
      MachineState.writeBytes memory (paddedMessage input) messageOffset := by
  have hsentinel : (sentinelMemory memory input).size =
      messageOffset + input.size + 1 := by
    simp only [sentinelMemory, copiedMemory, MachineState.writeBytes_size,
      show (ByteArray.mk #[0x80]).size = 1 by rfl, one_ne_zero, if_false]
    by_cases hz : input.size = 0
    · simp [hz]
      omega
    · rw [if_neg hz]
      omega
  have hpadded : (paddedMemory memory input).size =
      messageOffset + paddedLength input.size := by
    rw [paddedMemory, MachineState.writeBytes_size, lengthBytes_size,
      if_neg (by decide : 8 ≠ 0), hsentinel]
    have hfit := input_and_footer_fit input.size
    omega
  have hwritten :
      (MachineState.writeBytes memory (paddedMessage input) messageOffset).size =
        messageOffset + paddedLength input.size := by
    rw [MachineState.writeBytes_size,
      if_neg (Nat.ne_of_gt (by simpa using paddedLength_pos input.size)),
      paddedMessage_size]
    omega
  apply ByteArray.ext_getElem
  · exact hpadded.trans hwritten.symm
  · intro i hi₁ hi₂
    have hl := MachineState.writeBytes_getElem?_getD
      (sentinelMemory memory input) (lengthBytes input)
      (messageOffset + paddedLength input.size - 8) i
    have hs := MachineState.writeBytes_getElem?_getD
      (copiedMemory memory input) (ByteArray.mk #[0x80])
      (messageOffset + input.size) i
    have hc := MachineState.writeBytes_getElem?_getD memory input messageOffset i
    have hr := MachineState.writeBytes_getElem?_getD memory
      (paddedMessage input) messageOffset i
    have hleft : (paddedMemory memory input)[i]?.getD 0 =
        (paddedMemory memory input)[i] := by
      exact Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁
    have hright :
        (MachineState.writeBytes memory (paddedMessage input) messageOffset)[i]?.getD 0 =
          (MachineState.writeBytes memory (paddedMessage input) messageOffset)[i] := by
      exact Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₂
    rw [← hleft, ← hright]
    change (MachineState.writeBytes (sentinelMemory memory input) (lengthBytes input)
      (messageOffset + paddedLength input.size - 8))[i]?.getD 0 = _
    rw [hl, hr]
    change (sentinelMemory memory input)[i]?.getD 0 = _ at hs
    change (copiedMemory memory input)[i]?.getD 0 = _ at hc
    rw [hs, hc]
    simp only [lengthBytes_size, show (ByteArray.mk #[0x80]).size = 1 by rfl,
      paddedMessage_size]
    have hfit := input_and_footer_fit input.size
    have hprefix := prefix_size input.size
    have hlenOff : messageOffset + paddedLength input.size - 8 =
        messageOffset + input.size + 1 + zeroCount input.size := by omega
    rw [hlenOff] at hl ⊢
    have hiEnd : i < messageOffset + paddedLength input.size := by
      rw [← hpadded]
      exact hi₁
    by_cases hbefore : i < messageOffset
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
    · have hiBase : messageOffset ≤ i := by omega
      by_cases hlen : messageOffset + paddedLength input.size - 8 ≤ i
      · rw [if_pos (by omega), if_pos (by omega)]
        simp only [paddedMessage]
        rw [Challenge.EvmProof.Memory.getElem?_getD_append]
        rw [if_neg (by
          simp only [ByteArray.size_append, zeroBytes_size,
            show (ByteArray.mk #[0x80]).size = 1 by rfl]
          omega)]
        apply congrArg (fun k : Nat => (lengthBytes input)[k]?.getD 0)
        simp only [ByteArray.size_append, zeroBytes_size,
          show (ByteArray.mk #[0x80]).size = 1 by rfl]
        omega
      · have hlencond' : ¬(messageOffset + input.size + 1 + zeroCount input.size ≤ i ∧
            i < messageOffset + input.size + 1 + zeroCount input.size + 8) := by omega
        rw [if_neg hlencond']
        by_cases hsentinel : i = messageOffset + input.size
        · subst i
          rw [if_pos (by omega), if_pos (by omega)]
          simp only [paddedMessage]
          rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_pos (by
            simp only [ByteArray.size_append, zeroBytes_size,
              show (ByteArray.mk #[0x80]).size = 1 by rfl]
            omega)]
          rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_pos (by
            simp only [ByteArray.size_append,
              show (ByteArray.mk #[0x80]).size = 1 by rfl]
            omega)]
          rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_neg (by omega)]
          apply congrArg (fun k : Nat => (ByteArray.mk #[0x80])[k]?.getD 0)
          omega
        · rw [if_neg (by omega)]
          by_cases hinput : i < messageOffset + input.size
          · rw [if_pos (by omega), if_pos (by omega)]
            simp only [paddedMessage]
            rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_pos (by
              simp only [ByteArray.size_append, zeroBytes_size,
                show (ByteArray.mk #[0x80]).size = 1 by rfl]
              omega)]
            rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_pos (by
              simp only [ByteArray.size_append,
                show (ByteArray.mk #[0x80]).size = 1 by rfl]
              omega)]
            rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_pos (by omega)]
          · rw [if_neg (by omega), if_pos (by omega)]
            rw [Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le memory i
              (by omega)]
            simp only [paddedMessage]
            rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_pos (by
              simp only [ByteArray.size_append, zeroBytes_size,
                show (ByteArray.mk #[0x80]).size = 1 by rfl]
              omega)]
            rw [Challenge.EvmProof.Memory.getElem?_getD_append, if_neg (by
              simp only [ByteArray.size_append,
                show (ByteArray.mk #[0x80]).size = 1 by rfl]
              omega)]
            simp only [zeroBytes]
            let zeros : ByteArray :=
              ByteArray.mk (Array.replicate (zeroCount input.size) 0)
            have hzeros : zeros.size = zeroCount input.size := by
              change (Array.replicate (zeroCount input.size) 0).size = _
              exact Array.size_replicate
            change 0 = zeros[i - messageOffset - (input ++ ByteArray.mk #[0x80]).size]?.getD 0
            have hindex : i - messageOffset - (input ++ ByteArray.mk #[0x80]).size =
                i - messageOffset - (input.size + 1) := by
              simp only [ByteArray.size_append]
              rfl
            rw [hindex]
            rw [Challenge.EvmProof.Memory.getD0_eq_getElem!]
            by_cases hz : i - messageOffset - (input.size + 1) < zeroCount input.size
            · rw [getElem!_pos zeros _ (by rw [hzeros]; exact hz)]
              dsimp only [zeros]
              have harray : i - messageOffset - (input.size + 1) <
                  (Array.replicate (zeroCount input.size) (0 : UInt8)).size := by
                rw [Array.size_replicate]
                exact hz
              exact (Array.getElem_replicate harray).symm
            · rw [getElem!_neg zeros _ (by rw [hzeros]; exact hz)]
              rfl

/-- Reading at a relative padded-message offset is unchanged by its concrete
placement at `messageOffset`. -/
theorem readPadded_paddedMemory_shift (base input : ByteArray)
    (off width : Nat) (hbase : base.size ≤ messageOffset) :
    MachineState.readPadded (paddedMemory base input)
        (messageOffset + off) width =
      MachineState.readPadded (paddedMessage input) off width := by
  rw [paddedMemory_eq_write base input hbase]
  apply ByteArray.ext_getElem
  · simp
  · intro i hi₁ hi₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₂,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD]
    have hi : i < width := by simpa using hi₁
    rw [if_pos hi, if_pos hi]
    rw [MachineState.writeBytes_getElem?_getD]
    simp only [paddedMessage_size]
    by_cases hpadded : off + i < paddedLength input.size
    · rw [if_pos (by omega)]
      apply congrArg (fun n : Nat => (paddedMessage input)[n]?.getD 0)
      omega
    · rw [if_neg (by omega)]
      rw [Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le base _
        (by omega)]
      exact (Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le
        (paddedMessage input) (off + i) (by
          rw [paddedMessage_size]
          omega)).symm

theorem readWord_paddedMemory_shift (base input : ByteArray) (off : Nat)
    (hbase : base.size ≤ messageOffset) :
    MachineState.readWord (paddedMemory base input) (messageOffset + off) =
      MachineState.readWord (paddedMessage input) off := by
  unfold MachineState.readWord
  rw [readPadded_paddedMemory_shift base input off 32 hbase]

private theorem readLEWord_paddedMemory_shift (base input : ByteArray)
    (off : Nat) (hbase : base.size ≤ messageOffset)
    (hoff : messageOffset + off < 2 ^ 256) :
    Schedule.readLEWord (paddedMemory base input)
        (UInt256.ofNat (messageOffset + off)) =
      Schedule.readLEWord (paddedMessage input) (UInt256.ofNat off) := by
  unfold Schedule.readLEWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hoff,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : off < 2 ^ 256),
    readWord_paddedMemory_shift base input off hbase]

private theorem loadOffsetWord_eq (input : ByteArray) (blockOff k : Nat)
    (hfit : Challenge.Ripemd160.CalldataFits input)
    (hblock : blockOff + 64 ≤ paddedLength input.size)
    (hk : k < 16) :
    Schedule.loadOffsetWord
        (UInt256.ofNat (messageOffset + blockOff)) k =
      UInt256.ofNat (messageOffset + (blockOff + k * 4)) := by
  have hpadded := paddedLength_lt input.size
  have hinput : input.size < 2 ^ 64 := hfit
  have haddr : k * 2 ^ 2 + (messageOffset + blockOff) < 2 ^ 256 := by
    have hsmall : k * 2 ^ 2 + (messageOffset + blockOff) < 2 ^ 64 + 4096 := by
      simp only [messageOffset]
      omega
    exact lt_trans hsmall (by norm_num)
  unfold Schedule.loadOffsetWord
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by omega) (by omega),
    Challenge.EvmProof.Word.ofNat_add_ofNat haddr]
  congr 1
  omega

/-- The concrete padded memory and a complete-block pointer establish the
exact little-endian reader seam required by the generic schedule proof. -/
theorem paddedBlockAt (s : State) (base input : ByteArray)
    (msgOff : UInt256) (blockOff : Nat)
    (hmemory : s.memory = paddedMemory base input)
    (hbase : base.size ≤ messageOffset)
    (hmsgOff : msgOff = UInt256.ofNat (messageOffset + blockOff))
    (hfit : Challenge.Ripemd160.CalldataFits input)
    (hblock : blockOff + 64 ≤ paddedLength input.size) :
    ScheduleCorrect.MessageBlockAt s.memory msgOff
      (paddedMessage input) blockOff := by
  intro k hk
  rw [hmemory, hmsgOff]
  unfold ScheduleCorrect.expectedWord
  rw [loadOffsetWord_eq input blockOff k hfit hblock hk]
  have hpadded := paddedLength_lt input.size
  have haddr : messageOffset + (blockOff + k * 4) < 2 ^ 256 := by
    have hsmall : messageOffset + (blockOff + k * 4) < 2 ^ 64 + 4096 := by
      have hinput : input.size < 2 ^ 64 := hfit
      simp only [messageOffset]
      omega
    exact lt_trans hsmall (by norm_num)
  change Challenge.EvmProof.Word.mask32
      (Schedule.readLEWord (paddedMemory base input)
        (UInt256.ofNat (messageOffset + (blockOff + k * 4)))) = _
  rw [readLEWord_paddedMemory_shift base input (blockOff + k * 4)
    hbase haddr]
  exact mask32_readLEWord_eq_readLE32 (paddedMessage input)
    (blockOff + k * 4) (by omega)

/-- Every concrete padded-block read is above the schedule scratch area. -/
theorem scheduleSeparated (input : ByteArray) (msgOff : UInt256)
    (blockOff : Nat)
    (hmsgOff : msgOff = UInt256.ofNat (messageOffset + blockOff))
    (hfit : Challenge.Ripemd160.CalldataFits input)
    (hblock : blockOff + 64 ≤ paddedLength input.size) :
    ∀ k, k < 16 →
      0x4a0 ≤ (Schedule.loadOffsetWord msgOff k).toNat := by
  intro k hk
  rw [hmsgOff, loadOffsetWord_eq input blockOff k hfit hblock hk,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt]
  · simp only [messageOffset]
    omega
  · have hpadded := paddedLength_lt input.size
    have hinput : input.size < 2 ^ 64 := hfit
    have hsmall : messageOffset + (blockOff + k * 4) < 2 ^ 64 + 4096 := by
      simp only [messageOffset]
      omega
    exact lt_trans hsmall (by norm_num)

private theorem padBase_memory (input : ByteArray) :
    (PaddingTrace.padLengthReady input).memory =
      (Main.initializedState input).memory := by
  rfl

private theorem applyInitStore_size_le (s : State) (w : Artifact.InitStore)
    (hs : s.memory.size ≤ messageOffset) (hw : w ∈ Artifact.initStores) :
    (Main.applyInitStore s w).memory.size ≤ messageOffset := by
  have hoff : w.offset.toNat + 32 ≤ messageOffset := by
    simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil,
      or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [Main.applyInitStore]
  rw [MachineState.writeBytes_size, if_neg]
  · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    exact max_le hs hoff
  · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega

private theorem padBase_size (input : ByteArray) :
    (PaddingTrace.padLengthReady input).memory.size ≤ messageOffset := by
  rw [padBase_memory]
  unfold Main.initializedState
  have hfold : ∀ (ws : List Artifact.InitStore) (s : State),
      (∀ w, w ∈ ws → w ∈ Artifact.initStores) →
      s.memory.size ≤ messageOffset →
      (ws.foldl Main.applyInitStore s).memory.size ≤ messageOffset := by
    intro ws
    induction ws with
    | nil => simp
    | cons w ws ih =>
        intro s hmem hs
        simp only [List.foldl_cons]
        apply ih (Main.applyInitStore s w)
        · intro x hx
          exact hmem x (List.mem_cons_of_mem w hx)
        · exact applyInitStore_size_le s w hs (hmem w (by simp))
  apply hfold Artifact.initStores (Execution.mainStart input)
  · intro w hw
    exact hw
  · simp [Execution.mainStart, Execution.atPC, initialState, messageOffset]

/-- The certified padding trace establishes the schedule's mathematical
message-block precondition for every complete padded block. -/
theorem padReturned_paddedBlockAt (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (blockOff : Nat)
    (hblock : blockOff + 64 ≤ paddedLength input.size) :
    ScheduleCorrect.MessageBlockAt (PaddingTrace.padReturned input).memory
      (UInt256.ofNat (messageOffset + blockOff))
      (paddedMessage input) blockOff := by
  apply paddedBlockAt (PaddingTrace.padReturned input)
    (PaddingTrace.padLengthReady input).memory input
  · exact PaddingTrace.padReturned_memory input hfit
  · exact padBase_size input
  · rfl
  · exact hfit
  · exact hblock

/-- Block-number form of `padReturned_paddedBlockAt`, matching the driver's
`i * 64` block offset. -/
theorem padReturned_blockIndexAt (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < paddedLength input.size / 64) :
    ScheduleCorrect.MessageBlockAt (PaddingTrace.padReturned input).memory
      (UInt256.ofNat (messageOffset + i * 64))
      (paddedMessage input) (i * 64) := by
  apply padReturned_paddedBlockAt input hfit (i * 64)
  rw [paddedLength_eq_blocks input.size]
  omega

/-- The matching concrete block pointer is disjoint from all schedule
scratch slots. -/
theorem padReturned_blockIndexSeparated (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < paddedLength input.size / 64) :
    ∀ k, k < 16 →
      0x4a0 ≤ (Schedule.loadOffsetWord
        (UInt256.ofNat (messageOffset + i * 64)) k).toNat := by
  apply scheduleSeparated input (UInt256.ofNat (messageOffset + i * 64))
    (i * 64) rfl hfit
  rw [paddedLength_eq_blocks input.size]
  omega

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddedBlockBridge
