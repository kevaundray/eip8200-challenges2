import Challenge.Modexp.Spec
import EvmSemantics.EVM.StepF
import EvmSemantics.Data.Hex
set_option warningAsError true

/-!
# MODEXP executable falsification checks

The scorer compares candidate returndata with the pinned precompile-level
`spec`. It includes the EIP-198 examples, edge cases, trailing-zero input
normalization, BN254 inversion, full-width arithmetic, and a deterministic
public corpus through 2048-bit operands that exercises the multi-limb path.
-/

namespace Challenge.Modexp.Scorer

open EvmSemantics
open Challenge.Modexp

def scoringGas : Nat := 1_000_000_000_000
def scoringFuel : Nat := 500_000_000

def runEvm : Nat → EVM.State → EVM.State
  | 0, state => state
  | fuel + 1, state => if state.isDone then state else runEvm fuel (EVM.stepF state)

structure Vector where
  label : String
  input : ByteArray

private def fromHex (hex : String) : ByteArray := Hex.hexToBytes hex

private def word (n : Nat) : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded n 32

private def operand (n width : Nat) : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded n width

def makeInput (base exponent modulus bsize esize msize : Nat) : ByteArray :=
  word bsize ++ word esize ++ word msize ++
    operand base bsize ++ operand exponent esize ++ operand modulus msize

/-- Build a MODEXP tuple from already encoded, full-width operands. -/
def makeInputBytes (base exponent modulus : ByteArray) : ByteArray :=
  word base.size ++ word exponent.size ++ word modulus.size ++
    base ++ exponent ++ modulus

private def makeHexInput (base exponent modulus : String) : ByteArray :=
  makeInputBytes (fromHex base) (fromHex exponent) (fromHex modulus)

/-- Reproducible bytes produced by a 64-bit linear congruential generator.
This is test data generation, not a cryptographic random-number generator. -/
private def generatedBytes (seed size : Nat) : ByteArray :=
  let rec go (remaining state : Nat) (bytes : Array UInt8) : ByteArray :=
    match remaining with
    | 0 => ByteArray.mk bytes
    | n + 1 =>
        let next :=
          (state * 6364136223846793005 + 1442695040888963407) % (2 ^ 64)
        go n next (bytes.push (UInt8.ofNat (next / (2 ^ 56))))
  go size (seed % (2 ^ 64)) #[]

/-- A generated big-endian operand whose first bit is set. -/
private def generatedOperand (seed : Nat) : Nat → ByteArray
  | 0 => ByteArray.empty
  | n + 1 =>
      ByteArray.mk #[UInt8.ofNat (128 + seed % 128)] ++
        generatedBytes (seed + 0x9e3779b97f4a7c15) n

/-- A generated full-width odd modulus. -/
private def generatedModulus (seed : Nat) : Nat → ByteArray
  | 0 => ByteArray.empty
  | 1 => ByteArray.mk #[UInt8.ofNat (129 + 2 * (seed % 64))]
  | n + 2 =>
      ByteArray.mk #[UInt8.ofNat (128 + seed % 128)] ++
        generatedBytes (seed + 0xd1b54a32d192ed03) n ++
        ByteArray.mk #[UInt8.ofNat (1 + 2 * (seed % 127))]

private def generatedInput
    (seed width exponent exponentWidth : Nat) : ByteArray :=
  makeInputBytes
    (generatedOperand (3 * seed + 1) width)
    (operand exponent exponentWidth)
    (generatedModulus (3 * seed + 2) width)

private def generatedWideExponentInput
    (seed width exponentWidth : Nat) : ByteArray :=
  makeInputBytes
    (generatedOperand (3 * seed + 1) width)
    (generatedOperand (3 * seed + 3) exponentWidth)
    (generatedModulus (3 * seed + 2) width)

/-- The exponent prefix used by the Osaka/EIP-7883 precompile gas formula. -/
def exponentHead (input : ByteArray) : Nat :=
  let size := Nat.min (exponentSize input) 32
  EVM.Precompile.bytesToNatPadded input (96 + baseSize input) size

/-- Gas charged by the pinned Osaka MODEXP precompile for this tuple. -/
def precompileGas (input : ByteArray) : Nat :=
  EVM.Precompile.modexpGas .Osaka (baseSize input) (exponentSize input)
    (modulusSize input) (exponentHead input)

def eipExample1 : ByteArray := fromHex
  ("0000000000000000000000000000000000000000000000000000000000000001" ++
   "0000000000000000000000000000000000000000000000000000000000000020" ++
   "0000000000000000000000000000000000000000000000000000000000000020" ++
   "03" ++
   "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e" ++
   "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f")

def eipExample2 : ByteArray := fromHex
  ("0000000000000000000000000000000000000000000000000000000000000000" ++
   "0000000000000000000000000000000000000000000000000000000000000020" ++
   "0000000000000000000000000000000000000000000000000000000000000020" ++
   "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e" ++
   "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f")

/-- EIP-198's truncated-input example: the one supplied modulus byte is
interpreted as `0x80` followed by 31 zero bytes. -/
def truncatedModulus : ByteArray := fromHex
  ("0000000000000000000000000000000000000000000000000000000000000001" ++
   "0000000000000000000000000000000000000000000000000000000000000002" ++
   "0000000000000000000000000000000000000000000000000000000000000020" ++
   "03ffff80")

/-- Inversion of a fixed nonzero element in the BN254 base field, computed as
`x^(p - 2) mod p`. The element is SHA-256-derived from the domain
`eip8200-challenges/modexp/bn254-inversion/base` and reduced modulo `p`. -/
def bn254ModularInversion : ByteArray := makeHexInput
  "0d2fb5ffb5b07c344bcf7640e3908737f96cce132e7e9110de36377b5d5c6289"
  "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd45"
  "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47"

/-- Fermat exponentiation of the fixed BN254 field element: `x^(p - 1) mod p`. -/
def bn254Fermat : ByteArray := makeHexInput
  "0d2fb5ffb5b07c344bcf7640e3908737f96cce132e7e9110de36377b5d5c6289"
  "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd46"
  "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47"

/-- A reproducible full-width 256-bit tuple. Each operand is derived from a
SHA-256 domain below `eip8200-challenges/modexp/random-256/`; the modulus is
forced to be odd and every operand has its high bit set. -/
def random256 : ByteArray := makeHexInput
  "a1f0b222a74b403a5a84d341cdd90fc26bf8769225b24557b64d01d7df61d9fd"
  "eca0f5ed5862646d6dc22650707a487c3436d99d7dbbba56b2f630cb682e1941"
  "afea24ccce325d471af2371241676b55270044423156c0904bb50225867f93a5"

/-- A full-width RSA-1024 operation with public exponent 3. The modulus is
RFC 9500's `testRSA1024`; the base is SHAKE256-derived from the domain
`eip8200-challenges/modexp/rsa-1024/base`. -/
def rsa1024e3 : ByteArray := makeHexInput
  ("1370d5cf7cd3f80baf7ae9fddfdfcc0253d7d1f00fa2985f14456e44cb16bcdf" ++
   "6269d1ed3f20cfd7a7e421752a77c1b47db96367c224e660a706bbceff1e8bae" ++
   "1e5e0c04e5ec10b0a6876d2d05fdf6184e64794efd75567969f9f67444ba5b2d" ++
   "2ddb6b0396504efc38ea5664a4e8f2e76c29bd9d23e15e48b40b5754830bd0f2")
  "03"
  ("b0d18352a88f53d5516f46c20e7a367d7de88acf54a019f6def57ab9b44ceddb" ++
   "2242b1bca0fb1b5cb82b3036176a63903564dec6eb41db2f8fc787f4e52e1149" ++
   "e33347572973f660c3c77ca9e0821c2b695be7ae9d7d30f4079110f48aae6f8b" ++
   "702d474b2900817f2866249bec12a2b19b8278416808f81ae1fcf9b7778a623f")

/-- A full-width RSA-2048 operation with public exponent 65537. The modulus is
RFC 9500's `testRSA2048`; the base is SHAKE256-derived from the domain
`eip8200-challenges/modexp/rsa-2048/base`. -/
def rsa2048e65537 : ByteArray := makeHexInput
  ("0b81c9d16a35da3debeb1e95032d1a2c1793b3179d8a5fda6baa3372d44b8e89" ++
   "8be842be71bd691a8969b83040ea9ab769c000aee702af762e164d8cfaf4599b" ++
   "612e21bf0b5f09f1049d390c15f0dbbe9118e1460f79e4c128a5992175b58aea" ++
   "bdeed7f45ace257a4ff2c8d94cc202cfefac112c4013ee3d25c1df1c28daf411" ++
   "9a5fbc83a78e6b70fb2f7aca1004390385e09d6e821cd5cb7cb21d7e5cc8d792" ++
   "2a74521233519f34f2596cab25b5fe618752b7b5fc696d8040a8ce88a337b52f" ++
   "399a2c6ac3e4bf7fec0b1c0b4948fcc2dd1261d5347512c957dd9daae4103ac5" ++
   "a9002ec564a1611ec2b27d297b25e296dc1610cd0f8fe7e8c15b294edd5295d4")
  "010001"
  ("b0f9e81943a7ae9892aade17ca7c40f8744fed2f8148e6c8eaa27b7d001548fb" ++
   "5192ab28b56c5060b118ccd131e594874c6ca989b56c27296f09fb93a034df32" ++
   "e97c6ff0998cfd8e6f42dda58acd1fa97986f144f3d154d67650175e6854b3a9" ++
   "52003bc06887b8455ac2b19f7b2f76504ebc98ec945571b07892150ddc6a74ca" ++
   "0fbcd35497ce81534daf9418844b13aea31f9d5a6b9557bbdf619efd4e887f2d" ++
   "42b8dd8bc987eae1bf89cab85ee21e356305df6c07a8838e3ef41c595dcce43d" ++
   "afc49123ef4d8abba93d3905e4028d7ba91484a27596e07b4b6ed992f077b524" ++
   "d3dcfe7ddd5549be7cce8da035cfa0b3fb8f9e46f732b2a86b460165c08f5313")

/-- Forty-eight deterministic public inputs. Repeated operand widths make
exact-input dispatch increasingly costly while retaining reproducibility. -/
def generatedVectors : List Vector :=
  [ { label := "generated 256-bit #01 BN254 p-1", input := bn254Fermat }
  , { label := "generated 256-bit #02 full exponent", input := generatedWideExponentInput 0x1002 32 32 }
  , { label := "generated 256-bit #03 full exponent", input := generatedWideExponentInput 0x1003 32 32 }
  , { label := "generated 256-bit #04 full exponent", input := generatedWideExponentInput 0x1004 32 32 }
  , { label := "generated 256-bit #05 full exponent", input := generatedWideExponentInput 0x1005 32 32 }
  , { label := "generated 256-bit #06 full exponent", input := generatedWideExponentInput 0x1006 32 32 }
  , { label := "generated 256-bit #07 full exponent", input := generatedWideExponentInput 0x1007 32 32 }
  , { label := "generated 256-bit #08 full exponent", input := generatedWideExponentInput 0x1008 32 32 }
  , { label := "generated 256-bit #09 full exponent", input := generatedWideExponentInput 0x1009 32 32 }
  , { label := "generated 256-bit #10 full exponent", input := generatedWideExponentInput 0x100a 32 32 }
  , { label := "generated 256-bit #11 full exponent", input := generatedWideExponentInput 0x100b 32 32 }
  , { label := "generated 256-bit #12 full exponent", input := generatedWideExponentInput 0x100c 32 32 }
  , { label := "generated 256-bit #13 full exponent", input := generatedWideExponentInput 0x100d 32 32 }
  , { label := "generated 256-bit #14 full exponent", input := generatedWideExponentInput 0x100e 32 32 }
  , { label := "generated 256-bit #15 full exponent", input := generatedWideExponentInput 0x100f 32 32 }
  , { label := "generated 256-bit #16 full exponent", input := generatedWideExponentInput 0x1010 32 32 }
  , { label := "generated 256-bit #17 full exponent", input := generatedWideExponentInput 0x1011 32 32 }
  , { label := "generated 256-bit #18 full exponent", input := generatedWideExponentInput 0x1012 32 32 }
  , { label := "generated 256-bit #19 full exponent", input := generatedWideExponentInput 0x1013 32 32 }
  , { label := "generated 256-bit #20 full exponent", input := generatedWideExponentInput 0x1014 32 32 }
  , { label := "generated 256-bit #21 full exponent", input := generatedWideExponentInput 0x1015 32 32 }
  , { label := "generated 256-bit #22 full exponent", input := generatedWideExponentInput 0x1016 32 32 }
  , { label := "generated 256-bit #23 full exponent", input := generatedWideExponentInput 0x1017 32 32 }
  , { label := "generated 256-bit #24 full exponent", input := generatedWideExponentInput 0x1018 32 32 }
  , { label := "generated 256-bit #25 full exponent", input := generatedWideExponentInput 0x1019 32 32 }
  , { label := "generated 256-bit #26 full exponent", input := generatedWideExponentInput 0x101a 32 32 }
  , { label := "generated 256-bit #27 full exponent", input := generatedWideExponentInput 0x101b 32 32 }
  , { label := "generated 256-bit #28 full exponent", input := generatedWideExponentInput 0x101c 32 32 }
  , { label := "generated 256-bit #29 full exponent", input := generatedWideExponentInput 0x101d 32 32 }
  , { label := "generated 256-bit #30 full exponent", input := generatedWideExponentInput 0x101e 32 32 }
  , { label := "generated 256-bit #31 full exponent", input := generatedWideExponentInput 0x101f 32 32 }
  , { label := "generated 256-bit #32 full exponent", input := generatedWideExponentInput 0x1020 32 32 }
  , { label := "generated RSA-1024 #01 e=3", input := generatedInput 0x3001 128 3 1 }
  , { label := "generated RSA-1024 #02 e=3", input := generatedInput 0x3002 128 3 1 }
  , { label := "generated RSA-1024 #03 e=3", input := generatedInput 0x3003 128 3 1 }
  , { label := "generated RSA-1024 #04 e=17", input := generatedInput 0x3004 128 17 1 }
  , { label := "generated RSA-1024 #05 e=17", input := generatedInput 0x3005 128 17 1 }
  , { label := "generated RSA-1024 #06 e=17", input := generatedInput 0x3006 128 17 1 }
  , { label := "generated RSA-1024 #07 e=257", input := generatedInput 0x3007 128 257 2 }
  , { label := "generated RSA-1024 #08 e=257", input := generatedInput 0x3008 128 257 2 }
  , { label := "generated RSA-1024 #09 e=65537", input := generatedInput 0x3009 128 65537 3 }
  , { label := "generated RSA-1024 #10 e=65537", input := generatedInput 0x300a 128 65537 3 }
  , { label := "generated RSA-2048 #01 e=3", input := generatedInput 0x4001 256 3 1 }
  , { label := "generated RSA-2048 #02 e=3", input := generatedInput 0x4002 256 3 1 }
  , { label := "generated RSA-2048 #03 e=17", input := generatedInput 0x4003 256 17 1 }
  , { label := "generated RSA-2048 #04 e=17", input := generatedInput 0x4004 256 17 1 }
  , { label := "generated RSA-2048 #05 e=257", input := generatedInput 0x4005 256 257 2 }
  , { label := "generated RSA-2048 #06 e=65537", input := generatedInput 0x4006 256 65537 3 }
  ]

theorem generatedVectors_length : generatedVectors.length = 48 := by decide

theorem firstGeneratedVector_exponentHead :
    generatedVectors[0]?.map (fun vector => exponentHead vector.input) =
      some 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd46 := by
  native_decide

def vectors : List Vector :=
  [ { label := "empty tuple", input := ByteArray.empty }
  , { label := "2^5 mod 13", input := makeInput 2 5 13 1 1 1 }
  , { label := "zero exponent", input := makeInput 42 0 97 1 0 1 }
  , { label := "zero modulus", input := makeInput 42 7 0 1 1 12 }
  , { label := "zero modulus size", input := makeInput 42 7 0 1 1 0 }
  , { label := "EIP-198 example 1", input := eipExample1 }
  , { label := "EIP-198 example 2", input := eipExample2 }
  , { label := "trailing-zero normalization", input := truncatedModulus }
  , { label := "257-bit modulus"
    , input := makeInput (2 ^ 256 + 5) 3 (2 ^ 256 + 7) 33 1 33 }
  , { label := "BN254 modular inversion", input := bn254ModularInversion }
  , { label := "random 256-bit modexp", input := random256 }
  , { label := "RSA-1024 e=3", input := rsa1024e3 }
  , { label := "RSA-2048 e=65537", input := rsa2048e65537 }
  ] ++ generatedVectors

theorem vectors_length : vectors.length = 61 := by decide

inductive Outcome where
  | ok (gas : Nat)
  | wrongResult (got expected : String) (gas : Nat)
  | badHalt (halt : String) (gas : Nat)
  | outOfFuel

def Outcome.gas? : Outcome → Option Nat
  | .ok gas | .wrongResult _ _ gas | .badHalt _ gas => some gas
  | .outOfFuel => none

def score (code input : ByteArray) : Outcome :=
  let start := initialState code input scoringGas
  let final := runEvm scoringFuel start
  if !final.isDone then .outOfFuel else
  let gas := start.gasAvailable - final.gasAvailable
  match final.halt with
  | .Returned =>
      let expected := spec input
      if final.hReturn == expected then .ok gas
      else .wrongResult (Hex.bytesToHex final.hReturn) (Hex.bytesToHex expected) gas
  | halt => .badHalt (toString (repr halt)) gas

end Challenge.Modexp.Scorer
