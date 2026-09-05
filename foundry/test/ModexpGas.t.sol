// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {console2} from "forge-std/Test.sol";
import {GasCrossCheck} from "./GasCrossCheck.sol";
import {Vectors} from "../src/Vectors.sol";
import {ModexpDeployed} from "evmification/modexp/ModexpDeployed.sol";

/// @notice Cross-checks the MODEXP challenge's published gas against a real EVM.
///
/// @dev The `leanGas` column is what `Challenge/Modexp/Scorer.lean` reports for
///      the frozen reference, as printed by `lake exe modexpchallenge` and
///      summarized in that challenge's README gas table. The original 13-vector
///      subset runs here against the same bytecode under revm.
///
///      MODEXP is the sharpest of the three cross-checks. Its cost is
///      branch-sensitive rather than a function of calldata length alone, the
///      reference switches between a `MULMOD` fast path and a 32-limb fallback,
///      and the precompile's own price follows the Osaka/EIP-7883 schedule. The
///      precompile column therefore also checks the Lean side's model of that
///      schedule against revm's.
contract ModexpGasTest is GasCrossCheck {
    /// @dev One scored vector, plus the gas `Scorer.lean` reports the Osaka
    ///      MODEXP precompile would charge for the same tuple.
    struct ModexpCase {
        string label;
        bytes input;
        uint256 leanGas;
        uint256 leanPrecompileGas;
    }

    ModexpCase[] internal cases;
    address internal refAddr;
    address internal evmification;

    function setUp() public override {
        super.setUp();
        refAddr = _etchReference("../Challenge/Modexp/Reference");
        evmification = address(new ModexpDeployed());

        // Challenge/Modexp/Scorer.lean, `vectors`, in order.
        cases.push(ModexpCase("empty tuple", "", 183, 500));
        cases.push(ModexpCase("2^5 mod 13", Vectors.makeInput(2, 5, 13, 1, 1, 1), 2403, 500));
        cases.push(ModexpCase("zero exponent", Vectors.makeInput(42, 0, 97, 1, 0, 1), 1193, 500));
        cases.push(ModexpCase("zero modulus", Vectors.makeInput(42, 7, 0, 1, 1, 12), 950, 500));
        cases.push(ModexpCase("zero modulus size", Vectors.makeInput(42, 7, 0, 1, 1, 0), 183, 500));
        cases.push(ModexpCase("EIP-198 example 1", _eipExample1(), 39913, 4080));
        cases.push(ModexpCase("EIP-198 example 2", _eipExample2(), 39773, 4080));
        cases.push(ModexpCase("trailing-zero normalization", _truncatedModulus(), 3613, 500));
        cases.push(ModexpCase("257-bit modulus", _wideModulus(), 18958693, 500));
        cases.push(ModexpCase("BN254 modular inversion", _bn254ModularInversion(), 44253, 4048));
        cases.push(ModexpCase("random 256-bit modexp", _random256(), 44253, 4080));
        cases.push(ModexpCase("RSA-1024 e=3", _rsa1024e3(), 70590487, 512));
        cases.push(ModexpCase("RSA-2048 e=65537", _rsa2048e65537(), 770374226, 32768));
    }

    /// @dev `Scorer.eipExample1`.
    function _eipExample1() private pure returns (bytes memory) {
        return hex"0000000000000000000000000000000000000000000000000000000000000001"
            hex"0000000000000000000000000000000000000000000000000000000000000020"
            hex"0000000000000000000000000000000000000000000000000000000000000020" hex"03"
            hex"fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e"
            hex"fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f";
    }

    /// @dev `Scorer.eipExample2`.
    function _eipExample2() private pure returns (bytes memory) {
        return hex"0000000000000000000000000000000000000000000000000000000000000000"
            hex"0000000000000000000000000000000000000000000000000000000000000020"
            hex"0000000000000000000000000000000000000000000000000000000000000020"
            hex"fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e"
            hex"fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f";
    }

    /// @dev `Scorer.truncatedModulus`: EIP-198's truncated-input example, where
    ///      the single supplied modulus byte reads as `0x80` followed by 31
    ///      zero bytes.
    function _truncatedModulus() private pure returns (bytes memory) {
        return hex"0000000000000000000000000000000000000000000000000000000000000001"
            hex"0000000000000000000000000000000000000000000000000000000000000002"
            hex"0000000000000000000000000000000000000000000000000000000000000020" hex"03ffff80";
    }

    /// @dev `Scorer`'s 257-bit tuple: `makeInput (2^256 + 5) 3 (2^256 + 7) 33 1 33`.
    ///      Both operands exceed 256 bits, so they are built byte-wise.
    function _wideModulus() private pure returns (bytes memory) {
        bytes memory base = abi.encodePacked(bytes1(0x01), bytes32(uint256(5)));
        bytes memory exponent = abi.encodePacked(bytes1(0x03));
        bytes memory modulus = abi.encodePacked(bytes1(0x01), bytes32(uint256(7)));
        return Vectors.makeInputBytes(base, exponent, modulus);
    }

    /// @dev `Scorer.bn254ModularInversion`: `x^(p - 2) mod p` in the BN254 base field.
    function _bn254ModularInversion() private pure returns (bytes memory) {
        return Vectors.makeInputBytes(
            hex"0d2fb5ffb5b07c344bcf7640e3908737f96cce132e7e9110de36377b5d5c6289",
            hex"30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd45",
            hex"30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47"
        );
    }

    /// @dev `Scorer.random256`: a fixed, reproducible full-width tuple.
    function _random256() private pure returns (bytes memory) {
        return Vectors.makeInputBytes(
            hex"a1f0b222a74b403a5a84d341cdd90fc26bf8769225b24557b64d01d7df61d9fd",
            hex"eca0f5ed5862646d6dc22650707a487c3436d99d7dbbba56b2f630cb682e1941",
            hex"afea24ccce325d471af2371241676b55270044423156c0904bb50225867f93a5"
        );
    }

    /// @dev `Scorer.rsa1024e3`, using RFC 9500's `testRSA1024` modulus.
    function _rsa1024e3() private pure returns (bytes memory) {
        return Vectors.makeInputBytes(
            hex"1370d5cf7cd3f80baf7ae9fddfdfcc0253d7d1f00fa2985f14456e44cb16bcdf"
            hex"6269d1ed3f20cfd7a7e421752a77c1b47db96367c224e660a706bbceff1e8bae"
            hex"1e5e0c04e5ec10b0a6876d2d05fdf6184e64794efd75567969f9f67444ba5b2d"
            hex"2ddb6b0396504efc38ea5664a4e8f2e76c29bd9d23e15e48b40b5754830bd0f2",
            hex"03",
            hex"b0d18352a88f53d5516f46c20e7a367d7de88acf54a019f6def57ab9b44ceddb"
            hex"2242b1bca0fb1b5cb82b3036176a63903564dec6eb41db2f8fc787f4e52e1149"
            hex"e33347572973f660c3c77ca9e0821c2b695be7ae9d7d30f4079110f48aae6f8b"
            hex"702d474b2900817f2866249bec12a2b19b8278416808f81ae1fcf9b7778a623f"
        );
    }

    /// @dev `Scorer.rsa2048e65537`, using RFC 9500's `testRSA2048` modulus.
    function _rsa2048e65537() private pure returns (bytes memory) {
        return Vectors.makeInputBytes(
            hex"0b81c9d16a35da3debeb1e95032d1a2c1793b3179d8a5fda6baa3372d44b8e89"
            hex"8be842be71bd691a8969b83040ea9ab769c000aee702af762e164d8cfaf4599b"
            hex"612e21bf0b5f09f1049d390c15f0dbbe9118e1460f79e4c128a5992175b58aea"
            hex"bdeed7f45ace257a4ff2c8d94cc202cfefac112c4013ee3d25c1df1c28daf411"
            hex"9a5fbc83a78e6b70fb2f7aca1004390385e09d6e821cd5cb7cb21d7e5cc8d792"
            hex"2a74521233519f34f2596cab25b5fe618752b7b5fc696d8040a8ce88a337b52f"
            hex"399a2c6ac3e4bf7fec0b1c0b4948fcc2dd1261d5347512c957dd9daae4103ac5"
            hex"a9002ec564a1611ec2b27d297b25e296dc1610cd0f8fe7e8c15b294edd5295d4",
            hex"010001",
            hex"b0f9e81943a7ae9892aade17ca7c40f8744fed2f8148e6c8eaa27b7d001548fb"
            hex"5192ab28b56c5060b118ccd131e594874c6ca989b56c27296f09fb93a034df32"
            hex"e97c6ff0998cfd8e6f42dda58acd1fa97986f144f3d154d67650175e6854b3a9"
            hex"52003bc06887b8455ac2b19f7b2f76504ebc98ec945571b07892150ddc6a74ca"
            hex"0fbcd35497ce81534daf9418844b13aea31f9d5a6b9557bbdf619efd4e887f2d"
            hex"42b8dd8bc987eae1bf89cab85ee21e356305df6c07a8838e3ef41c595dcce43d"
            hex"afc49123ef4d8abba93d3905e4028d7ba91484a27596e07b4b6ed992f077b524"
            hex"d3dcfe7ddd5549be7cce8da035cfa0b3fb8f9e46f732b2a86b460165c08f5313"
        );
    }

    function test_vectors_match_scorer() public view {
        assertEq(cases.length, 13, "vector count");
        assertEq(pin.provedSize, 1284, "reference bytecode size");
        assertEq(refAddr.code.length, 1284, "etched code size");

        uint256[13] memory sizes = [uint256(0), 99, 98, 110, 98, 161, 160, 100, 163, 192, 192, 353, 611];
        for (uint256 i = 0; i < cases.length; i++) {
            assertEq(cases[i].input.length, sizes[i], cases[i].label);
        }
    }

    /// @dev The reference must return what the `0x05` precompile returns, so
    ///      the gas comparison is between implementations of one function.
    function test_reference_returns_precompile_result() public view {
        for (uint256 i = 0; i < cases.length; i++) {
            (, bytes memory ret) = _gas(refAddr, cases[i].input);
            (, bytes memory expected) = _gas(address(0x05), cases[i].input);
            assertEq(ret, expected, cases[i].label);
        }
    }

    /// @notice The cross-check: revm must charge what `Scorer.lean` reports.
    function test_reference_gas_matches_lean_scorer() public view {
        uint256 leanTotal;
        uint256 forgeTotal;
        _header("MODEXP reference: Lean scorer vs revm");
        for (uint256 i = 0; i < cases.length; i++) {
            (uint256 gasUsed,) = _gas(refAddr, cases[i].input);
            _row(cases[i].label, cases[i].input.length, cases[i].leanGas, gasUsed);
            assertEq(gasUsed, cases[i].leanGas, cases[i].label);
            leanTotal += cases[i].leanGas;
            forgeTotal += gasUsed;
        }
        _row("all vectors", 0, leanTotal, forgeTotal);
        assertEq(forgeTotal, 860100123, "13-vector subset total");
    }

    /// @dev The scorer's `precompile` column comes from the pinned semantics'
    ///      own Osaka MODEXP pricing. Measuring `0x05` through the same probe
    ///      checks that model against revm's implementation of EIP-7883.
    function test_precompile_schedule_matches_lean_model() public view {
        uint256 leanTotal;
        uint256 forgeTotal;
        _header("MODEXP precompile (0x05): Lean gas model vs revm");
        for (uint256 i = 0; i < cases.length; i++) {
            (uint256 precompileGas,) = _gas(address(0x05), cases[i].input);
            _row(cases[i].label, cases[i].input.length, cases[i].leanPrecompileGas, precompileGas);
            assertEq(precompileGas, cases[i].leanPrecompileGas, cases[i].label);
            leanTotal += cases[i].leanPrecompileGas;
            forgeTotal += precompileGas;
        }
        _row("all vectors", 0, leanTotal, forgeTotal);
        assertEq(forgeTotal, 53068, "README precompile total");
    }

    /// @dev The scorer scores from a fixed initial state; the reference's gas
    ///      must not depend on the account's storage or balance either.
    function test_gas_is_state_independent() public {
        _assertGasIsStateIndependent(refAddr, cases[0].input, "empty tuple");
        _assertGasIsStateIndependent(refAddr, cases[8].input, "257-bit modulus");
    }

    /// @dev Computes the `vs precompile` ratio for the 13-vector subset.
    function test_subset_precompile_ratio() public view {
        uint256 referenceTotal;
        uint256 precompileTotal;
        for (uint256 i = 0; i < cases.length; i++) {
            (uint256 gasUsed,) = _gas(refAddr, cases[i].input);
            (uint256 precompileGas,) = _gas(address(0x05), cases[i].input);
            referenceTotal += gasUsed;
            precompileTotal += precompileGas;
        }
        console2.log(
            string.concat(
                "reference vs precompile: ", _ratio(referenceTotal, precompileTotal), " (subset: 16207.51x)"
            )
        );
        assertEq(_ratio(referenceTotal, precompileTotal), "16207.51x", "vs precompile ratio");
    }

    /// @notice Measures eth-act/evmification's Solidity implementation on the
    ///         same vectors, through the same probe.
    function test_evmification_comparison() public view {
        uint256 referenceTotal;
        uint256 evmificationTotal;
        uint256 precompileTotal;
        uint256 atOrBelowPrecompile;

        console2.log("");
        console2.log("MODEXP on the Lean scorer's vectors (frame gas, revm)");
        console2.log(
            string.concat(
                _rpad("vector", 30),
                _rpad("bytes", 7),
                _rpad("reference", 12),
                _rpad("evmification", 14),
                "precompile"
            )
        );
        for (uint256 i = 0; i < cases.length; i++) {
            (uint256 referenceGas,) = _gas(refAddr, cases[i].input);
            (uint256 evmificationGas, bytes memory ret) = _gas(evmification, cases[i].input);
            (uint256 precompileGas, bytes memory expected) = _gas(address(0x05), cases[i].input);

            assertEq(ret, expected, cases[i].label);

            console2.log(
                string.concat(
                    _rpad(cases[i].label, 30),
                    _rpad(vm.toString(cases[i].input.length), 7),
                    _rpad(vm.toString(referenceGas), 12),
                    _rpad(vm.toString(evmificationGas), 14),
                    vm.toString(precompileGas)
                )
            );
            if (evmificationGas <= precompileGas) atOrBelowPrecompile++;
            referenceTotal += referenceGas;
            evmificationTotal += evmificationGas;
            precompileTotal += precompileGas;
        }
        console2.log(
            string.concat(
                _rpad("all vectors", 30),
                _rpad("-", 7),
                _rpad(vm.toString(referenceTotal), 12),
                _rpad(vm.toString(evmificationTotal), 14),
                vm.toString(precompileTotal)
            )
        );
        console2.log(
            string.concat(
                "vs precompile: reference ",
                _ratio(referenceTotal, precompileTotal),
                ", evmification ",
                _ratio(evmificationTotal, precompileTotal)
            )
        );
        // On MODEXP this is not a formality: the precompile's EIP-7883 floor is
        // 500 gas, and a Solidity implementation can settle a trivial tuple for
        // less than that.
        console2.log(
            string.concat(
                "evmification at or below the precompile's price on ",
                vm.toString(atOrBelowPrecompile),
                " of ",
                vm.toString(cases.length),
                " vectors"
            )
        );
    }
}
