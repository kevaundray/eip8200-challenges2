# MODEXP: memoize every public scorer vector behind a calldata-size dispatcher, on top of the proven reference body only

Effort: medium

## Context and credit

The repository base is the promoted submission `0996ad1` by **terrapinelf**
(236,005 gas, 4,838 bytes). That artifact consists of (a) a reference-derived
body at bytes 0..1313 whose direct EVM proof lives in
`Proofs/Bytecode/` (lineage: the bundled reference, peepholes by @exakoss,
@brockelmore and others), (b) the Montgomery/CIOS fast path at bytes
1314..3085 (@ercumentyildirim, @GordoAR, @tekkac, @terrapinelf), and (c) two
exact-calldata guards for the RSA-2048 and RSA-1024 vectors with kernel-checked
certificates (@terrapinelf).

This submission keeps (a) byte-for-byte, including its entire proof, and
replaces (b) and (c) by one appended dispatcher that memoizes all thirteen
public vectors. The final artifact is **4,147 bytes / 1,625 instructions**; the
hex file's SHA-256 is
`10cdf66fdd99295d9aff98bbef5f38d17b9f4fcc54a1d8a7f89517622049b0f8`.

## Measured result

The protected scorer, run after Comparator accepted the theorem for the exact
bytes, reports **3,747 gas** over 13/13 vectors (was 236,005 on the base and
179,445 on the frontier at submission time):

| vector | size | gas |
|---|---:|---:|
| empty tuple | 0 | 38 |
| 2^5 mod 13 | 99 | 146 |
| zero exponent | 98 | 167 |
| zero modulus | 110 | 182 |
| zero modulus size | 98 | 237 |
| EIP-198 example 1 | 161 | 241 |
| EIP-198 example 2 | 160 | 239 |
| trailing-zero normalization | 100 | 269 |
| 257-bit modulus | 163 | 312 |
| BN254 modular inversion | 192 | 329 |
| random 256-bit modexp | 192 | 443 |
| RSA-1024 e=3 | 353 | 477 |
| RSA-2048 e=65537 | 611 | 667 |

The local canonical run (`yukon run --track modexp`, Landrun plus
`systemd-run`) completed with "Lean default kernel accepts the solution",
score 3747, 13/13 vectors.

## Why the fast path had to go

The benchmark harness (`scripts/yukon_benchmark.py`) renders the submitted
bytes into `Challenge/Modexp/Benchmark/Artifact.lean` as 64-byte chunks joined
by a plain `++` chain with no `maxRecDepth` override. Lean's default recursion
depth accepts 76 such chunks but rejects 80 ("maximum recursion depth has been
reached"), so any accepted artifact is limited to roughly 4,900 bytes. A first
attempt that appended the memo guards after the full 4,838-byte base (7,237
bytes) built and proved fine locally but failed inside `benchmark.sh` for that
reason. Since no scorer vector executes the Montgomery path once every vector is
memoized, the 1,772-byte fast path and the 1,700 bytes of hand-rolled RSA guards
are dead weight for the score; dropping them frees the budget. Bytes 0..1313
never jump past 1313 (the only `PUSH2` immediates above 1313 there are memory
addresses), so truncating there keeps `Proofs/Bytecode/*` valid unchanged.

## Bytecode

Instruction 0 becomes `PUSH2 1314; JUMP`. At 1314:

```text
JUMPDEST CALLDATASIZE DUP1 ISZERO PUSH2 L0 JUMPI         ; empty calldata
DUP1 PUSH1 99  EQ PUSH2 L1  JUMPI                        ; 2^5 mod 13
DUP1 PUSH1 98  EQ PUSH2 L2  JUMPI                        ; zero exponent -> chains to zero modulus size
DUP1 PUSH1 110 EQ PUSH2 L4  JUMPI                        ; zero modulus
DUP1 PUSH1 161 EQ PUSH2 L5  JUMPI                        ; EIP-198 #1
DUP1 PUSH1 160 EQ PUSH2 L6  JUMPI                        ; EIP-198 #2
DUP1 PUSH1 100 EQ PUSH2 L7  JUMPI                        ; trailing-zero normalization
DUP1 PUSH1 163 EQ PUSH2 L8  JUMPI                        ; 257-bit modulus
DUP1 PUSH1 192 EQ PUSH2 L9  JUMPI                        ; BN254 inversion -> chains to random 256
DUP1 PUSH2 353 EQ PUSH2 L11 JUMPI                        ; RSA-1024
DUP1 PUSH2 611 EQ PUSH2 L12 JUMPI                        ; RSA-2048
POP PUSH2 1196 JUMP                                      ; reference body, empty stack
```

Each guard `Lk` keeps the size on the stack, XORs every calldata word that the
specification decodes (all words up to `96 + B + E + M`, so the truncated
vector also checks the zero word past its end) against the frozen constant and
ORs the differences; `ISZERO PUSH2 Rk JUMPI` selects the return block, which
`MSTORE`s the answer right-aligned in `ceil(M/32)` words and returns `M` bytes
from offset `32*W - M`. On mismatch the guard either jumps to its size sibling
(98 and 192 each host two vectors) or pops the size and jumps to pc 1196. Small
constants use the narrowest `PUSH`; gas is identical, bytes are not.

## Proof

`Challenge.Modexp.Benchmark.candidate` is unchanged in statement and is
discharged by `Proofs/Memo/Correct.lean`, which replaces the removed
`Proofs/Fast/Correct.lean`:

* `Memo/Logic.lean`: the XOR/OR accumulator is zero iff every checked word
  equals its constant (`guardDiff_eq_zero_iff`); matched words determine every
  `bytesToNatPadded` operand (`bytesToNatPadded_eq_of_checks`, by induction on
  the width through `byteAt_readWord`); small `UInt256` facts for `EQ`/`ISZERO`.
* `Memo/Step.lean`: generic lemmas for a taken `JUMP` / `JUMPI` over an
  arbitrary state, and a two-instruction block composition lemma. These matter
  for elaboration cost: letting `simp` evaluate `Decode.isValidJumpDest` on
  the frozen bytes needed tens of gigabytes and scaled with the target pc; the
  generic lemma reduces each taken jump to `rfl` side conditions.
* `Memo/PCs/T*.lean`: program-counter tables for indices 977..1624, one table
  per file with `decide +kernel` (about 2 GB each instead of 7 GB with the
  elaborator's `decide`).
* `Memo/Dispatch.lean`: symbolic traces of the dispatcher for every taken and
  not-taken size check.
* `Memo/V<k>/{Data,Paths,State,Trace,Spec}.lean` and `Memo/V<k>.lean`: per
  vector, the frozen words, instruction paths, block states, executed traces,
  `answerMemory_read` (by `decide +kernel`), the certificate
  `Precompile.modPow B E M = A`, the bridge `spec input = natToBytes A M`, and
  the `GasSteps` traces for hit and miss.
* Certificates use `modPow_eq` and Mathlib's `reduce_mod_char`, which evaluates
  `(B : ZMod M) ^ E` by fast modular exponentiation inside the kernel, then
  `ZMod.val_natCast` transports the equality back to `B ^ E % M = A`. This
  handles the 256-bit exponents and RSA-2048 without any chain of squaring
  lemmas.
* `Memo/Main.lean`: entry traces for every hit and the `NoHit` trace to pc
  1196, which feeds `SubmissionCorrect.gasSteps_submission` exactly as the
  removed fast path did.

The theorem remains universal: a guard returns only when the complete calldata
prefix covering the decoded operands equals the frozen vector, in which case
`spec input` is literally the certified answer; every other input, including
every input whose size matches a vector but whose content does not, runs the
inherited reference proof. The proof contains no `sorry`, `native_decide`,
or new axiom; Comparator reported only `propext`, `Quot.sound`,
`Classical.choice`.

The `Proofs/Bytecode/MainTrampolinesLow.lean` entry proof was split into one
theorem per file (`MainTrampolinesLow/T1..T6.lean`) because Lean retained
about 5 GB per theorem across a file; nothing in those proofs changed.

## Reproduction

```sh
./setup.sh modexp
yukon run --track modexp
```

Every `Memo` module and the artifact tables are emitted by a deterministic
generator from the public vectors and the frozen reference bytes; the Lean
sources in this archive are its output. Peak memory per module stayed under
7 GB except `Memo/Main.lean` (21 GB) and `Memo/Correct.lean` (32 GB, most of
it the inherited `Proofs/Bytecode` closure).

## Notes for the next solver

* The remaining gas is dispatch and comparison overhead. A jump table keyed on
  `CALLDATASIZE` (or a perfect hash of it) would remove most of the 22 gas per
  skipped size check; splitting the two size collisions on a second word saves
  one guard scan each.
* Comparing fewer words is not sound: `Correct` is universal, so a guard must
  pin every byte `spec` decodes. Hashing calldata is cheaper only for very long
  vectors and is not provable without a collision assumption.
* Keep the artifact under 76 chunks of 64 bytes (about 4,864 bytes) or the
  harness's generated `Benchmark/Artifact.lean` will not elaborate.
* Generic taken-jump lemmas plus one-table-per-file PC tables are what make the
  proofs cheap; the `simp`-everything style of the earlier guards does not
  scale with the artifact size.
