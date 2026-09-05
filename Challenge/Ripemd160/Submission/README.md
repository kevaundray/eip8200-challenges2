# RIPEMD-160 Yukon submission

This directory is the complete editable surface for the `ripemd160` track. A
submission must include:

- `bytecode.hex`: one line of lowercase EVM bytecode without a `0x` prefix;
- `Solution.lean`: `Challenge.Ripemd160.Benchmark.candidate`, proving
  `Challenge.Ripemd160.Correct bytecode` for the generated artifact.

Additional Lean modules may live here and be imported by `Solution.lean`.
Everything outside this directory is the protected specification, proof
support, evaluator, and workflow.

The lower-is-better score is clean-state gas summed over all 17 public vectors.
The same bytes must also return the correct result from the dirty state.
Executable vectors are a falsification check; Comparator must accept the
universal Lean proof before the protected scorer runs.

## Earlier direct-entry candidate

The initial `PUSH2; JUMP` now targets the existing main-body `JUMPDEST` at
`0x03ee` directly. This skips twelve compiler-generated
`JUMPDEST; PUSH2; JUMP` forwarding stubs while preserving the 1,671-byte code
length and every downstream program counter. The expected saving is 144 gas
per invocation, or 2,448 gas across the 17-vector score suite.

The candidate-specific proof under this directory changes the structural
artifact and entry execution trace to the direct jump. The downstream
RIPEMD-160 functional proof is unchanged, and its exact-gas bridge accounts
for the reduced entry cost.

## Stack-consuming helper candidate

This candidate starts from promoted submission
`943c3303-c540-44c3-8049-73aee90390f3`. It keeps that submission's Boolean
jump table and the direct entry jump. It consumes helper arguments directly
and uses the caller's zero result slot to remove stack cleanup work.

| Helper | Previous base gas | New base gas |
| --- | ---: | ---: |
| xAt | 37 | 30 |
| wordSet | 42 | 36 |
| xSet | 40 | 36 |
| tableAt | 57 | 48 |
| rotl | 54 | 45 |

Memory expansion is unchanged. The changes save 7,904 gas per padded block,
or 521,664 across the 66-block public suite. The native scorer reports
8,685,426 gas with all 17 clean and dirty vectors correct. The exact-bytecode
Lean proof is the acceptance condition, not the executable vectors alone.

Bytecode size remains 1,830 bytes. Each edited helper keeps its original
entry address, allocated byte length, and instruction count. Unreachable
STOP instructions after each return JUMP preserve later addresses and
instruction indexes. All caller-visible helper contracts remain unchanged.

## Prior candidate: unaligned table windows and hAt

That candidate added the table-window idea from submission
`80dacb5` by `ercumentyildirim`. The logical table bases remain unchanged.
Four calls push `base - 31`. The helper loads a word at `base - 31 + i`
and selects byte 31. It consumes its arguments and the zero result slot.
This reduces tableAt from 48 to 27 gas. The same argument-consumption
change reduces hAt from 37 to 30 gas.

The byte correspondence proof requires `31 ≤ base` and `i < 80`.
All four actual table bases meet that condition. Separate memory bounds
prove that the unaligned loads do not increase the memory high-water mark.
The public correctness theorem and its calldata domain are unchanged.

The native suite passes all 17 clean and dirty vectors at 8,241,311 gas.
The saving is 444,115 against the prior helper candidate and 1,618,387
against the original baseline. Its closed gas formula is
`3698 + 123852 * B + 3 * C + memCost(65 + 2 * B)`, where
`B = (inputSize + 72) / 64` and `C = (inputSize + 31) / 32`.
The full exact-bytecode Comparator remains the acceptance condition.

## Prior candidate: stack-consuming Boolean helpers

This candidate also consumes the Boolean case index and helper arguments.
Two selection arms use bitwise XOR identities proved for all UInt256
inputs. The per-bit proof uses only the permitted axiom set; the earlier
bv_decide probe is not part of this source.

Boolean case costs are [42,51,54,54,54]. The native score is 8,027,999,
with all seventeen clean and dirty cases passing. The formula is
`3698 + 120620 * B + 3 * C + memCost(65 + 2 * B)`.
The generic Boolean trace and complete execution/gas proof build have
passed. The independent exact-bytecode Comparator remains the acceptance
condition. Run all Yukon commands in the benchmark work directory printed
by the clone command.

## Prior candidate: direct stack-resident rounds (H10)

H10 retains the message schedule and replaces the compressor with two fully
unrolled 80-round lanes. Five working words stay on the EVM stack through each
lane. The right lane runs above the saved left result. Round templates use
immediate message-slot addresses, constants, and rotations, with inline Boolean
operations and 32-bit rotation. The three old working-state memory copies and
the round helper calls are no longer on the active compression path.

The exact artifact is 12,906 bytes. Native tests report 1,743,479 gas over all
17 clean vectors. All 17 dirty vectors also pass with the same gas total.
The measured formula is `3698 + 25400 * B + 3 * C + memCost(65 + 2 * B)`.
It is not a separate proved gas schedule. H09, the prior immediate-wrapper
candidate, passed local Comparator at 6,181,847 gas and 5,133 bytes.

The proof uses 42 instruction-aligned assembly chunks, five generic round
traces, and exact indexed certificates for all 160 sites. The scheduled words
match the pinned RIPEMD-160 message schedule. Both complete lane traces use
actual machine states with unchanged memory and active-word count. The final
61-instruction tail stores the five combined hash words in the exact program
order. `StackCorrect` connects these components to the outer block model and
the unchanged public Correct contract. `Solution.lean` is the benchmark entry.

Only the protected Comparator and scorer determine benchmark acceptance.
The final theorem must pass that check for the exact submitted bytecode.

## Prior candidate: compact shared stack rounds (H12)

H12 retains the stack-resident working words, schedule, and final combination.
It replaces H10's inline round bodies with 160 six-instruction wrappers and
ten shared helpers. Each wrapper supplies a return PC, rotation, message-slot
address, and helper PC. Each helper embeds its group constant. Both the helper
return JUMP and the wrapper's return JUMPDEST are executed and proved.

The exact artifact is 4,796 bytes and 2,583 instructions. The native suite
reports 2,292,599 gas over all 17 clean vectors. All 17 dirty vectors pass with
the same individual gas results. The measured formula is
`3698 + 33720 * B + 3 * C + memCost(65 + 2 * B)`.
This is a native measurement, not a separate proved gas schedule.

H09 was promoted at 6,181,847 gas. H10 failed before proof replay because the
protected generated-byte module exceeded its recursion limit. H12's smaller
byte array passes that isolated generator check without a harness change.

The proof uses 13 instruction-aligned assembly chunks, five generic helper
traces, exact call/helper/return locations, bounded 80-round lane composition,
and the final storage tail with its nonempty helper suffix. StackCorrect and
Solution retain the exact universal Correct contract. Acceptance still
requires the full protected Comparator and scorer.

## Prior candidate: compact rotation and return sequence (H14)

H14 keeps H12's shared helper design and changes only the common stack
permutations. It consumes the C input directly during its ten-bit rotation.
It also consumes the sum and rotation inputs directly when it computes T.
All masks, arithmetic, memory accesses, and call/return steps remain.

The artifact is 4,726 bytes and 2,513 instructions. The native suite reports
2,113,079 gas for all 17 clean vectors. All 17 dirty vectors pass with equal
paired gas. This saves 179,520 per frame suite, or 2,720 per compression block,
against H12. The measured formula is
`3698 + 31000 * B + 3 * C + memCost(65 + 2 * B)`.
It is not a separate proved gas schedule.

The five before-JUMP templates have lengths 44, 48, 49, 48, and 49.
The wrappers and final storage tail keep their previous positions. Each
helper has seven fewer instructions and bytes. All ten helper addresses,
160 wrapper targets, and the tail's 486-instruction suffix are updated.
The unchanged public Correct contract and protected Comparator remain the
acceptance conditions for these exact bytes.

## H16: merged permutations and deferred Boolean masks

H16 includes H15's merged T/C permutation, which removes two SWAPs per
helper. It also removes the early Boolean-result mask from groups 2 and 4.
The later sum mask, T mask, and C mask remain. The ordinary-kernel identity
`mask32 (K + (A + (X + F))) = mask32 (K + (A + (X + mask32 F)))`
justifies the change for all UInt256 inputs, including arithmetic wrap.
The equality applies after the sum mask; unmasked sums need not be equal.

The native suite reports 2,024,375 gas for each frame. All 17 clean and 17
dirty vectors pass with equal paired gas. The artifact is 4,682 bytes and
2,485 instructions. H16 saves 25,344 gas against H15, or 384 per block.
The measured formula is
`3698 + 29656 * B + 3 * C + memCost(65 + 2 * B)`.
This is not a separate proved gas schedule.

The five before-JUMP template lengths are 42, 46, 45, 46, and 45. All ten
helper PCs, 160 wrapper targets, and the tail's 458-instruction suffix match
the new artifact. The public Correct contract is unchanged. Protected
Comparator acceptance is still required for the exact submitted bytes.

## Prior candidate: reordered helper parameters (H18)

H18 pushes the rotation before the return PC. The helper entry is
`[xAddress, returnPC, rotation, A, B, C, D, E] ++ rest`.
After the sum mask, `SWAP3; POP; SWAP2` reaches the same state that H16
reached with one more `SWAP1`. All later operations and masks stay fixed.
The change applies to all ten helpers and all 160 wrappers.

The native suite reports 1,992,695 gas per frame suite. All 17 clean and
17 dirty vectors pass with equal paired gas. The artifact has 4,672 bytes
and 2,475 instructions. The saving against H16 is 480 per compression
block, or 31,680 per suite. The measured formula is
`3698 + 29176 * B + 3 * C + memCost(65 + 2 * B)`.
This is not a separate proved gas schedule.

The five before-JUMP lengths are 41, 45, 44, 45, and 44 instructions.
Wrapper lengths stay at 13 bytes and six instructions. The second PUSH
starts at wrapper PC + 2; the return stays at PC + 12. The tail has a
448-instruction suffix. The universal Correct contract is unchanged.

## Prior candidate: consume A in the shared sum (H20)

H20 consumes A instead of copying it and later discarding it. After the
Boolean and X addition, the stack is `[s, ret, r, A, B, C, D, E] ++ rest`.
`SWAP1; SWAP3; ADD` gives `[A+s, r, ret, B, C, D, E] ++ rest`.
The unchanged group constant and sum mask then produce H18's exact
pre-rotation stack. All later T/C operations, three masks, memory accesses,
and return semantics stay fixed. Full-width working inputs remain valid.

Each helper is two bytes and two instructions shorter and costs five less
gas. The exact artifact has 4,652 bytes and 2,455 instructions; the helper
block has 610 bytes. The five before-JUMP lengths are 39, 43, 42, 43, and 42.
All 160 wrapper targets are correct; 144 changed. Their lengths and return PCs are fixed.
The final tail has a 428-instruction suffix.

The native suite reports 1,939,895 gas, with all 17 clean and 17 dirty cases
correct and equal paired gas. The reduction from H18 is 800 per block or
52,800 per suite. The measured formula is
`3698 + 28376 * B + 3 * C + memCost(65 + 2 * B)`.
This is measured gas, not a separate proved gas schedule. The universal
Correct contract and protected acceptance checks are unchanged.

## Prior candidate: consume A with the packed schedule (H21)

H21 combines the H20 round helpers with the same 528-byte ascending packed
schedule used in H19. The schedule PUSH2 at PC `0x72b` now targets `0x122c`.
Only its two immediate bytes change in the 4,652-byte H20 prefix. The new
helper starts at instruction 2455. Its final JUMP is instruction 2614 at
PC `0x143b`. The full candidate has 5,180 bytes and 2,615 instructions.
The unchanged final combination tail has a 588-instruction suffix.

The helper reads +60 decimal, +0, and +32 before all 16 ascending X stores.
Two byte-swap stages per input word produce the little-endian values.
The warm-up preserves the old active-word count. Separate raw, byte-order,
full-memory, active-word, state, and located-step proofs connect the helper
to the old scheduled-state model. The frame uses CalldataFits and a valid
block index, with one return JUMPDEST. The public Correct contract is fixed.

Native tests report 1,730,279 gas with all 17 clean and 17 dirty cases
correct and equal paired gas. This saves 209,616 gas from H20 and 52,800
from H19 per suite. Native gas is not an official server score.

## Current candidate: bounded RotationFold with the packed schedule (H22c-packed)

H22c-packed is the current native candidate. It combines two bounded helper
folds with the unchanged 528-byte ascending packed schedule helper. The native
measurement is 5,150 bytes, 2,585 instructions, and 1,635,239 gas per frame.
The result is 95,040 gas lower than the H21 native measurement. Native gas is
not an official server score. The measured formula is
`3698 + 23760 * B + 3 * C + memCost(65 + 2 * B)`, where
`B = (inputSize + 72) / 64` and `C = (inputSize + 31) / 32`.

The C fold replaces:

```text
DUP1 PUSH1 10 SHL SWAP1 PUSH1 22 SHR OR PUSH4 0xffffffff AND
DUP1 PUSH1 32 SHL OR PUSH1 22 SHR PUSH4 0xffffffff AND
```

The C input remains a full-width UInt256 value until the preserved
`PUSH4 0xffffffff; AND`. The replacement uses bitwise OR. It does not use the
invalid multiplication shortcut `C * (2^32 + 1)` for arbitrary C.

The T fold replaces:

```text
DUP1 DUP3 SHL SWAP2 PUSH1 32 SUB SHR OR
DUP1 PUSH1 32 SHL OR SWAP1 SHR
```

The sum `q` is already masked to 32 bits. Every wrapper uses the complement
rotation payload `32-r` exactly once for this fold. The new stack prefix is
`[q, 32-r, ret, ...]`. The raw result is
`((q << 32) OR q) >> (32-r)`. At `r=0` the raw result is `q`; at `r=32` it is
`(q << 32) OR q`. The later addition and 32-bit mask preserve the required
round result at both endpoints.

All three 32-bit masks remain. All five groups, both constant tables, all
working-lane order, return behavior, suffix behavior, and the final
combination tail remain fixed. The 160 wrappers remain 13 bytes and six
instructions. Their return PC remains wrapper PC plus 12. The H22c prefix has
4,622 bytes and 2,425 instructions. The appended schedule helper starts at
PC `0x120e`, instruction index 2,425, and its final JUMP is at PC `0x141d`,
instruction index 2,584. The packed tail suffix is 558 instructions.

Native testing passed 12/12 tests. Main independently reran all twelve tests.
Each of the four trusted native scorer processes passed 34 rows: 17 clean and
17 dirty. All rows were correct, and every clean/dirty pair had equal gas.

The generic proof build passed 1,020 jobs, and the fresh seven-theorem
`H22RawAudit` passed with only the three allowed axioms. The exact Artifact
build, fresh Artifact audit, and independent source review also passed.
The complete `StackCorrect.correct` build passed 1,091 jobs. Fresh Correct,
Site, and Raw audits also passed with only the allowed axioms. The local
Comparator accepted H22. The server promoted its exact artifact at
1,635,239 gas. Each later candidate requires its own protected checks.

## H27: full-width paired rounds and the exact C-fold

H27 is the current locally verified candidate after H25. The native
measurement is from the trusted binary on macOS, not the ranked server.
The public files are `Challenge/Ripemd160/Submission/bytecode.hex`
and `Challenge/Ripemd160/Submission/Proofs/Bytecode/StackCorrect.lean`.

| candidate | status | gas | bytes | instructions |
| --- | --- | ---: | ---: | ---: |
| H24 `c6ac2fcc` | promoted | 1,429,319 | 5,020 | 2,593 |
| H25 `044d5a48` | promoted | 1,387,079 | 5,060 | 2,553 |
| H26 | dominated; not submitted | 1,323,719 | 4,940 | 2,513 |
| H27 | local native candidate | 1,281,479 | 4,980 | 2,473 |

H25 source SHA-1 is `576dbe880abd933fe853367e0434f42b99879410`. H27 saves
105,600 gas versus H25 and 147,840 versus H24, at 1,600 gas per 512-bit
block. H26 removed a mask; H27 also changes the C-fold.

The C-fold changes from `DUP1 PUSH1 32 SHL OR PUSH1 22 SHR` to
`PUSH5 0x100000001 MUL PUSH1 22 SHR`. The exact pure raw operation is
`((UInt256.ofNat 0x100000001).mul C).shiftRight (UInt256.ofNat 22)`.
The exact raw evaluator theorem preserves all five full-256-bit output words,
equal to two pure raw rounds, and preserves full memory. It proves ordered
`activeWords` for the two MLOADs; the production `activeWords ≥ 67` bound
makes the count unchanged.

The generic raw premises include a running state, `rest.length < 1012`,
`r0 ≤ 32`, `r1 ≤ 32`, f0 constant `0`, and the memory, stack, and suffix conditions.
Each helper executes two rounds; the lane composes 40 pair calls. The generic
rotation proof is universal for rotations at most 32. Only semantic
`WorkingRepresents` identifies canonical 32-bit B/C with `embeddedUInt32` and
uses low A/D/E; the generic raw theorem remains full width. The bound
`C < 2^32` is used only for that semantic bridge. At `C = 2^32 + 1`, MUL
gives low result 2,048 and the old OR gives 1,024.

The packed bytecode uses 64-byte chunks: 4,980 bytes require 78 chunks. The
nonpacked main uses 70 chunks. The exact Lean Artifact has 14 instruction
chunks: 12×200, 73, and empty. Its ASCII hex SHA-256 is
`3f9a9f23df70cf8ec172e2840caf20e86ea415047224fcd97b996e9152519a08`; its
decoded-byte SHA-256 is
`ec8d3612bcf4240063117b7176d36bcac57fd1f11be37d718a076b50cb1cb9c0`.

The trusted scorer has 34 rows: 17 clean and 17 dirty, all PASS with equal
clean/dirty gas. The 1,281,479 score is the total for the 17 clean rows. A
separate native test oracle ran 21,780 cases across H26 and H27 in seven tests:
2 variants × 10 helpers × 33 × 33 rotations. All seven tests passed. Empty
costs 22,307 gas; 1,000 bytes cost 298,503 gas.

Main reports proper `StackCorrect.correct` 1,087 PASS and fresh
`H27CorrectAudit` PASS with only the three allowed axioms. Negative proper
1,020 plus fresh 2, Lane fresh 5, Sites fresh 10, Endpoint/Seams proper 1,077,
and outer fresh 7 all PASS. The independent review and fresh 26-check full
audit also passed. Local H27 Comparator and server validation are pending.

The actual f0 change is q1 XOR/add grouping and C-fold MUL. Negative failures
were a missing fold-to-two-shift equality, f2 fixed by
`hsecondRotC'.trans hT1_sem.symm`, and an f4 broad `simp` hitting the
4-million heartbeat limit after 84 seconds. The final direct fix was
`raw_rotate_target.trans hT1_sem.symm`. Premises and limits did not change.

Reproduce from a public checkout with:

```text
./.benchmark-tools/trusted/ripemd160challenge --hex=Challenge/Ripemd160/Submission/bytecode.hex --csv
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
```

Root audits and generator logs are ignored and are not uploaded. H23 dense
packing and the H28 cache are research only; H28 had worse gas. Credit public
terrapinelf ScratchLow/StackCompression PR 69, commit
`6e97b9236cdf63c69e9e558828eee92ea3146ec9`, and ercumentyildirim for the
inherited compiler/proof base. GPT 5.6 Sol coordinated verification; GPT 5.6
Luna at maximum effort prepared the text. Local Comparator and server status
remain pending; submission is the next step after final review.

## H23: dense active-word schedule

This appendix records the later H23 dense-schedule candidate. It does not
rewrite the H22, H25, or H27 history above. H23 starts from the frozen H27
source base (SHA-1 `e6291c72ffce96b8fde9b1919ab0dce7186f8986`) and leaves the
H27 paired-round helper code unchanged.

The change is a schedule-memory reduction. There are 80 pair wrappers. Each
wrapper has two schedule-word indices `j0,j1` in `0..15`. Its load offsets
are `p0 = 644 + 4*j0` and `p1 = 644 + 4*j1`. These indices are not wrapper numbers. The packed helper keeps its warmup
and endian stages, and keeps every source read before the replacement writes.
It has two endian passes of 22 opcodes each, each split into 11+11 with the
unchanged 8-bit and 16-bit masks. The old sixteen slot stores become two
whole-word stores at offsets `672` and `704`. The low32 load equality is
`DenseScheduleMemory`; `DenseScheduleWord` preserves exact full raw outputs
under low32-equal inputs. High bits in the original message words may remain
in memory. The active-word value is `max(initialActive, 67 + 2*i)`; the stores
are below this bound and preserve the full active state. The suffix limit is
counted in UInt256 words, not bytes.

The measured native outputs are:

| candidate | bytes | opcodes | chunks | packed gas |
| --- | ---: | ---: | ---: | ---: |
| H23 dense nonpacked | 4,452 | 2,313 | 70 | — |
| H23 dense packed | 4,784 | 2,375 | 75 | 1,262,075 |
| H27 local packed baseline | 4,980 | 2,473 | 78 | 1,281,479 |

The packed helper is 332 bytes, 62 opcodes, and 188 gas. The trusted scorer
passed all 34 paired rows, with clean and dirty totals equal. The empty input
case used 22,013 gas; the 1,000-byte case used 293,799 gas. Against the H27
local baseline of 1,281,479 gas, the 66-block comparison suite shows a
reduction of 19,404 gas. `19,404 / 66 = 294` gas per block exactly. These are
local native-candidate measurements, not H23 server results.

Five native unit tests passed in 0.243 seconds. Exact Artifact proper ran
1,010 jobs and passed; Artifact took 156 seconds and Data took 2.4 seconds as
distinct modules. Dense Template/Trace/Word proper ran 1,018 jobs and passed,
with fresh 6+3 audits. The active-word writer passed.

The verified H23 gate updates are Main DenseMemory proper 1,013 PASS in
10 seconds with fresh 5 PASS (source prefix `e7249eef…`), DenseActive proper
1,024 PASS with fresh 3 PASS, DenseSite proper 1,027 PASS with fresh 10 PASS,
PairLeft 297 seconds and PairRight 365 seconds in parallel PASS, and PairLane
proper 1,045 PASS with Certificate 2.8 seconds, Lane 1 second, and fresh 5
PASS. BlockModel proper 1,052 passed in 2.1 seconds; Frame proper 1,063 passed
in 22 seconds; Endpoint proper 1,067 passed in 1.2 seconds. LoadSeams passed
in 1.2 seconds. Full StackCorrect proper 1,086 passed in 2.2 seconds. A fresh
31-declaration axiom audit passed with only the three allowed axioms.
H23 local Comparator and server validation remain pending at preparation;
no H23 server result is claimed.

Curie independently passed fresh Memory, Active, Site, and Lane audits with
5, 3, 10, and 5 PASS. This is an audit result, not a review of this note.

The prior H27 local Comparator accepted 1,281,479. H27 server CI run
`33869171263` succeeded in 19 minutes 26 seconds, and Yukon now reports
1,281,479 as the current best, promoted from source
`e6291c72ffce96b8fde9b1919ab0dce7186f8986`.

For a public checkout, use:

```text
./.benchmark-tools/trusted/ripemd160challenge --hex=Challenge/Ripemd160/Submission/bytecode.hex --csv
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
```

The generated Artifact is required before evaluating `Solution.lean`. The
macOS local diagnostic uses `BENCHMARK_INSECURE_LOCAL=1 yukon run --track ripemd160`.
The protected server remains the authority for acceptance and recorded score.

The selected theorem remains `StackCorrect.correct : Correct submissionBytecode`
for every input allowed by `CalldataFits`. Internal pointer bounds come from
the existing input and block bounds. A small memory-update wrapper and generic
projection lemmas fixed proof-normalization timeouts without changing states,
bytecode, assumptions, or proof limits.

Credit goes to @ercumentyildirim and @terrapinelf for the inherited compiler,
proof, and low32 foundations, including terrapinelf PR 69. Final H23 status
belongs to the later integration and gate review.

## H31b: direct output on the frozen H23 packed base

H31b has passed the full `Correct` proof build and a fresh axiom audit.
The original benchmark directory also passed `StackCorrect` and `Solution`.
The local macOS export/Comparator run is active at the time of this record.
Local Comparator and server acceptance are not yet claimed. The candidate is the
H23 dense packed base plus the H31b output helper. It is not the separate
H30b-combined candidate.

### Exact candidate and score

H31b starts from the frozen H23 dense packed bytecode. The base is 4,784 bytes
and 2,375 instructions. H31b appends the exact 186-byte, 50-instruction
primary output helper. The resulting bytecode is 4,970 bytes and 2,425
instructions.

| candidate | base | bytes | instructions | clean gas | dirty gas | result |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| H23 dense packed | H23 | 4,784 | 2,375 | 1,262,075 | 1,262,075 | 34-row base PASS |
| H31b direct output | H23 dense packed | 4,970 | 2,425 | 1,220,289 | 1,220,289 | 34-row native PASS |

The trusted native run has 34 passing rows: 17 clean rows and 17 dirty rows.
The reported score is the clean 17-row sum, `1,220,289`. The dirty rows are a
separate correctness and memory-state check and are not added to that score.
The H31b saving against H23 is `41,786 = 2,458 × 17`. It is not a clean-plus-
dirty double count.

The H23 local Comparator and server run `33874014497` passed. Yukon promoted
`4fe6451d-dabd-46b1-b982-66acf37edc71` at 1,262,075 from source `9fcca978`.
This is the verified current frontier. Those facts do not make H31b accepted.

### Prefix patch and exact layout

The decoded prefix instruction at index 775 has PC `0x633` and is
`PUSH2 0x64e`. H31b changes only the two original immediate bytes at byte
indices `0x634` and `0x635`, changing the target to `0x12b0`. The old six-byte
driver prelude at `[0x64e, 0x654)` is preserved byte-for-byte as
`5b505f5f525f`. All other prefix bytes, instruction boundaries, and old
instruction indices remain unchanged.

The appended helper starts at PC `0x12b0`, instruction index 2,375, and ends
at PC `0x1369`, instruction index 2,424. Its final four bytes are
`60205ff3`, which are `PUSH1 32; PUSH0; RETURN`. The H23 dense packed segment
still occupies instruction indices 2,313 through 2,374. The unchanged main
tail suffix contains 718 instructions. The actual output suffix is exactly
the new 50-instruction helper. These fixed boundaries are used by the
artifact import and extraction logic. They avoid treating an old H23 output
path as the H31b output path.

The H23 base identities are:

```text
ASCII hex SHA-256: 2c1151282e43abc6b8636e60fb7353c1c666a958785b38e9af64c1580d16679d
decoded bytes SHA-256: f196b33a6dd4a4edcd406a136712c0d1cf12a0289ef31c323a08264e2c7aac50
```

The H31b identities are:

```text
bytecode.hex SHA-256: 8a1b5a0ad70db1b1243f118cfe02b99c361159720a31617ac2bfb9c11fa2162f
decoded bytes SHA-256: 55ffc569b7c60cbb748cb265ad947696d08417a12be45c3b24446c582f4e4a20
layout JSON SHA-256: 572ecfbb5ce5a817fbb7bd3e09e05571a626d452d80da6d65379fdd035c179c0
helper raw SHA-256: 8d6d6855642748a68aee9da119ce239c14fbd5d57fb4199a3c58bc4d7031c1a7
```

The branch generator reads the frozen H23 base and the frozen H31b helper
identity. It changes the branch operand only. It does not use the H30b base,
reapply the old B01 transform, or infer the helper from a stale output path.
The generated certificate chunks are 12 chunks of 200 instructions, one
chunk of 25 instructions, and one empty chunk. The native 64-byte chunk count
is 78.

### Helper operation

The helper receives five full-width words at memory addresses 32, 64, 96,
128, and 160. It reads them once, before the only write. It packs the words
with four `SHL 32; OR` steps, applies the byte-order stages, writes 32 bytes
at memory offset zero, and returns 32 bytes.

The two byte-order stages use the minimal immediate widths. The 8-bit stage
uses `PUSH31 mask8`; the 16-bit stage uses `PUSH30 mask16`. The helper has 143
static gas in the template calculation. Its final sequence is
`PUSH0 MSTORE PUSH1 32 PUSH0 RETURN`.

The direct branch saves 12 runtime gas per invocation compared with the
earlier H31 forwarding-stub variant. That variant overwrote the old six-byte
driver region with a forwarding sequence. H31b jumps directly to `0x12b0`, so
the 17-row saving is `12 × 17 = 204` gas. H31b has 2,425 instructions while
the stub variant had 2,423 because H31b preserves the old six-byte prelude;
the lower runtime gas comes from skipping the forwarding instructions.

### Formal boundary and proof status

The generic raw proof is in `FastOutputTemplate.lean` and
`FastOutputTrace.lean`. It proves a 49-operation state before `RETURN` and a
50-operation returned state. Its premises are a running state and
`rest.length < 1021`. Memory, stack words, suffix values, shared state, and
all UInt256 inputs are arbitrary. The proof records the PC, stack, memory,
active-word, halt, and return-state changes. `RETURN` consumes offset zero and
size 32, sets the returned state, and does not advance the PC.

The raw theorem has no canonical 32-bit premise. The canonical packing
specification is proved in a separate math layer. It is not used to justify
the raw execution. The raw-to-math bridge also fixes the
`OR` operand order: the EVM stack evaluator pops the operands in the reverse
of the displayed mathematical expression, and bitwise OR commutativity proves
the exact full-width equality. No low-word assumption is used for this step.

The following H31b component results are recorded:

| component | result |
| --- | --- |
| Artifact proper | PASS, 1,010 jobs, 160 seconds |
| fresh Artifact audit | PASS, 18 checks |
| Driver proof | PASS, 47 seconds |
| Schedule site | PASS, 3 seconds |
| Tail proof | PASS, 34 seconds |
| Pair-site left proof | PASS, 312 seconds |
| Pair-site right proof | PASS, 383 seconds |
| Interface | PASS, 1.6 seconds |
| Compression bridge | PASS, 1.1 seconds |
| shared formal build | PASS, 1,059 jobs; this is a job count, not a check count |
| canonical output math | PASS, proper 1,026-job build and four fresh axiom checks |
| full StackCorrect | PASS, proper 1,094-job build and fresh 13-theorem audit |
| original-directory proof | PASS, StackCorrect 1,094 jobs and fresh 13-theorem audit |
| original-directory Solution | PASS, 1,097 jobs, 18 seconds |

The generic output Main proper build passed with 1,017 jobs, and its fresh
two-theorem audit passed with explicit `-j1`. The actual output Site proper
build passed with 1,028 jobs and its fresh ten-check audit passed. Independent
review passed for both. Only the allowed foundational axioms are used.
The canonical theorem `PackedOutputMath.packedOutput_eq_prefix_emitDigest`
proves the exact 12-zero-byte prefix and 20 digest bytes for arbitrary five
UInt32 values. `PackedOutputDigits.extract` provides the packed digit proof.
`FastOutputResultBridge` combines the byte theorem, the existing compression
seam, and the actual full trace cost. The completed `Correct` theorem keeps
the original input and gas quantifiers. It has no extra output hypothesis.
`Solution` still exports `StackCorrect.correct`.

The selected 78-module submission closure excludes the old output execution
and result bridge. It uses only `propext`, `Classical.choice`, and `Quot.sound`.
No protected file, resource limit, or theorem contract changed. Local
Comparator and H31b server validation remain pending.

### Public source manifest

The relevant public source and reproduction files are:

```text
Challenge/Ripemd160/Submission/README.md
Challenge/Ripemd160/Submission/bytecode.hex
Challenge/Ripemd160/Submission/Bytes.lean
Challenge/Ripemd160/Submission/Bytecode.lean
Challenge/Ripemd160/Submission/Proofs/Bytecode/Artifact.lean
Challenge/Ripemd160/Submission/Proofs/Bytecode/FastOutputTemplate.lean
Challenge/Ripemd160/Submission/Proofs/Bytecode/FastOutputTrace.lean
Challenge/Ripemd160/Submission/Proofs/Bytecode/FastOutputSite.lean
Challenge/Ripemd160/Submission/Proofs/Bytecode/PackedOutputDigits.lean
Challenge/Ripemd160/Submission/Proofs/Bytecode/PackedOutputMath.lean
Challenge/Ripemd160/Submission/Proofs/Bytecode/FastOutputResultBridge.lean
Challenge/Ripemd160/Submission/Proofs/Bytecode/OutputModel.lean
Challenge/Ripemd160/Submission/Proofs/Bytecode/CompressionInterface.lean
Challenge/Ripemd160/Submission/Proofs/Bytecode/CompressionSeamBridge.lean
Challenge/Ripemd160/Submission/Proofs/Bytecode/DriverTrace.lean
Challenge/Ripemd160/Submission/Proofs/Bytecode/PackedScheduleSite.lean
Challenge/Ripemd160/Submission/Proofs/Bytecode/StackTailTrace.lean
Challenge/Ripemd160/Submission/Proofs/Bytecode/StackRunBridge.lean
Challenge/Ripemd160/Submission/Proofs/Bytecode/StackCorrect.lean
Challenge/Ripemd160/Submission/Solution.lean
```

These are relevant files, not a claim that every listed file changed. The
submission contains the exact bytes and their assembly certificates. Local
generators, native inputs, root audits, and logs are ignored working records,
not public source files. The commands below do not require those records.

### Reproduction commands

Run these commands from the benchmark work directory after obtaining this
candidate's public submission files. The exact bytecode is already included.

```sh
yukon setup --track ripemd160
sha256sum Challenge/Ripemd160/Submission/bytecode.hex
./.benchmark-tools/trusted/ripemd160challenge --hex=Challenge/Ripemd160/Submission/bytecode.hex --csv
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
BENCHMARK_INSECURE_LOCAL=1 yukon run --track ripemd160
```

Build the generic raw output and exact output site with the project targets:

```sh
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputTrace Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputSite
```

The protected scorer is the authority for the 34-row native check. The Yukon
run is the normal local macOS workflow. A local PASS does not replace the
formal proof or server validation.

### Known failure and future work

The only recorded initial native test failures were a missing
`SparseMemory.snapshot` method and use of `branch_instruction_index` before
the layout key was emitted. Both were test and layout bookkeeping errors and
were fixed. The final math proof also needed three explicit UInt8 zero-array
annotations and removal of one extra conditional rewrite. The corrected math
and complete proof builds passed without changing bytecode or the contract.

The separate H30b-combined native candidate measures 1,165,377 gas, but it is
unproved and unsubmitted. It is not the current H31b candidate and is not
combined with the H23-base score above. Future H30b/H31b work must keep its
native result separate from this H31b proof and score.

Main, using GPT 5.6 Sol, handled coordination, integration, final proof work,
and review. GPT 5.6 Luna at maximum effort prepared component proofs and the
initial note. GPT 5.6 Sol at high effort provided independent review.
The final CLI metadata is supplied outside the note body with the
exact underlying model `GPT 5.6 Sol`, harness `Codex`, and coauthors
`ercumentyildirim` and `terrapinelf`; the note does not duplicate canonical
metadata fields.

## H30b + H31b combined checkpoint

The native tests, component proofs, and full `Correct` build passed. Local
Comparator and server acceptance are still pending at this checkpoint.
This section describes the current 5,298-byte candidate. Earlier sections
are records of the separate candidates and do not describe its current PCs.

H31b was promoted at 1,220,289 gas as
`f7212717-583e-4839-a39e-d04c3989f862`, landed source
`4670b4ab52cf404c84db183e5f7d484b3e08b71f`.
The combined native candidate uses 1,165,377 gas: a further saving of 54,912.
All 17 clean and 17 dirty rows passed. The dirty sum equals the clean sum;
only the clean sum is the score. The unchanged 186-byte direct output helper
contributes the earlier H31b saving of 41,786 gas relative to H23.

The compression path uses 20 four-round calls per lane. Each call retains
`F = 2^32 + 1` below its five working words. The generic proof accepts arbitrary
UInt256 working words and an arbitrary ordered suffix of length less than
1007. The semantic bridge uses only the low 32 bits of overlapping dense
message reads. A SWAP5 preserves the left result below the right lane. The
62-instruction tail removes the factor and uses the existing hash-combination
result. The schedule and mathematical block model are unchanged.

Exact identity:

```text
bytecode.hex SHA-256:
2714189b259bd782517ba2f485bf6301cd8d709852c3dc20f9e28cbe97be346a
decoded bytecode SHA-256:
9c0271153f45c8d8c0c0a8b75145861ff11d6944b779300aa4cef3c785e9c7fe
bytes: 5298
instructions: 2864
```

The first left call is index997 at PC0x746. The route is index1237 at0x976.
The first right call is index1248 at0x986. The tail starts at index1488 at0xbb6.
The dense schedule starts at index2752 at0x12ac. Output starts at index2814
at0x13f8 and returns at index2863 at0x14b1. Code ends at0x14b2.

Proper builds and fresh audits passed for Artifact, QuadLayout, generic quad
execution, call/helper lifting, semantic four-round results, generic tail,
both concrete quad sites, the relocated output and schedule, the driver,
frame, route, and load connections. The lane build passed 1,054 jobs. The
actual tail build passed 1,025 jobs in 25 seconds; its fresh audit passed.
The full correctness build passed 1,104 jobs in two seconds. A fresh root
checked the exact contract, 5,298 bytes, 2,864 instructions, and 17 axiom
lists. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
No protected source or resource limit changed. The theorem preserves the
original `Correct submissionBytecode` contract for every fitting input and
all sufficient gas amounts.

Public reproduction uses only files in the editable submission and the
protected setup tools:

```sh
yukon setup --track ripemd160
shasum -a 256 Challenge/Ripemd160/Submission/bytecode.hex
./.benchmark-tools/trusted/ripemd160challenge --hex=Challenge/Ripemd160/Submission/bytecode.hex --csv
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
BENCHMARK_INSECURE_LOCAL=1 yukon run --track ripemd160
```

Local native output, fresh audit roots, generators, and the append-only
hypothesis log are ignored working records. They are not required public
inputs and are not in the submitted directory. Inlining, specialization, and
warm-up removal are separate tests; none of their proposed gains is included
in this candidate's score.
