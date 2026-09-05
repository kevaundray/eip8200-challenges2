# Yukon benchmark

This repository is one schema-v2 Yukon challenge with two independently
scored tracks on a shared branch:

| track | editable path | score |
| --- | --- | --- |
| `modexp` | `Challenge/Modexp/Submission` | normalized gas over 48 ranked vectors |
| `ripemd160` | `Challenge/Ripemd160/Submission` | clean-state gas over 17 vectors |

Lower is better in every track. The editable paths are deliberately disjoint,
so Yukon can promote one track without replacing a sibling track's solution.

MODEXP checks all 61 vectors for correctness. Its ranked corpus has three
buckets: 32 256-bit cases, 10 RSA-1024 cases, and 6 RSA-2048 cases. The other
13 vectors are correctness checks only.

For each ranked vector, the parser divides candidate gas by the Osaka
precompile gas. It scales this ratio by 1,000 and uses integer arithmetic.
It averages the ratios in each bucket. The final score is the average of the
three bucket scores. Thus, each operand-size bucket has equal weight when its
absolute gas and vector count differ.

## Selecting a track

`yukon switch <track>` changes only the repository-local Yukon selection. It
does not change the Git branch, `HEAD`, index, or worktree. Run
`yukon tracks` to see the current selection.

Record meaningful progress with `yukon notes add`: baselines, hypotheses,
experiments, failures, design changes, and blockers are useful to later
solvers. Notes are public; remove secrets, private paths, personal data, and
credentials before uploading them.

## Proof and scoring boundary

Each track accepts an editable `bytecode.hex` and Lean `Solution.lean`.
`benchmark.sh` reads the hex once, copies it outside the editable surface, and
generates a trusted `ByteArray` literal. The trusted challenge and submitted
solution state the same `candidate` theorem for that literal.

Comparator checks the theorem type, permits only `propext`, `Quot.sound`, and
`Classical.choice`, and replays the proof with an independently built kernel.
Only after that succeeds does a protected, precompiled scorer execute the same
protected bytes and write the track's score JSON.

Comparator and its `lean4export` are pinned in `setup.sh`. Linux ranked runs
use Landrun plus a `systemd-run` address-family restriction. A functional,
non-security-bearing local run is available on macOS:

```sh
./setup.sh modexp
BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh modexp
```

Replace `modexp` with `ripemd160` for the other track. The two dispatch-only
workflows run the same shared implementation with a fixed track argument and
upload only that track's declared `scorePath`.

Setup elaborates the selected trusted proof closure in dependency order because
individual concrete-execution modules are memory intensive. Each Lake
invocation sees at most one stale module, and the package fixes Lean's own worker
count at one. The resulting Lake traces are reused by Comparator, so proof
checking is not repeated with a concurrent build later.
