# Read-Write Quorum Load under Known Crashes: Verification Artifact

When clients know which servers have crashed, they can choose among the surviving read and write quorums. The paper studies how often those choices must contact the busiest server. [Read the paper on Zenodo](https://doi.org/10.5281/zenodo.24428085)

Lean verifies the lower bounds, several exact constructions, and the asymptotic results. The Python scripts check finite certificates with exact arithmetic. The centered two-crash upper bound and the voting theorem also rely on written proofs.

## Repository layout

| Path | Contents |
| --- | --- |
| [`formal/GeneralCrashLower.lean`](formal/GeneralCrashLower.lean), [`formal/TwoCrashOptimal.lean`](formal/TwoCrashOptimal.lean) | The general lower bound, the lower bound for every two-crash size, and exact attainment by cyclic triples for n = 3k + 2. |
| [`formal/CircleSampling.lean`](formal/CircleSampling.lean), [`formal/GeneralFOptimal.lean`](formal/GeneralFOptimal.lean) | Weighted circle sampling and exact attainment for arbitrary crash budgets on the size sequence in the paper. |
| [`formal/MixedCircleAssembly.lean`](formal/MixedCircleAssembly.lean) | An exact optimum for equal read and write shares with fixed interval reads. The proof uses 124 finite certificates and a construction for larger sizes. |
| [`formal/PaperModel.lean`](formal/PaperModel.lean), [`formal/PaperClaims.lean`](formal/PaperClaims.lean), [`formal/FullRangeChecks.lean`](formal/FullRangeChecks.lean) | The common probability model and the formal statements for the known-failure and advance-contact results. |
| Root `*_verify.py` scripts and [`runs/`](runs/) | Certificate checkers and their inputs. The `source.py` files record the generators used to produce the certificates beside them. |
| [`paper/statement-correspondence.json`](paper/statement-correspondence.json) | The Lean declarations and written proofs that support each claim in the paper. |

## Requirements

- Lean **4.34.1** with Lake. The toolchain and Mathlib dependencies are pinned. [Toolchain](formal/lean-toolchain) · [Lake manifest](formal/lake-manifest.json)
- The Python commands were tested with **Python 3.14.4** and use only the standard library. Run them without `-O` and leave `PYTHONOPTIMIZE` unset so assertions run.

## Build the Lean proofs

Run from the repository root with the pinned Lean toolchain available.

```sh
python3 formal/build_balanced.py --roots \
  QuorumAudit TwoCrashFullControls TwoCrashBridge GeneralFControls \
  PaperModelControls FullRangeControls FullRangeChecks
```

The build prints `passed` for each module. The reported theorem dependencies use only `propext`, `Classical.choice`, and `Quot.sound`. Rebuilding all 211 modules took about 52 minutes on an Apple Silicon Mac with the pinned Mathlib dependencies already installed.

## Replay the certificates

```sh
verification_dir=$(mktemp -d)
python3 ap_gadget_verify.py runs/ap-gadgets-006/result.json --out "$verification_dir/bases"
python3 ap_strategy.py --nodes 35 --failed 0 17 --alpha 3/133 --out "$verification_dir/strategy"
python3 ap_strategy_verify.py "$verification_dir/strategy/result.json"
python3 two_crash_residues_verify.py --finite runs/two-crash-residues-002 --direct runs/two-crash-interval-direct-001 --out "$verification_dir/residues"
python3 two_crash_centered_sampling_verify.py --source runs/two-crash-centered-sampling-001 --out "$verification_dir/centered"
python3 general_f_interval_verify.py --source runs/general-f-interval-001 --out "$verification_dir/general-f"
python3 balanced_mixed_circle_all_verify.py runs/balanced-mixed-circle-all-001 --out "$verification_dir/balanced"
python3 full_range_frontier_verify.py --out "$verification_dir/full-range"
```

On success, each command exits with status 0. The strategy example reports load `13/133`. The certificate validators report `valid: true`, and the full-range replay reports `status: pass`. The full replay took about 2 minutes 40 seconds on an Apple Silicon Mac.

## AI assistance

This work used a human-directed, AI-assisted workflow. The Lean 4 kernel checks the formal proofs, which use no `sorry`. Separate Python scripts verify finite certificates using exact rational arithmetic.

## Citation and license

The repository is available under the [MIT License](LICENSE). Cite the code and the paper using [`CITATION.cff`](CITATION.cff).
