# Release tools

Scripts and data that the release gate uses. None of them is called by
`Scc/Test/certify.sh`, and none is part of what a certificate trusts. They decide
what gets checked and reviewed, so changes to them still need review.

| File | What it is | How the release gate uses it |
|------|------------|------------------------------|
| `quick_gate.sh` | Runs an incremental build under memory caps, then the cheap check groups in parallel. These are `run.sh` on both ISAs, sorry set, trusted files, regen `--check`, drift, `blocks.sh --check`, `textalign.sh`, `elf.sh` (relink and raw checks), the assembler tests, and `diff_place.sh` per ISA. Optional external hooks cover audit, segment reach, freeze and guard. | It is the first gate pass on a candidate, and is rerun after each fix. The full release gate adds cold timed builds and `certify.sh`/`certify_test.sh`. |
| `diff_place.sh` | Pins the PlaceOK outcomes of the differential test (wide and narrow samples) for each ISA. | `quick_gate.sh` runs one group per ISA, each under `timeout $DPLACE_TIMEOUT` (default 7200 s). It runs after `diff.sh` for the same ISA, because both use `.lake/scc-diff/<ISA>/`. |
| `memory_caps.tsv` | The measured peak RssAnon of each module above 2.5 GiB, with its cap and build mode (`parallel`, `solo`, `cert`). | `memwatch.py` enforces the caps. `quick_gate.sh` builds the `solo` and `cert` rows alone before the main build. Update a row when a module outgrows its cap; the gate stops when a module is killed twice. |
| `memwatch.py` | The per-process RssAnon watch for one checkout's `lean` processes. It can kill a process above its cap, and records peaks and concurrency. | Kills over-cap processes during the builds; during the checks it only records. |
| `trusted_paths.md5` | The md5 of every file matched by the trusted filter at the last release. | It is the reference for `trusted_check.sh`. Regenerate it with `trusted_check.sh --write <release>` when a release is cut, and commit it with that release. |
| `trusted_check.sh` | Lists the trusted files at a revision that are added, removed or changed relative to `trusted_paths.md5`, with a per-directory summary. | `quick_gate.sh` runs it on `HEAD` in the static group. Every file it lists needs review before the release. |
| `closure.py` | Computes the import closure of Lean modules at a revision from their header `import`s only. `--changed A B` lists the closure files that differ between two revisions, and `--certify` uses the modules `certify.sh` builds as roots. | Supports carrying certify results from one candidate to the next. If `closure.py --certify --changed A B` lists nothing and the `scc` binaries are identical, the certify/certify_test results of A still hold for B. |

## Typical runs

```sh
tools/quick_gate.sh                                   # everything, defaults
SETUP_ONLY=1 tools/quick_gate.sh                      # print the plan and caps
BASE=<previous release> QG_GROUPS="static quick" tools/quick_gate.sh
tools/trusted_check.sh HEAD                           # trusted-file review list
tools/closure.py --certify --changed <old> <new>      # certify carry-over check
```
