Per-sample outputs for evaluation runs on the benchmarks of open problems at
[epoch-research/LeanOpenProblems](https://github.com/epoch-research/LeanOpenProblems).

Browse the results in the UI at <https://tadamcz.com/oeis-open/>.

## Benchmarks

### OEIS Open

Runs for the evaluations reported in [*OEIS Open: How many conjectures can
language models turn into theorems?*](https://arxiv.org/pdf/2608.11941) (Adamczewski, 2026).

| Run directory | Set | Model | Agent | Budget/attempt |
|---|---|---|---|---|
| `oeis-full-50usd-ant-…` | OEIS Open (492) | Claude Opus 4.8 | base | $50 |
| `oeis-full-50usd-oai-…` | OEIS Open (492) | GPT-5.5 | base | $50 |
| `oeis-full-50usd-gdm-…` | OEIS Open (492) | Gemini 3.5 Flash | base | $50 |
| `oeis-lite-200usd-ant-…` | Lite (100) | Claude Opus 4.8 | base | $200 |
| `oeis-lite-200usd-oai-…` | Lite (100) | GPT-5.5 | base | $200 |
| `oeis-lite-200usd-gdm-…` | Lite (100) | Gemini 3.5 Flash | base | $200 |
| `oeis-lite-200usd-fable-…` | Lite (100) | Claude Fable 5 | base | $200 |
| `oeis-lite-200usd-deep-ant-…` | Lite (100) | Claude Opus 4.8 | DeepAgent | $200 |
| `oeis-lite-200usd-deep-oai-…` | Lite (100) | GPT-5.5 | DeepAgent | $200 |
| `oeis-lite-200usd-deep-gdm-…` | Lite (100) | Gemini 3.5 Flash | DeepAgent | $200 |
| `oeis-lite-200usd-lit-ant-…` | Lite (100) | Claude Opus 4.8 | literature | $200 |
| `oeis-lite-200usd-lit-oai-…` | Lite (100) | GPT-5.5 | literature | $200 |
| `oeis-lite-200usd-lit-gdm-…` | Lite (100) | Gemini 3.5 Flash | literature | $200 |

## Repository layout

### Run contents

Each run directory (under `runs/`) contains one directory per attempted
conjecture, plus an aggregate `scores.json`:

- `Submission/` — the Lean files the agent submitted (the scored proof is
  `Spec.lean`)
- `info.json` — sample id, token usage, and cost
- `scores.json`, `scores.txt` — the SafeVerify verdict, including the failure
  stage and checker output for rejected submissions

Proofs that passed the verifier are the samples whose `scores.json` has
`.proof_scorer.value == "C"`.

Accepted samples may also include `metadata.json`, containing an LLM-written proof summary. 

### Metadata
The root `metadata/` directory contains run-independent data, organized per
benchmark. For OEIS Open, `metadata/oeis/` contains sequence descriptions
(`sequences.json`) and conjecture statements and provenance (`conjectures.json`).

## Source and methodology
Data in this repo is typically generated using code in `epoch-research/LeanOpenProblems`. See that repo for methodology.  