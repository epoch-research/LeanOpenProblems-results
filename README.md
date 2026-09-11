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

Later Lite runs in the paper's canonical configuration (base agent, $200 per
attempt). Runs named `oeis-open-lite-…` were launched from the canonical
`configs/oeis-open-lite.yaml` in `epoch-research/LeanOpenProblems`.

| Run directory | Set | Model | Agent | Budget/attempt |
|---|---|---|---|---|
| `oeis-lite-200usd-grok46-…` | Lite (100) | Grok 4.6 | base | $200 |
| `oeis-lite-200usd-sol-…` | Lite (100) | GPT-5.6 Sol | base | $200 |
| `oeis-open-lite-fable51-…` | Lite (100) | Claude Fable 5.1 | base | $200 |
| `oeis-open-lite-gemini31pro-…` | Lite (100) | Gemini 3.1 Pro | base | $200 |
| `oeis-open-lite-gpt6astra-…` | Lite (100) | GPT-6 Astra | base | $200 |

### FrontierMath Erdős

Runs for the evaluations reported in *FrontierMath Erdős* (Adamczewski and
Bloom, 2026): 68 open Erdős conjectures selected by Thomas Bloom (the
`bloom_selection` subsets of the `erdos` and `erdos_autoformalized` datasets),
attempted in the default configuration of one attempt per conjecture by the
`deepagent`-based agent with the offline literature snapshot, under $300 and 72
hours of working time per attempt. GPT-6 Astra is a pre-release model, named
`ultima-alpha` and `vega-alpha` in the logs.

| Run directory | Model name in logs | Configuration | Accepted |
|---|---|---|---|
| `bloom68-ultima-e1dhs43ykrmakree` | `ultima-alpha` | default | 3: Erdos1 (disproof), Erdos74 (disproof), Erdos126 (proof) |
| `bloom68-vega-hxlmrsfzzg3h01o7` | `vega-alpha` | default | 2: Erdos74 (disproof), Erdos126 (proof) |
| `bloom68-vega-roe-7avcuzc2f4e865lf` | `vega-alpha` | default (relaunch with retry-on-error) | 2: Erdos74 (disproof), Erdos126 (proof) |
| `erdos-ultima-alpha-1000usd-t4aijzkukl7718bm` | `ultima-alpha` | non-systematic: ReAct agent, no literature snapshot, $1,000 and 96 hours per attempt, an earlier 67-statement version of the problem set, SafeVerify checker | 3: Erdos74 (disproof), Erdos126 (proof), Erdos548 (proof) |
| `erdos-ultima-alpha-1000usd-t4aijzkukl7718bm-reruns` | `ultima-alpha` | second attempts of the above | 3: Erdos1 (disproof), Erdos74 (disproof), Erdos571 (proof) |

Notes specific to these runs:

- **Costs.** GPT-6 Astra had no published prices while these runs were made, so
  the harness metered its spend at GPT-5.6 Sol's prices ($5 / $30 per million
  input / output tokens, $0.50 cache read, $6.25 cache write). The `total_cost`
  in `info.json` and the cost limits are in those metered dollars. The paper
  reports costs at Astra's actual prices ($10 / $50 / $1 / $12.50), about 1.8 to
  2.0 times higher, and counts a benchmark resolution only if it cost at most
  $300 at actual prices, which excludes the Erdos1 disproof in
  `bloom68-ultima-e1dhs43ykrmakree` ($405).

## Repository layout

### Run contents

Each run directory (under `runs/`) contains one directory per attempted
conjecture, plus an aggregate `scores.json`:

- `Submission/` — the Lean files the agent submitted (the scored proof is
  `Spec.lean`)
- `info.json` — sample id, token usage, and cost
- `scores.json`, `scores.txt` — the verifier's verdict, including the failure
  stage and checker output for rejected submissions

Proofs that passed the verifier are the samples whose `scores.json` has
`.proof_scorer.value == "C"`.

Accepted samples may also include `metadata.json`, containing an LLM-written
proof summary and full natural-language proof.

### Verifier

Submissions are checked by Comparator. The OEIS Open paper runs and
`erdos-ultima-alpha-1000usd-…` predate the switch to Comparator and were checked
by SafeVerify.

### Metadata
The root `metadata/` directory contains run-independent data, organized per
benchmark. For OEIS Open, `metadata/oeis/` contains sequence descriptions
(`sequences.json`) and conjecture statements and provenance (`conjectures.json`).
For FrontierMath Erdős, `metadata/erdos/conjectures.json` contains informal
conjecture statements and erdosproblems.com links.

## Source and methodology
Data in this repo is typically generated using code in `epoch-research/LeanOpenProblems`. See that repo for methodology.  