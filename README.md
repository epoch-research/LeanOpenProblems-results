# LeanOpenProblems results

Per-sample outputs for the evaluation runs reported in *OEIS Open: How many
conjectures can language models turn into theorems?* (Adamczewski, 2026).

## Runs

| Run directory | Set | Model | Agent | Budget/attempt |
|---|---|---|---|---|
| `oeis-full-50usd-ant-…` | OEIS Open (492) | Claude Opus 4.8 | base | $50 |
| `oeis-full-50usd-oai-…` | OEIS Open (492) | GPT-5.5 | base | $50 |
| `oeis-full-50usd-gdm-…` | OEIS Open (492) | Gemini 3.5 Flash | base | $50 |
| `oeis-lite-200usd-ant-…` | Lite (100) | Claude Opus 4.8 | base | $200 |
| `oeis-lite-200usd-oai-…` | Lite (100) | GPT-5.5 | base | $200 |
| `oeis-lite-200usd-gdm-…` | Lite (100) | Gemini 3.5 Flash | base | $200 |
| `oeis-lite-200usd-fable-…` | Lite (100) | Claude Fable 5 | base | $200 |
| `oeis-lite-200usd-deep-…` | Lite (100) | (per suffix) | DeepAgent | $200 |
| `oeis-lite-200usd-lit-…` | Lite (100) | (per suffix) | literature | $200 |

Model suffixes: `ant` = Claude Opus 4.8, `oai` = GPT-5.5, `gdm` = Gemini 3.5
Flash, `fable` = Claude Fable 5.

## Contents

Each run directory contains one directory per attempted conjecture, plus an
aggregate `scores.json`:

- `Submission/` — the Lean files the agent submitted (the scored proof is
  `Spec.lean`)
- `info.json` — sample id, token usage, and cost
- `scores.json`, `scores.txt` — the SafeVerify verdict, including the failure
  stage and checker output for rejected submissions

The full-set runs contain a directory only for samples where the agent
produced a submission.
