# RunbookFX demo

A trimmed demo of the core of *RunbookFX: Type- and Effect-Safe LLM Synthesis for Executable Incident
Diagnosis and Mitigation* (Xiao, Li, Ge; PACMPL 10, ICFP 2026, [doi:10.1145/3828675](https://doi.org/10.1145/3828675)).

> **Honesty notice.** This is a minimal demo that illustrates the method on a synthetic toy incident.
> It is a trimmed demo of the method's core, **not** the code used for the paper's experiments, and it
> does not reproduce any number reported in the paper. The mock "LLM" is a deterministic script.

## The paper in one paragraph

LLM agents that act directly on production systems can hallucinate diagnoses, run unauthorized
actions, and make changes that cannot be undone. RunbookFX turns incident response into executable
programs of a small typed functional DSL (`observe`, `act`, `guard`, `branch`, `retry`, `rollback`,
`require_approval`, `hypothesize`, `validate`). A type-and-effect system tracks a product effect
algebra *Risk x Capabilities x Rollback-count*, constrained by four interaction axioms, and treats
rollback tokens as affine resources. An LLM only proposes candidate programs. A CEGIS-style loop
accepts a candidate after static checking and contract replay, and otherwise feeds the failure back
for repair. Safety is stated for every accepted program, independent of the LLM.

## Quickstart

```sh
python -m runbookfx.demo      # prints the synthesis loop trace (well under a second)
pip install pytest && pytest -q
```

Python >= 3.10, standard library only (pytest for the tests). No network and no API key are used.
There is no real-LLM hook in this demo; any object with `generate` and `repair` (see `LLMClient` in
`runbookfx/synth.py`) can replace `MockLLM`.

## What the demo shows

Toy incident (synthetic): service `api` has high p99 latency because the log volume of `api-host` is
full. Restarting `api` does not help; rotating logs does; purging the volume also does but deletes data.
The operator grants reads, `log_rotate` and `purge_volume`, and sets the maximum effect to
`SafeChange` with at most one rollback obligation.

| Demo component | File | Paper concept |
|---|---|---|
| Risk lattice, capability sets, effect grade `(r, k, n)`, join / branch-join, axioms I1-I4 | `effects.py` | Parametric effect algebra, interaction axioms |
| AST, JSON codec, printer | `syntax.py` | Core syntax; candidates as JSON ASTs |
| `Gamma_u; Gamma_a; kappa \|- e : tau \|> eps`, affine rollback tokens, approval gate, top-level disruptive check, `eps <= eps_max` | `checker.py` | Type and effect system |
| Simulated world and handlers | `sim.py` | Handlers (replay vs. live) |
| Interpreter with audit trace, runtime guards | `interp.py` | Operational semantics, audit trace |
| `phi_causal`, `phi_postcheck` over the trace | `contracts.py` | Runtime contracts |
| Verify = parse, check, replay, contracts; score; repair loop; execute | `synth.py` | Multi-candidate ranking, CEGIS-style repair, synthesis-to-execution |
| Scripted candidates and rule-based repair | `mock_llm.py` | The LLM role |
| Trace printer | `demo.py` | - |

The demo run has five round-0 candidates, all flawed in a different way, so the repair loop runs:

1. `act[kubectl_restart]` without diagnosis: capability not granted (`E-CAP`).
2. `act[purge_volume]` without an approval gate: `E-APPROVAL` and `E-RISK` (round 1 adds the gate, then `E-RISK` remains).
3. Rollback token never consumed (`E-LEAK`).
4. Skips `validate`: type-correct, rejected by the replayed contract `phi_causal`.
5. Rollback token used twice (`E-AFFINE`).

After one repair round three candidates verify. Ranking uses the paper's weights
(`10 * typechecks + 5 * contract_score + 3 * replay_score - cost`); the highest-scoring verified program is
executed against the live simulator. The demo then runs the same program under a second handler in
which recovery fails, so the program takes its rollback path. This illustrates, but does not prove,
the "verify under replay, run under any handler" idea.

## Repository layout

```
runbookfx/    effects.py syntax.py checker.py sim.py interp.py contracts.py synth.py mock_llm.py demo.py
tests/        effect algebra + checker tests; interpreter + synthesis-loop tests
CITATION.bib  LICENSE
```

## Simplifications (differences from the paper)

- The grade `(r, k, n)`, the join (resources add up), the branch join (resources take the maximum),
  `wf` axioms I1-I4, the guard/branch/rollback/approval rules, and the affine treatment of tokens follow
  the paper. Only the monomorphic fragment is implemented; bounded effect polymorphism is not.
- Affine contexts are threaded through the derivation (tracking "available on some / every path")
  instead of being split up front. The unused-token warning is an error, as in the paper's pipeline.
- `retry n e` is checked with an empty affine context and multiplies the resource count of `e` by `n`;
  this scaling is my choice for the demo, not taken from the paper.
- Queries and actions are plain strings (`observe[c] target.key`, `act[c] target.action`) instead of
  typed `Query_c` / `Action_c` expressions. `Threshold` and `Ctor` (Success/Failure) are small
  additions to make the toy runnable. `hypothesize` / `validate` are audit points; their ordering is
  enforced by the replayed contract `phi_causal`, not by the type system.
- Capabilities are a reduced set (`log_rotate` and `purge_volume` are demo-specific).
- The replay handler runs on a snapshot of the simulator, not on an offline telemetry dataset.
  Contracts are two hand-written predicates; the paper's default set is not reproduced.
- The loop follows the paper's shape (k = 5 candidates, up to 3 repair rounds, weights 10/5/3/1) but
  the mock repairs from the first line of each report, with one scripted fix per error code. A
  candidate is accepted only if it passes both the static check and every contract on replay.
- No safety theorem is proved here. `trace_safety` only checks two trace-level consequences on the
  runs the demo performs.
- The costs, thresholds, and all world numbers are made-up toy values.

## Citation

If you use this code, please cite the paper:

```bibtex
@article{xiao2026runbookfx,
  title = {RunbookFX: Type- and Effect-Safe LLM Synthesis for Executable Incident Diagnosis and Mitigation},
  volume = {10},
  ISSN = {2475-1421},
  url = {http://dx.doi.org/10.1145/3828675},
  DOI = {10.1145/3828675},
  number = {ICFP},
  journal = {Proceedings of the ACM on Programming Languages},
  publisher = {Association for Computing Machinery (ACM)},
  author = {Xiao, Yifan and Li, Shijie and Ge, Yuhao},
  year = {2026},
  month = Aug,
  articleno = {277},
  numpages = {34},
}
```

The paper is open access (CC BY).

## License

MIT, see `LICENSE`. Copyright (c) 2026 Yifan Xiao.
