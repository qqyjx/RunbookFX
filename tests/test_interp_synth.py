import json

import pytest

from runbookfx.demo import UnhelpfulHandler, make_spec
from runbookfx.effects import Cap
from runbookfx.interp import Interpreter, TokenError, UnauthorizedAction
from runbookfx.mock_llm import MockLLM, Plan, build
from runbookfx.sim import SimEnv, SimHandler
from runbookfx.synth import execute, synthesize, verify
from runbookfx.syntax import Act, Let, LetPair, ParseError, Rollback, Var, parse_program, to_json


def test_interpreter_mitigates_toy_incident():
    env = SimEnv()
    assert not env.healthy
    value, trace, problems = execute(make_spec(), env, build(Plan()))
    assert env.healthy and env.disk_used_pct == 41.0
    assert value[1][0] == "Success" and problems == []
    assert [t.kind for t in trace].count("act") == 1


def test_restart_does_not_fix_the_incident():
    env = SimEnv()
    SimHandler(env).act(Cap.KUBECTL_RESTART, "api", "restart")
    assert not env.healthy


def test_rollback_restores_state_when_recovery_check_fails():
    env = SimEnv()
    it = Interpreter(UnhelpfulHandler(env), make_spec().caps)
    value = it.run(build(Plan()))
    assert value[1][0] == "Failure" and env.disk_used_pct == 98.0
    assert it.trace[-1].kind == "rollback"


def test_runtime_guards_catch_what_the_checker_would_reject():
    it = Interpreter(SimHandler(SimEnv()), frozenset({Cap.READ_LOGS}))
    with pytest.raises(UnauthorizedAction):
        it.run(Act(Cap.LOG_ROTATE, "api-host", "rotate"))
    double = LetPair("r", "t", Act(Cap.LOG_ROTATE, "api-host", "rotate"),
                     Let("_", Rollback(Var("t")), Rollback(Var("t"))))
    with pytest.raises(TokenError):
        Interpreter(SimHandler(SimEnv()), frozenset(Cap)).run(double)


def test_json_roundtrip_and_parse_errors():
    prog = build(Plan(traces=True))
    assert parse_program(json.dumps(to_json(prog))) == prog
    for bad in ("not json", '{"node": "Nope"}', '{"node": "Observe", "cap": "rm_rf", "target": "x", "key": "y"}'):
        with pytest.raises(ParseError):
            parse_program(bad)
    v = verify(make_spec(), SimEnv(), "{")
    assert not v.accepted and v.diags[0].code == "E-PARSE"


def test_synthesis_loop_rejects_unsafe_candidates_then_accepts_safe_one():
    spec, env = make_spec(), SimEnv()
    before = env.summary()
    res = synthesize(MockLLM(), spec, env)
    assert not any(v.accepted for v in res.history[0])      # round 0: every draft is flawed
    assert res.accepted is not None and res.rounds == 1
    assert env.summary() == before                           # replay ran on a snapshot only
    execute(spec, env, res.accepted.expr)
    assert env.healthy


def test_contract_violation_is_caught_by_replay_not_by_types():
    v = verify(make_spec(), SimEnv(), MockLLM()._emit(Plan(validate=False)))
    assert not v.diags and v.violations and not v.accepted


def test_loop_abstains_when_nothing_verifies():
    class Stubborn:
        def generate(self, spec, k):
            return [json.dumps(to_json(build(Plan(cap=Cap.PURGE_VOLUME))))] * k
        def repair(self, spec, program, report, hint):
            return program
    spec, env = make_spec(), SimEnv()
    res = synthesize(Stubborn(), spec, env)
    assert res.accepted is None and len(res.history) == 4   # initial + N_max repair rounds
    assert not env.data_deleted
