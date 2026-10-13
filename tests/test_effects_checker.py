from itertools import product

import pytest

from runbookfx.checker import Checker
from runbookfx.effects import BOT, Cap, Effect, Risk
from runbookfx.mock_llm import Plan, build
from runbookfx.syntax import (Act, Branch, Ctor, Let, LetPair, Lit, Observe, RequireApproval,
                              Retry, Rollback, Threshold, Var)

READS = {Cap.READ_LOGS, Cap.READ_METRICS, Cap.READ_TRACES}
ALL = frozenset(Cap)
codes = lambda res: {d.code for d in res.diags}  # noqa: E731


def grades():
    caps = [frozenset(s) for s in ([], [Cap.READ_LOGS], [Cap.LOG_ROTATE], [Cap.PURGE_VOLUME],
                                   [Cap.READ_LOGS, Cap.LOG_ROTATE])]
    return [Effect(r, k, n) for r, k, n in product(Risk, caps, range(3))]


def test_axioms_reject_inconsistent_grades():
    assert not Effect(Risk.READ_ONLY, frozenset(), 1).wf            # I1/I3
    assert not Effect(Risk.DISRUPTIVE, frozenset(), 0).wf           # I2
    assert not Effect(Risk.SAFE_CHANGE, frozenset({Cap.PURGE_VOLUME}), 1).wf  # I4
    assert BOT.wf


def test_join_preserves_wellformedness():
    wf = [g for g in grades() if g.wf]
    assert len(wf) > 10
    assert all(a.join(b).wf and a.alt(b).wf for a in wf for b in wf)


def test_join_is_additive_in_resources_and_alt_is_max():
    a = Effect(Risk.SAFE_CHANGE, frozenset({Cap.LOG_ROTATE}), 1)
    assert a.join(a).n == 2 and a.alt(a).n == 1


def test_checker_rejects_effect_violation_unapproved_disruptive():
    prog = LetPair("r", "t", Act(Cap.PURGE_VOLUME, "api-host", "purge"), Ctor("Success", Var("t")))
    res = Checker(ALL).check_program(prog)
    assert "E-APPROVAL" in codes(res) and not res.ok
    assert Checker(ALL).check_program(RequireApproval(prog)).ok


def test_checker_rejects_effect_above_maximum():
    safe_only_reads = Effect(Risk.READ_ONLY, frozenset(READS), 0)
    prog = build(Plan())
    assert "E-RISK" in codes(Checker(ALL, safe_only_reads).check_program(prog))


def test_checker_rejects_ungranted_capability():
    res = Checker(frozenset(READS)).check_program(build(Plan()))
    assert "E-CAP" in codes(res)


def test_checker_accepts_safe_runbook():
    kappa = frozenset(READS | {Cap.LOG_ROTATE})
    res = Checker(kappa, Effect(Risk.SAFE_CHANGE, kappa, 1)).check_program(build(Plan()))
    assert res.ok, res.diags
    assert res.effect == Effect(Risk.SAFE_CHANGE, frozenset({Cap.READ_LOGS, Cap.READ_METRICS, Cap.LOG_ROTATE}), 1)
    assert res.effect.wf


@pytest.mark.parametrize("token,code", [("leak", "E-LEAK"), ("double", "E-AFFINE")])
def test_affine_token_discipline(token, code):
    res = Checker(ALL).check_program(build(Plan(tok_mode=token)))
    assert code in codes(res)


def test_require_approval_needs_disruptive_body():
    res = Checker(ALL).check_program(RequireApproval(Observe(Cap.READ_LOGS, "h", "errors")))
    assert "E-APPROVAL" in codes(res)


def test_branch_takes_max_resources_and_retry_scales():
    act = lambda: LetPair("r", "t", Act(Cap.LOG_ROTATE, "h", "rotate"), Ctor("Success", Var("t")))  # noqa: E731
    cond = Threshold(Observe(Cap.READ_METRICS, "h", "disk_used_pct"), "<", 80.0)
    br = Branch(cond, (("true", act()), ("false", act())))
    assert Checker(ALL).check_program(br).effect.n == 1
    assert Checker(ALL).check_program(Retry(3, act())).effect.n == 3


def test_branch_arms_must_agree_and_be_exhaustive():
    cond = Threshold(Observe(Cap.READ_METRICS, "h", "disk_used_pct"), "<", 80.0)
    bad = Branch(cond, (("true", Lit(True)), ("false", Lit("x"))))
    assert "E-TYPE" in codes(Checker(ALL).check_program(bad))
    partial = Branch(cond, (("true", Lit(True)),))
    assert "E-TYPE" in codes(Checker(ALL).check_program(partial))


def test_retry_body_cannot_capture_outer_token():
    prog = LetPair("r", "t", Act(Cap.LOG_ROTATE, "h", "rotate"), Retry(2, Rollback(Var("t"))))
    assert not Checker(ALL).check_program(prog).ok


def test_unbound_variable_and_ill_typed_rollback():
    assert "E-SCOPE" in codes(Checker(ALL).check_program(Var("nope")))
    assert "E-TYPE" in codes(Checker(ALL).check_program(Let("x", Lit("s"), Rollback(Var("x")))))
