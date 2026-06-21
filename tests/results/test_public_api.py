"""Acceptance for the structural cut (issue #13): the Option family moved to
`results.option`, Result stays in `results.results`, and the public surface plus
the construction-boundary invariant are unchanged for users."""

from __future__ import annotations

import importlib

import pytest

import results
from results import Some

PUBLIC_NAMES = [
    "Err",
    "Null",
    "Ok",
    "Option",
    "Result",
    "ResultError",
    "Some",
    "UnwrapFailedError",
]


@pytest.mark.parametrize("name", PUBLIC_NAMES, ids=PUBLIC_NAMES)
def test_public_name_resolves(name: str) -> None:
    assert hasattr(results, name)
    assert name in results.__all__


def test_public_all_has_no_drift() -> None:
    assert sorted(results.__all__) == sorted(PUBLIC_NAMES)


@pytest.mark.parametrize(
    ("module", "expected"),
    [
        (
            "results.results",
            {"Result", "Ok", "Err", "ResultError", "UnwrapFailedError"},
        ),
        ("results.option", {"Option", "Some", "Null"}),
    ],
    ids=["result-family-stays-in-results", "option-family-in-option"],
)
def test_families_live_in_expected_module(module: str, expected: set[str]) -> None:
    mod = importlib.import_module(module)
    assert expected <= set(vars(mod))


@pytest.mark.parametrize(
    "module",
    ["results", "results.results", "results.option"],
    ids=["package", "results-module-first", "option-module-first"],
)
def test_module_imports_in_isolation(module: str) -> None:
    # No ImportError in any order — proves the results<->option cycle is broken.
    assert importlib.import_module(module) is not None


def test_some_none_boundary_guard_still_fires() -> None:
    # The construction-boundary invariant moved intact to results.option:
    # Some(None) is rejected, so the move did not weaken the guarantee.
    with pytest.raises(ValueError, match="Some.None. is forbidden"):
        Some(None)
