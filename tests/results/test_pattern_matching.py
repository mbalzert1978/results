from __future__ import annotations

from results import Null, Option, Some


def test_pattern_matching_on_ok_type() -> None:
    o = Some("yay")
    match o:
        case Option(value):
            reached = True

    assert value == "yay"
    assert reached


def test_pattern_matching_on_err_type() -> None:
    n = Null()
    match n:
        case Option(None):
            reached = True

    assert reached
