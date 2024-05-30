from __future__ import annotations

from results import Null, Some


def test_pattern_matching_on_ok_type() -> None:
    o = Some("yay")
    match o:
        case Some(value):
            reached = True

    assert value == "yay"
    assert reached


def test_pattern_matching_on_err_type() -> None:
    n = Null("nay")
    match n:
        case Null(value):
            reached = True

    assert value == "nay"
    assert reached
