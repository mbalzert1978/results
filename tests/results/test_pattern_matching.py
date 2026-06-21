from __future__ import annotations

from results import Null, Option, Some


def test_pattern_matching_on_some_type() -> None:
    o = Some("yay")
    reached = False
    match o:
        case Some(value):
            reached = True

    assert value == "yay"
    assert reached


def test_pattern_matching_on_null_type() -> None:
    n: Option = Null()
    reached = False
    match n:
        case Null():
            reached = True

    assert reached


def test_pattern_matching_distinguishes_some_none_from_null() -> None:
    o = Some(None)
    match o:
        case Null():
            branch = "null"
        case Some(value):
            branch = "some"

    assert branch == "some"
    assert value is None
