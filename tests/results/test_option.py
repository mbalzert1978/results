from __future__ import annotations

import re

import pytest

from results import Err, Null, Ok, Option, Some, UnwrapFailedError


@Option.as_option
def div(a: int, b: int) -> float | None:
    return None if b == 0 else a / b


@Option.as_option
def sq_then_to_string(x: int) -> str | None:
    try:
        return str(x**2)
    except Exception:
        return None


@pytest.mark.parametrize(
    "option, func, expected",
    [
        (Some(2), sq_then_to_string, Some("4")),
        (Null(), sq_then_to_string, Null()),
    ],
    ids=[
        "test_and_then_when_some_should_call_function",
        "test_and_then_when_null_should_return_null",
    ],
)
def test_and_then_when_value_should_call_the_given_function_or_return_none(
    option: Option, func, expected
) -> None:
    assert option.and_then(func) == expected


def test_expect_when_some_should_return_value() -> None:
    option = Some(10)
    msg = "Something went wrong"
    expected = 10
    assert option.expect(msg) == expected


def test_expect_when_null_should_raise_error() -> None:
    option = Null()
    msg = "Something went wrong"
    with pytest.raises(UnwrapFailedError, match=msg):
        option.expect(msg)


@pytest.mark.parametrize(
    "option, predicate, expected",
    [
        (Some(10), lambda x: x % 2 == 0, Some(10)),
        (Some(15), lambda x: x % 2 == 0, Null()),
        (Null(), lambda x: x % 2 == 0, Null()),
    ],
    ids=[
        "test_filter_when_some_and_predicate_true_should_return_some",
        "test_filter_when_some_and_predicate_false_should_return_null",
        "test_filter_when_null_should_return_null",
    ],
)
def test_option_filter_when_predicate_is_called_should_return_some_if_true_and_null_if_false(
    option, predicate, expected
) -> None:
    assert option.filter(predicate) == expected


def test_option_from_fn_when_some_should_return_some() -> None:
    values = {
        "1": 1,
        "2": 2,
        "3": 3,
        "4": 4,
        "5": 5,
        "6": 6,
    }
    assert Option.from_fn(dict.get, values, "1") == Some(1)
    assert Option.from_fn(dict.get, values, "7") == Null()


@pytest.mark.parametrize(
    "option, expected",
    [
        (Null(), True),
        (Some(10), False),
    ],
    ids=[
        "test_is_none_when_null_should_return_true",
        "test_is_none_when_some_should_return_false",
    ],
)
def test_is_none_when_null_value_should_return_true(option: Option, expected) -> None:
    assert option.is_none() == expected


@pytest.mark.parametrize(
    "option, expected",
    [
        (Null(), False),
        (Some(10), True),
    ],
    ids=[
        "test_is_some_when_null_should_return_false",
        "test_is_some_when_some_should_return_true",
    ],
)
def test_is_some_when_value_should_return_true(option, expected) -> None:
    assert option.is_some() == expected


@pytest.mark.parametrize(
    "option, predicate, expected",
    [
        (Some(10), lambda x: x % 2 == 0, True),
        (Some(15), lambda x: x % 2 == 0, False),
        (Null(), lambda x: x % 2 == 0, False),
    ],
    ids=[
        "test_is_some_and_when_some_and_predicate_true_should_return_true",
        "test_is_some_and_when_some_and_predicate_false_should_return_false",
        "test_is_some_and_when_null_should_return_false",
    ],
)
def test_is_some_and_when_some_value_should_match_predicate(
    option, predicate, expected
) -> None:
    assert option.is_some_and(predicate) == expected


@pytest.mark.parametrize(
    "option, func, expected",
    [
        (Some(10), lambda i: i * 2, Some(20)),
        (Null(), lambda i: i * 2, Null()),
    ],
    ids=[
        "test_map_when_some_should_apply_function",
        "test_map_when_null_should_return_null",
    ],
)
def test_map_on_option_should_map_option_te_to_option_ue_by_applying_a_function_to_a_contained_some_value_leaving_an_null_untouched(
    option: Option, func, expected
) -> None:
    assert option.map(func) == expected


@pytest.mark.parametrize(
    "option, default, func, expected",
    [
        (Some("foo"), 42, lambda v: len(v), 3),
        (Null(), 42, lambda v: len(v), 42),
    ],
    ids=[
        "test_map_or_when_some_should_apply_function",
        "test_map_or_when_null_should_return_default",
    ],
)
def test_map_or_when_option_should_apply_a_function_to_contained_value_or_default(
    option, default, func, expected
):
    assert option.map_or(default, func) == expected


@pytest.mark.parametrize(
    "option, default_func, func, expected",
    [
        (Some("foo"), lambda: 21 * 2, lambda v: len(v), 3),
        (Null(), lambda: 21 * 2, lambda v: len(v), 42),
    ],
    ids=[
        "test_map_or_else_when_some_should_apply_function",
        "test_map_or_else_when_null_should_apply_default_function",
    ],
)
def test_map_or_else_when_option_should_apply_a_function_to_contained_value_or_apply_fallback_function(
    option, default_func, func, expected
):
    assert option.map_or_else(default_func, func) == expected


@pytest.mark.parametrize(
    "option, msg, expected",
    [
        (Some(10), "Something went wrong", Ok(10)),
        (Null(), "Something went wrong", Err("Something went wrong")),
    ],
    ids=[
        "test_ok_or_when_some_should_return_ok",
        "test_ok_or_when_null_should_return_err",
    ],
)
def test_option_ok_or_when_called_should_map_option_to_result(
    option, msg, expected
) -> None:
    assert option.ok_or(msg) == expected


@pytest.mark.parametrize(
    "option, msg_func, expected",
    [
        (Some(10), lambda: "Something went wrong", Ok(10)),
        (Null(), lambda: "Something went wrong", Err("Something went wrong")),
    ],
    ids=[
        "test_ok_or_else_when_some_should_return_ok",
        "test_ok_or_else_when_null_should_return_err",
    ],
)
def test_option_ok_or_else_when_called_should_map_some_to_ok_and_null_to_err(
    option, msg_func, expected
) -> None:
    assert option.ok_or_else(msg_func) == expected


@pytest.mark.parametrize(
    "option1, option2, expected",
    [
        (Some(2), Null(), Some(2)),
        (Null(), Some(100), Some(100)),
        (Some(2), Some(100), Some(2)),
        (Null(), Null(), Null()),
    ],
    ids=[
        "test_or_when_some_should_return_some",
        "test_or_when_null_should_return_other_option",
        "test_or_when_both_some_should_return_first",
        "test_or_when_both_null_should_return_null",
    ],
)
def test_option_or_when_called_should_return_option_if_contained_value_otherwise_optb(
    option1, option2, expected
) -> None:
    assert option1.or_(option2) == expected


@pytest.mark.parametrize(
    "option, func, expected",
    [
        (Some(2), lambda: Some(100), Some(2)),
        (Some(2), lambda: Null(), Some(2)),
        (Null(), lambda: Some(100), Some(100)),
        (Null(), lambda: Null(), Null()),
    ],
    ids=[
        "test_or_else_when_some_should_return_some",
        "test_or_else_when_some_should_return_some_even_if_func_returns_null",
        "test_or_else_when_null_should_call_func_and_return_some",
        "test_or_else_when_null_should_call_func_and_return_null",
    ],
)
def test_or_else_when_null_should_call_the_given_function_or_return_the_some_value(
    option, func, expected
):
    assert option.or_else(func) == expected


@pytest.mark.parametrize(
    "option, expected",
    [
        (Some(10), 10),
        (Null(), None),
        (Some("test"), "test"),
    ],
    ids=[
        "test_iter_when_some_with_int_should_yield_int",
        "test_iter_when_null_with_none_should_yield_none",
        "test_iter_when_some_with_str_should_yield_str",
    ],
)
def test_iter(option, expected):
    assert list(option) == [expected]


@pytest.mark.parametrize(
    "option, expected",
    [
        (Some(10), "Some(10)"),
        (Null(), "Null()"),
        (Some("test"), "Some('test')"),
        (Null(), "Null()"),
    ],
    ids=[
        "test_repr_when_some_with_int_should_return_formatted_string",
        "test_repr_when_null_with_none_should_return_formatted_string",
        "test_repr_when_some_with_str_should_return_formatted_string",
        "test_repr_when_null_with_str_should_return_formatted_string",
    ],
)
def test_repr(option, expected):
    assert repr(option) == expected


def test_str_when_some_should_return_value_string() -> None:
    assert str(Some(10)) == "10"
    assert str(Null()) == "None"


@pytest.mark.parametrize(
    "options, expected",
    [
        ({Some(1), Null(), Some(1), Null()}, 2),
        ({Some(1), Some(2)}, 2),
        ({Some("a"), Null()}, 2),
    ],
    ids=[
        "test_hash_when_some_and_no_duplicates_should_return_correct_length",
        "test_hash_when_different_some_values_should_return_correct_length",
        "test_hash_when_some_and_null_strings_should_return_correct_length",
    ],
)
def test_hash(options, expected) -> None:
    assert len(options) == expected


@pytest.mark.parametrize(
    "option1, option2, expected",
    [
        (Some(10), Some(10), True),
        (Null(), Null(), True),
        (Some("test"), Some("test"), True),
        (Null(), Null(), True),
        (Some(10), Null(), False),
        (Some(10), Some(20), False),
        (Null(), Null(), True),
    ],
    ids=[
        "test_eq_when_some_with_same_int_should_return_true",
        "test_eq_when_null_with_same_none_should_return_true",
        "test_eq_when_some_with_same_str_should_return_true",
        "test_eq_when_null_with_same_str_should_return_true",
        "test_eq_when_some_and_null_with_same_int_should_return_false",
        "test_eq_when_some_with_different_int_should_return_false",
        "test_eq_when_null_with_different_values_should_return_true",
    ],
)
def test_eq(option1, option2, expected):
    assert (option1 == option2) == expected


@pytest.mark.parametrize(
    "option1, option2, expected",
    [
        (Some(10), Some(10), False),
        (Null(), Null(), False),
        (Some("test"), Some("test"), False),
        (Null(), Null(), False),
        (Some(10), Null(), True),
        (Some(10), Some(20), True),
    ],
    ids=[
        "test_ne_when_some_with_same_int_should_return_false",
        "test_ne_when_null_with_same_none_should_return_false",
        "test_ne_when_some_with_same_str_should_return_false",
        "test_ne_when_null_with_same_str_should_return_false",
        "test_ne_when_some_and_null_with_same_int_should_return_true",
        "test_ne_when_some_with_different_int_should_return_true",
    ],
)
def test_ne(option1, option2, expected):
    assert (option1 != option2) == expected


@pytest.mark.parametrize(
    "a, b, expected",
    [
        (10, 0, Null()),
        (10, 2, Some(5.0)),
        (-10, 2, Some(-5.0)),
        (0, 2, Some(0.0)),
        (1_000_000, 2, Some(500_000.0)),
    ],
    ids=[
        "test_as_null_when_division_by_zero_should_return_null",
        "test_as_null_when_valid_division_should_return_some",
        "test_as_null_when_negative_division_should_return_some",
        "test_as_null_when_zero_dividend_should_return_some",
        "test_as_null_when_large_numbers_should_return_some",
    ],
)
def test_as_Null(a, b, expected) -> None:
    assert div(a, b) == expected


def test_unwrap_when_some_should_return_value() -> None:
    assert Some(10).unwrap() == 10


def test_unwrap_when_null_should_raise_error() -> None:
    msg = "Called `.unwrap` on an [`Null`] value."
    with pytest.raises(UnwrapFailedError, match=re.escape(msg)):
        Null().unwrap()


@pytest.mark.parametrize(
    "option, default, expected",
    [
        (Some(2), 42, 2),
        (Null(), 42, 42),
    ],
    ids=[
        "test_unwrap_or_when_some_should_return_value",
        "test_unwrap_or_when_null_should_return_default",
    ],
)
def test_unwrap_or_when_some_value_should_return_value_or_provided_default(
    option, default, expected
):
    assert option.unwrap_or(default) == expected


@pytest.mark.parametrize(
    "option, func, expected",
    [
        (Some(2), lambda: 3, 2),
        (Null(), lambda: 3, 3),
    ],
    ids=[
        "test_unwrap_or_else_when_some_should_return_value",
        "test_unwrap_or_else_when_null_should_call_func_and_return_value",
    ],
)
def test_unwrap_or_else_when_some_value_should_return_value_or_compute_from_function(
    option, func, expected
):
    assert option.unwrap_or_else(func) == expected


@pytest.mark.parametrize(
    "option, func, expected",
    [
        (Some(2), lambda: Some(100), Some(2)),
        (Some(2), lambda: Null(), Some(2)),
        (Null(), lambda: Some(100), Some(100)),
        (Null(), lambda: Null(), Null()),
    ],
    ids=[
        "test_or_else_when_some_should_return_some",
        "test_or_else_when_some_should_return_some_even_if_func_returns_null",
        "test_or_else_when_null_should_call_func_and_return_some",
        "test_or_else_when_null_should_call_func_and_return_null",
    ],
)
def test_or_else_when_some_should_return_some(option, func, expected):
    assert option.or_else(func) == expected


@pytest.mark.parametrize(
    "option, expected",
    [
        (Some(Ok(5)), Ok(Some(5))),
        (Some(Err("error")), Err("error")),
        (Some(Ok(None)), Ok(Some(None))),
        (Null(), Ok(Some(None))),
        (Some(5), Ok(Some(5))),
    ],
    ids=[
        "transpose_when_some_ok_should_return_ok_with_some_value",
        "transpose_when_some_err_should_return_err",
        "transpose_when_some_ok_none_should_return_ok_with_some_none",
        "transpose_when_null_err_should_return_ok_none",
        "transpose_when_some_value_should_return_ok_some_value",
    ],
)
def test_transpose_with_result(option, expected):
    assert option.transpose() == expected
