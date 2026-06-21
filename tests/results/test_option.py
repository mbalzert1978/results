from __future__ import annotations

import re

import pytest

from results import Err, Null, Ok, Option, Some, TransposeError, UnwrapFailedError


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
    "option, optb, expected",
    [
        (Some(1), Some(2), Some(2)),
        (Some(1), Null(), Null()),
        (Null(), Some(2), Null()),
        (Null(), Null(), Null()),
    ],
    ids=[
        "test_and_when_some_and_some_should_return_optb",
        "test_and_when_some_and_null_should_return_null",
        "test_and_when_null_and_some_should_return_null",
        "test_and_when_null_and_null_should_return_null",
    ],
)
def test_and_when_called_should_return_optb_if_some_else_null(
    option: Option, optb: Option, expected: Option
) -> None:
    assert option.and_(optb) == expected


def test_and_some_returns_same_optb_instance() -> None:
    optb: Option = Some(99)
    assert Some(1).and_(optb) is optb


@pytest.mark.parametrize(
    "option1, option2, expected",
    [
        (Some(1), Null(), Some(1)),
        (Null(), Some(2), Some(2)),
        (Some(1), Some(2), Null()),
        (Null(), Null(), Null()),
    ],
    ids=[
        "test_xor_when_some_and_null_should_return_self",
        "test_xor_when_null_and_some_should_return_optb",
        "test_xor_when_both_some_should_return_null",
        "test_xor_when_both_null_should_return_null",
    ],
)
def test_xor_when_called_should_return_some_iff_exactly_one_is_some(
    option1: Option, option2: Option, expected: Option
) -> None:
    assert option1.xor(option2) == expected


def test_xor_null_returns_same_optb_instance() -> None:
    optb: Option = Some(42)
    assert Null().xor(optb) is optb


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
    option: Option = Null()
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
    "option, predicate, expected",
    [
        (Null(), lambda x: x % 2 == 0, True),
        (Some(10), lambda x: x % 2 == 0, True),
        (Some(15), lambda x: x % 2 == 0, False),
    ],
    ids=[
        "test_is_none_or_when_null_should_return_true",
        "test_is_none_or_when_some_and_predicate_true_should_return_true",
        "test_is_none_or_when_some_and_predicate_false_should_return_false",
    ],
)
def test_is_none_or_when_null_returns_true_and_some_defers_to_predicate(
    option, predicate, expected
) -> None:
    assert option.is_none_or(predicate) == expected


def test_is_some_and_is_some_and_callable_through_option_base() -> None:
    # Regression for the typed interface: is_some / is_some_and must be
    # reachable through an Option[T] reference (declared on the ABC), not only
    # on the concrete Some / Null. This guards against them silently slipping
    # off the base again — `uv run mypy src tests` is the real gate here.
    present: Option[int] = Some(10)
    absent: Option[int] = Null()
    assert present.is_some()
    assert not absent.is_some()
    assert present.is_some_and(lambda v: v > 5)
    assert not absent.is_some_and(lambda v: v > 5)


def test_inspect_runs_fn_only_on_some_and_returns_self() -> None:
    calls: list[int] = []
    fn = lambda v: calls.append(v)  # noqa: E731

    some = Some(42)
    result = some.inspect(fn)
    assert result is some
    assert calls == [42]

    calls.clear()
    null: Option = Null()
    result_null = null.inspect(fn)
    assert result_null is null
    assert calls == []


@pytest.mark.parametrize(
    "option, expected_calls",
    [
        (Some(7), [7]),
        (Null(), []),
    ],
    ids=[
        "test_inspect_when_some_should_call_fn_with_value",
        "test_inspect_when_null_should_not_call_fn",
    ],
)
def test_inspect_when_called_should_side_effect_on_some_and_noop_on_null(
    option, expected_calls
) -> None:
    calls: list[int] = []
    option.inspect(lambda v: calls.append(v))
    assert calls == expected_calls


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
        (Some(0), 0),
        (Some(""), ""),
        (Some([]), []),
    ],
    ids=[
        "test_iter_when_some_with_int_should_yield_int",
        "test_iter_when_null_with_none_should_yield_none",
        "test_iter_when_some_with_str_should_yield_str",
        "test_iter_when_some_with_zero_should_yield_zero",
        "test_iter_when_some_with_empty_str_should_yield_empty_str",
        "test_iter_when_some_with_empty_list_should_yield_empty_list",
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
        (Some(0), "Some(0)"),
    ],
    ids=[
        "test_repr_when_some_with_int_should_return_formatted_string",
        "test_repr_when_null_with_none_should_return_formatted_string",
        "test_repr_when_some_with_str_should_return_formatted_string",
        "test_repr_when_null_with_str_should_return_formatted_string",
        "test_repr_when_some_zero_should_return_some_zero",
    ],
)
def test_repr(option, expected):
    assert repr(option) == expected


def test_str_when_some_should_return_value_string() -> None:
    assert str(Some(10)) == "10"
    assert str(Null()) == "None"


def test_some_none_is_forbidden() -> None:
    # None is absence, not a value: Some(None) raises, as do paths that would
    # wrap None (map -> None, transpose). Use Null() / and_then instead.
    with pytest.raises(ValueError, match="Some.None. is forbidden"):
        Some(None)
    with pytest.raises(ValueError, match="Some.None. is forbidden"):
        Some(5).map(lambda _: None)
    with pytest.raises(ValueError, match="Some.None. is forbidden"):
        Some(Ok(None)).transpose()


def test_option_base_class_cannot_be_instantiated_directly() -> None:
    with pytest.raises(TypeError):
        Option()  # type: ignore[abstract]


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
        (Some(0), Null(), False),
        (Some(""), Null(), False),
    ],
    ids=[
        "test_eq_when_some_with_same_int_should_return_true",
        "test_eq_when_null_with_same_none_should_return_true",
        "test_eq_when_some_with_same_str_should_return_true",
        "test_eq_when_null_with_same_str_should_return_true",
        "test_eq_when_some_and_null_with_same_int_should_return_false",
        "test_eq_when_some_with_different_int_should_return_false",
        "test_eq_when_null_with_different_values_should_return_true",
        "test_eq_when_some_zero_and_null_should_return_false",
        "test_eq_when_some_empty_str_and_null_should_return_false",
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
        (Some(0), Null(), True),
    ],
    ids=[
        "test_ne_when_some_with_same_int_should_return_false",
        "test_ne_when_null_with_same_none_should_return_false",
        "test_ne_when_some_with_same_str_should_return_false",
        "test_ne_when_null_with_same_str_should_return_false",
        "test_ne_when_some_and_null_with_same_int_should_return_true",
        "test_ne_when_some_with_different_int_should_return_true",
        "test_ne_when_some_zero_and_null_should_return_true",
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
        (Some(0), 42, 0),
        (Some(""), "x", ""),
        (Some([]), [1], []),
    ],
    ids=[
        "test_unwrap_or_when_some_should_return_value",
        "test_unwrap_or_when_null_should_return_default",
        "test_unwrap_or_when_some_zero_should_return_zero_not_default",
        "test_unwrap_or_when_some_empty_str_should_return_empty_str_not_default",
        "test_unwrap_or_when_some_empty_list_should_return_empty_list_not_default",
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
        (Some(0), lambda: 3, 0),
        (Some(""), lambda: "x", ""),
    ],
    ids=[
        "test_unwrap_or_else_when_some_should_return_value",
        "test_unwrap_or_else_when_null_should_call_func_and_return_value",
        "test_unwrap_or_else_when_some_zero_should_return_zero_not_func",
        "test_unwrap_or_else_when_some_empty_str_should_return_empty_str_not_func",
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
        (Null(), Ok(Null())),
    ],
    ids=[
        "transpose_when_some_ok_should_return_ok_with_some_value",
        "transpose_when_some_err_should_return_err",
        "transpose_when_null_should_return_ok_with_null",
    ],
)
def test_transpose_with_result(option, expected):
    assert option.transpose() == expected


def test_transpose_on_non_result_payload_raises() -> None:
    # Option.transpose expects Option[Result[...]]; a Some holding a non-Result
    # value is a contract violation — raise loudly, never silently wrap.
    with pytest.raises(TransposeError, match="non-Result"):
        Some(5).transpose()


@pytest.mark.parametrize(
    "option, expected",
    [
        (Some(Some(5)), Some(5)),
        (Some(Null()), Null()),
        (Null(), Null()),
    ],
    ids=[
        "some_some_to_some",
        "some_null_to_null",
        "null_to_null",
    ],
)
def test_flatten_collapses_one_level_of_nesting(
    option: Option, expected: Option
) -> None:
    assert option.flatten() == expected


def test_flatten_some_returns_inner_option_identity() -> None:
    # Some.flatten must return the inner Option unchanged — not a re-wrapped copy.
    inner_some: Option[int] = Some(5)
    assert Some(inner_some).flatten() is inner_some

    inner_null: Option[int] = Null()
    assert Some(inner_null).flatten() is inner_null


def test_option_error_is_no_longer_exported() -> None:
    import results

    assert not hasattr(results, "OptionError")
    assert "OptionError" not in results.__all__


def test_transpose_error_is_exported() -> None:
    import results

    assert results.TransposeError is TransposeError
    assert "TransposeError" in results.__all__


@pytest.mark.parametrize(
    "option_a, option_b, expected",
    [
        (Some(1), Some("x"), Some((1, "x"))),
        (Some(1), Null(), Null()),
        (Null(), Some("x"), Null()),
        (Null(), Null(), Null()),
    ],
    ids=[
        "test_zip_when_both_some_should_return_some_tuple",
        "test_zip_when_some_and_null_should_return_null",
        "test_zip_when_null_and_some_should_return_null",
        "test_zip_when_both_null_should_return_null",
    ],
)
def test_zip_when_called_should_return_some_tuple_or_null(
    option_a: Option, option_b: Option, expected: Option
) -> None:
    assert option_a.zip(option_b) == expected


@pytest.mark.parametrize(
    "option, expected",
    [
        (Some((1, "x")), (Some(1), Some("x"))),
        (Null(), (Null(), Null())),
    ],
    ids=[
        "test_unzip_when_some_tuple_should_return_pair_of_somes",
        "test_unzip_when_null_should_return_pair_of_nulls",
    ],
)
def test_unzip_when_called_should_split_option_tuple_into_pair(
    option: Option, expected: tuple
) -> None:
    assert option.unzip() == expected


@pytest.mark.parametrize(
    "option",
    [
        Some((None, 5)),
        Some((5, None)),
    ],
    ids=[
        "test_unzip_when_first_component_is_none_should_raise_value_error",
        "test_unzip_when_second_component_is_none_should_raise_value_error",
    ],
)
def test_unzip_when_component_is_none_should_raise_value_error(option: Option) -> None:
    with pytest.raises(ValueError, match="Some.None. is forbidden"):
        option.unzip()
