import re
import pytest

from result.result import Err, Ok, Result, UnwrapFailedError


def get_test_error():
    return ValueError("Error code: Error message")


def parse(s: str) -> Result[float, str]:
    try:
        i = float(s)
        return Ok(i)
    except ValueError:
        return Err("Invalid format")
    except OverflowError:
        return Err("Number too large or too small")


def square(x: int) -> Result[int, int]:
    return Ok(x * x)


def err(x: int) -> Result[int, int]:
    return Err(x)


def count(s: str) -> int:
    return len(s)


def sq_then_to_string(x: int) -> Result[str, str]:
    try:
        sq = x * x
        return Ok(str(sq))
    except Exception:
        return Err("Overflowed")


def test_is_ok_when_ok_value_should_return_true():
    assert Result.Ok(10).is_ok()
    assert not Result.Err("Something went wrong").is_ok()


def test_is_ok_and_when_ok_value_should_match_predicate():
    assert Result.Ok(2).is_ok_and(lambda x: x > 1)
    assert not Result.Ok(0).is_ok_and(lambda x: x > 1)
    assert not Result.Err("Something went wrong").is_ok_and(lambda x: x > 1)


def test_is_err_when_err_value_should_return_true():
    assert not Result.Ok(-3).is_err()
    assert Result.Err("Something went wrong").is_err()


def test_is_err_and_when_err_value_should_match_predicate():
    assert Result.Err(get_test_error()).is_err_and(lambda x: isinstance(x, ValueError))
    assert not Result.Err(get_test_error()).is_err_and(lambda x: isinstance(x, str))
    assert not Result.Ok(-3).is_err_and(lambda x: isinstance(x, ValueError))


def test_ok_when_ok_value_should_return_value_or_default():
    assert Result.Ok(2).ok() == 2
    assert Result.Err("Nothing here").ok() is None


def test_err_when_err_value_should_return_value_or_default():
    assert Result.Ok(2).err() is None
    assert Result.Err("Nothing here").err() == "Nothing here"


def test_map_when_result_should_map_result_te_to_result_ue_by_applying_a_function_to_a_contained_ok_value_leaving_an_err_untouched():
    assert parse("5").map(lambda i: i * 2) == Ok(10.0)
    assert parse("Nothing here").map(lambda i: i * 2) == Err("Invalid format")


def test_map_or_when_result_should_apply_a_function_to_contained_value_or_default():
    assert Result.Ok("foo").map_or(lambda v: len(v), 42) == 3
    assert Result.Err("bar").map_or(lambda v: len(v), 42) == 42


def test_map_or_else_when_result_should_apply_a_function_to_contained_value_or_apply_fallback_function():
    k = 21
    assert Result.Ok("foo").map_or_else(lambda e: k * 2, lambda v: len(v)) == 3
    assert Result.Err("bar").map_or_else(lambda e: k * 2, lambda v: len(v)) == 42


def test_map_err_when_result_should_map_result_te_to_result_tf_by_applying_a_function_to_a_contained_err_value_leaving_an_ok_untouched():
    assert Result.Ok(5).map_err(str) == Ok(5)
    assert Result.Err(10).map_err(str) == Err("10")


def test_iter_when_ok_value_should_yield_value_or_default():
    assert list(Result.Ok(5)) == [5]
    assert list(Result.Err("Nothing here")) == [None]


def test_expect_when_ok_value_should_return_the_value_or_throws_an_error_with_the_given_message():
    assert Result.Ok(10).expect("Something went wrong") == 10
    with pytest.raises(UnwrapFailedError, match="Something went wrong"):
        Result.Err("Emergency failure").expect("Something went wrong")


def test_unwrap_when_ok_value_should_returns_the_value_or_throws_an_unwrap_failed_exception():
    assert Result.Ok(10).unwrap() == 10
    with pytest.raises(
        UnwrapFailedError,
        match=re.escape("Called `.unwrap` on an [`Err`] value: 'Emergency failure'"),
    ):
        Result.Err("Emergency failure").unwrap()
    with pytest.raises(
        UnwrapFailedError,
        match=re.escape(
            "Called `.unwrap` on an [`Err`] value: ValueError('Error message'"
        ),
    ):
        Result.Err(ValueError("Error message")).unwrap()


def test_expect_err_when_err_value_should_return_error_or_throws_an_error_with_the_given_message():
    assert Result.Err(10).expect_err("Something went wrong") == 10
    with pytest.raises(UnwrapFailedError, match="Testing expect error"):
        Result.Ok(10).expect_err("Testing expect error")


def test_unwrap_err_when_err_value_should_return_error_or_throws_an_unwrap_failed_exception():
    assert Result.Err(10).unwrap_err() == 10
    with pytest.raises(
        UnwrapFailedError, match=re.escape("Called `.unwrap_err` on an [`Ok`] value")
    ):
        Result.Ok(10).unwrap_err()


def test_and_then_when_ok_value_should_call_the_given_function_or_return_the_error_value():
    assert Result.Ok(2).and_then(sq_then_to_string) == Ok("4")
    assert Result.Err("Not a number").and_then(sq_then_to_string) == Err("Not a number")


def test_or_else_when_err_value_should_call_the_given_function_or_return_the_ok_value():
    assert Result.Ok(2).or_else(square).or_else(square) == Ok(2)
    assert Result.Ok(2).or_else(err).or_else(square) == Ok(2)
    assert Result.Err(3).or_else(square).or_else(err) == Ok(9)
    assert Result.Err(3).or_else(err).or_else(err) == Err(3)


def test_unwrap_or_when_ok_value_should_return_value_or_provided_default():
    default_value = 42
    assert Result.Ok(2).unwrap_or(default_value) == 2
    assert Result.Err("Something went wrong").unwrap_or(default_value) == 42


def test_unwrap_or_else_when_ok_value_should_return_value_or_compute_from_function():
    assert Result.Ok(2).unwrap_or_else(count) == 2
    assert Result.Err("foo").unwrap_or_else(count) == 3


def test_iter_when_ok_value_should_yield_value_or_none() -> None:
    assert list(Result.Ok(5).iter()) == [5]
    assert list(Result.Err("Nothing here").iter()) == [None]


def test_as_result_when_wrapping_a_function_should_return_a_new_fn_that_returns_a_result() -> (
    None
):
    @Result.as_result
    def div(a: int, b: int) -> float:
        return a / b

    assert div(10, 2) == Result.Ok(5.0)
    assert div(10, 0).map_err(str) == Result.Err("division by zero")


def test_repr_when_called_should_return_a_string_representation_of_the_result() -> None:
    assert repr(ok := Result.Ok(123)) == "Ok(123)"
    assert ok == eval(repr(ok))
    assert repr(err := Result.Err(-1)) == "Err(-1)"
    assert err == eval(repr(err))


def test_hash_when_called_should_return_a_hash_of_the_result() -> None:
    assert len({Result.Ok(1), Result.Err("2"), Result.Ok(1), Result.Err("2")}) == 2
    assert len({Result.Ok(1), Result.Ok(2)}) == 2
    assert len({Result.Ok("a"), Result.Err("a")}) == 2
