import re

import pytest

from results import Err, Null, Ok, Result, Some, UnwrapFailedError


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
    return Ok(x**2)


def err(x: int) -> Result[int, int]:
    return Err(x)


def count(s: str) -> int:
    return len(s)


def sq_then_to_string(x: int) -> Result[str, str]:
    try:
        sq = str(x**2)
    except Exception:
        return Err("Overflowed")
    else:
        return Ok(sq)


@pytest.mark.parametrize(
    "result, expected",
    [
        (Ok(10), True),
        (Err("Something went wrong"), False),
    ],
    ids=[
        "is_ok when Ok value should return True",
        "is_ok when Err value should return False",
    ],
)
def test_is_ok(result, expected):
    assert result.is_ok() == expected


@pytest.mark.parametrize(
    "result, predicate, expected",
    [
        (Ok(2), lambda x: x > 1, True),
        (Ok(0), lambda x: x > 1, False),
        (Err("Something went wrong"), lambda x: x > 1, False),
    ],
    ids=[
        "is_ok_and when Ok value matches predicate should return True",
        "is_ok_and when Ok value does not match predicate should return False",
        "is_ok_and when Err value should return False",
    ],
)
def test_is_ok_and(result, predicate, expected):
    assert result.is_ok_and(predicate) == expected


@pytest.mark.parametrize(
    "result, predicate, expected",
    [
        (Err(2), lambda x: x > 1, True),
        (Err(0), lambda x: x > 1, False),
        (Ok("Something went wrong"), lambda x: x > 1, False),
    ],
    ids=[
        "is_err_and when Err value matches predicate should return True",
        "is_err_and when Err value does not match predicate should return False",
        "is_err_and when Ok value should return False",
    ],
)
def test_is_err_and(result, predicate, expected):
    assert result.is_err_and(predicate) == expected


@pytest.mark.parametrize(
    "result, expected",
    [
        (Ok(2), Some(2)),
        (Err("Nothing here"), Null(None)),
    ],
    ids=[
        "ok when Ok value should return value",
        "ok when Err value should return None",
    ],
)
def test_ok(result, expected):
    assert result.ok() == expected


@pytest.mark.parametrize(
    "result, expected",
    [
        (Ok(2), None),
        (Err("Nothing here"), "Nothing here"),
    ],
    ids=[
        "err when Ok value should return None",
        "err when Err value should return value",
    ],
)
def test_err(result, expected):
    assert result.err() == expected


@pytest.mark.parametrize(
    "input, func, expected",
    [
        (parse("5"), lambda i: i * 2, Ok(10.0)),
        (parse("Nothing here"), lambda i: i * 2, Err("Invalid format")),
    ],
    ids=[
        "map when Ok value should apply function",
        "map when Err value should remain untouched",
    ],
)
def test_map(input, func, expected):
    assert input.map(func) == expected


@pytest.mark.parametrize(
    "result, func, default, expected",
    [
        (Ok("foo"), lambda v: len(v), 42, 3),
        (Err("bar"), lambda v: len(v), 42, 42),
    ],
    ids=[
        "map_or when Ok value should apply function",
        "map_or when Err value should return default",
    ],
)
def test_map_or(result, func, default, expected):
    assert result.map_or(func, default) == expected


@pytest.mark.parametrize(
    "result, default_func, func, expected",
    [
        (Ok("foo"), lambda e: 42, lambda v: len(v), 3),
        (Err("bar"), lambda e: 42, lambda v: len(v), 42),
    ],
    ids=[
        "map_or_else when Ok value should apply function",
        "map_or_else when Err value should apply default function",
    ],
)
def test_map_or_else(result, default_func, func, expected):
    assert result.map_or_else(default_func, func) == expected


@pytest.mark.parametrize(
    "result, func, expected",
    [
        (Ok(5), str, Ok(5)),
        (Err(10), str, Err("10")),
    ],
    ids=[
        "map_err when Ok value should remain untouched",
        "map_err when Err value should apply function",
    ],
)
def test_map_err(result, func, expected):
    assert result.map_err(func) == expected


@pytest.mark.parametrize(
    "result, expected",
    [
        (Ok(5), [5]),
        (Err("Nothing here"), [None]),
    ],
    ids=[
        "iter when Ok value should yield value",
        "iter when Err value should yield None",
    ],
)
def test_iter(result, expected):
    assert list(result) == expected


@pytest.mark.parametrize(
    "result, msg, expected",
    [
        (Ok(10), "Something went wrong", 10),
    ],
    ids=[
        "expect when Ok value should return value",
    ],
)
def test_expect_ok(result, msg, expected):
    assert result.expect(msg) == expected


@pytest.mark.parametrize(
    "result, msg, expected",
    [
        (
            Err("Emergency failure"),
            "Something went wrong",
            pytest.raises(UnwrapFailedError, match="Something went wrong"),
        ),
    ],
    ids=[
        "expect when Err value should raise UnwrapFailedError",
    ],
)
def test_expect_err(result, msg, expected):
    with expected:
        result.expect(msg)


@pytest.mark.parametrize(
    "result, expected",
    [
        (Ok(10), 10),
    ],
    ids=[
        "unwrap when Ok value should return value",
    ],
)
def test_unwrap_ok(result, expected):
    assert result.unwrap() == expected


@pytest.mark.parametrize(
    "result, expected",
    [
        (
            Err("Emergency failure"),
            pytest.raises(
                UnwrapFailedError,
                match=re.escape(
                    "Called `.unwrap` on an [`Err`] value: 'Emergency failure'"
                ),
            ),
        ),
        (
            Err(ValueError("Error message")),
            pytest.raises(
                UnwrapFailedError,
                match=re.escape(
                    "Called `.unwrap` on an [`Err`] value: ValueError('Error message'"
                ),
            ),
        ),
    ],
    ids=[
        "unwrap when Err value should raise UnwrapFailedError with string",
        "unwrap when Err value should raise UnwrapFailedError with exception",
    ],
)
def test_unwrap_err(result, expected):
    with expected:
        result.unwrap()


@pytest.mark.parametrize(
    "result, msg, expected",
    [
        (Err(10), "Something went wrong", 10),
    ],
    ids=[
        "expect_err when Err value should return error",
    ],
)
def test_expect_err_ok(result, msg, expected):
    assert result.expect_err(msg) == expected


@pytest.mark.parametrize(
    "result, msg, expected",
    [
        (
            Ok(10),
            "Testing expect error",
            pytest.raises(UnwrapFailedError, match="Testing expect error"),
        ),
    ],
    ids=[
        "expect_err when Ok value should raise UnwrapFailedError",
    ],
)
def test_expect_err_when_ok(result, msg, expected):
    with expected:
        result.expect_err(msg)


@pytest.mark.parametrize(
    "result, expected",
    [
        (Err(10), 10),
    ],
    ids=[
        "unwrap_err when Err value should return error",
    ],
)
def test_unwrap_err_ok(result, expected):
    assert result.unwrap_err() == expected


@pytest.mark.parametrize(
    "result, expected",
    [
        (
            Ok(10),
            pytest.raises(
                UnwrapFailedError,
                match=re.escape("Called `.unwrap_err` on an [`Ok`] value"),
            ),
        ),
    ],
    ids=[
        "unwrap_err when Ok value should raise UnwrapFailedError",
    ],
)
def test_unwrap_when_ok(result, expected):
    with expected:
        result.unwrap_err()


@pytest.mark.parametrize(
    "result, func, expected",
    [
        (Ok(2), sq_then_to_string, Ok("4")),
        (Err("Not a number"), sq_then_to_string, Err("Not a number")),
    ],
    ids=[
        "and_then when Ok value should call function",
        "and_then when Err value should return error",
    ],
)
def test_and_then(result, func, expected):
    assert result.and_then(func) == expected


@pytest.mark.parametrize(
    "result, func, expected",
    [
        (Ok(2), square, Ok(2)),
        (Ok(2), err, Ok(2)),
        (Err(3), square, Ok(9)),
        (Err(3), err, Err(3)),
    ],
    ids=[
        "or_else when Ok value should return value",
        "or_else when Ok value should return value",
        "or_else when Err value should call function",
        "or_else when Err value should call function",
    ],
)
def test_or_else(result, func, expected):
    assert result.or_else(func) == expected


@pytest.mark.parametrize(
    "result, default, expected",
    [
        (Ok(2), 42, 2),
        (Err("Something went wrong"), 42, 42),
    ],
    ids=[
        "unwrap_or when Ok value should return value",
        "unwrap_or when Err value should return default",
    ],
)
def test_unwrap_or(result, default, expected):
    assert result.unwrap_or(default) == expected


@pytest.mark.parametrize(
    "result, func, expected",
    [
        (Ok(2), count, 2),
        (Err("foo"), count, 3),
    ],
    ids=[
        "unwrap_or_else when Ok value should return value",
        "unwrap_or_else when Err value should call function",
    ],
)
def test_unwrap_or_else(result, func, expected):
    assert result.unwrap_or_else(func) == expected


def test_as_result() -> None:
    @Result.as_result
    def div(a: int, b: int) -> float:
        return a / b

    assert div(10, 2) == Ok(5.0)
    assert div(10, 0).map_err(str) == Err("division by zero")


def test_from_fn() -> None:
    def div(a: int, b: int) -> float:
        return a / b

    assert Result.from_fn(div, 10, 2) == Ok(5.0)
    assert Result.from_fn(div, 10, 0).map_err(str) == Err("division by zero")


def test_repr():
    assert repr(ok := Ok(123)) == "Ok(123)"
    assert ok == eval(repr(ok))
    assert repr(err := Err(-1)) == "Err(-1)"
    assert err == eval(repr(err))


def test_hash():
    assert len({Ok(1), Err("2"), Ok(1), Err("2")}) == 2
    assert len({Ok(1), Ok(2)}) == 2
    assert len({Ok("a"), Err("a")}) == 2


@pytest.mark.parametrize(
    "result, other, expected",
    [
        (Ok(1), 1, True),
        (Err(1), 1, True),
        (Ok(1), Ok(2), True),
        (Err("error"), Err("different error"), True),
        (Ok(1), Ok(1), False),
        (Err("error"), Err("error"), False),
    ],
    ids=[
        "ne when Ok compared to non-Result should return True",
        "ne when Err compared to non-Result should return True",
        "ne when Ok compared to different Ok should return True",
        "ne when Err compared to different Err should return True",
        "ne when Ok compared to same Ok should return False",
        "ne when Err compared to same Err should return False",
    ],
)
def test__ne__(result, other, expected):
    assert (result != other) == expected
