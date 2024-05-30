from typing import Any, Callable, Generic, Iterator, Optional, ParamSpec, TypeVar

from option import Option

T = TypeVar("T")
E = TypeVar("E")
U = TypeVar("U")
F = TypeVar("F")
N = TypeVar("N")
P = ParamSpec("P")

class ResultError(Exception):
    """Base result error."""

class UnwrapFailedError(ResultError):
    """Unwrap failed error."""

class Result(Generic[T, E]):
    """
    `Result` is a type that represents either success ([`Ok`]) or failure ([`Err`]).
    """
    def and_then(self, op: Callable[[T], Result[U, E]]) -> Result[U, E]:
        """Calls `op` if the result is [`Ok`], otherwise returns the [`Err`] value of `self`.
        # Examples:

        >>> assert Result.Ok(2).and_then(sq_then_to_string) == Ok("4")
        >>> assert Result.Err("Not a number").and_then(sq_then_to_string) == Err("Not a number")
        """
    @staticmethod
    def as_result(fn: Callable[P, T]) -> Callable[P, Result[T, E]]:
        """Decorates a function so that it returns a `Result<T, E>` instead of `T`.
        # Examples:

        >>> @Result.as_result
        >>> def div(a: int, b: int) -> float:
        ...     return a / b
        >>> assert div(10, 2) == Result.Ok(5.0)
        >>> assert div(10, 0).map_err(str) == Result.Err("division by zero")
        """
    def err(self) -> Optional[E]:
        """Converts from `Result<T, E>` to [`Optional<E>`].
        # Examples:

        >>> assert Result.Ok(2).err() is None
        >>> assert Result.Err("Nothing here").err() == "Nothing here"
        """

    @staticmethod
    def Err(inner_value: E) -> Result[Any, E]:
        """Creates a new [`Err`] object from a given value.

        It is useful as a united way to create a new value from any container.
        # Examples:

        >>> from result import Result, Err
        >>> assert Result.from_failure(1) == Err(1)"""
        return Err(inner_value)

    def expect(self, msg: str) -> T:
        """Returns the contained [`Ok`] value.
         Because this function may raise an exception, its use is generally discouraged.

        Instead, prefer to use pattern matching and handle the [`Err`] case explicitly,
         or call [`unwrap_or`], [`unwrap_or_else`], or [`unwrap_or_default`].

        # Examples:

        >>> assert Result.Ok(10).expect("Something went wrong") == 10
        >>> with pytest.raises(UnwrapFailedError, match="Something went wrong"):
        ...     Result.Err("Emergency failure").expect("Something went wrong")
        """

    def expect_err(self, msg: str) -> E:
        """Returns the contained [`Err`] value.
         Because this function may raise an exception, its use is generally discouraged.

        # Examples:

        >>> assert Result.Err(10).expect_err("Something went wrong") == 10
        >>> with pytest.raises(UnwrapFailedError, match="Testing expect error"):
        ...    Result.Ok(10).expect_err("Testing expect error")
        """

    def is_err(self) -> bool:
        """Returns `True` if the result is [`Err`].
        # Examples:

        >>> assert not Result.Ok(-3).is_err()
        >>> assert Result.Err("Something went wrong").is_err()
        """

    def is_err_and(self, fn: Callable[[E], bool]) -> bool:
        """Returns `True` if the result is [`Err`] and the value inside of it matches a predicate.
        # Examples:

        >>> assert Result.Err(get_test_error()).is_err_and(lambda x: isinstance(x, ValueError))
        >>> assert not Result.Err(get_test_error()).is_err_and(lambda x: isinstance(x, str))
        >>> assert not Result.Ok(-3).is_err_and(lambda x: isinstance(x, ValueError))
        """

    def is_ok(self) -> bool:
        """Returns `True` if the result is [`Ok`].
        # Examples:

        >>> assert Result.Ok(10).is_ok()
        >>> assert not Result.Err("Something went wrong").is_ok()
        """

    def is_ok_and(self, fn: Callable[[T], bool]) -> bool:
        """Returns `True` if the result is [`Ok`] and the value inside of it matches a predicate.
        # Examples:

        >>> assert Result.Ok(2).is_ok_and(lambda x: x > 1)
        >>> assert not Result.Ok(0).is_ok_and(lambda x: x > 1)
        >>> assert not Result.Err("Something went wrong").is_ok_and(lambda x: x > 1)
        """

    def map(self, fn: Callable[[T], U]) -> Result[U, E]:
        """Maps a `Result<T, E>` to `Result<U, E>` by applying a function to a
         contained [`Ok`] value, leaving an [`Err`] value untouched.

        # Examples:

        >>> assert parse("5").map(lambda i: i * 2) == Ok(10.0)
        >>> assert parse("Nothing here").map(lambda i: i * 2) == Err("Invalid format")
        """

    def map_err(self, op: Callable[[E], F]) -> Result[T, F]:
        """Maps a `Result<T, E>` to `Result<T, F>` by applying a function to a
         contained [`Err`] value, leaving an [`Ok`] value untouched.
        # Examples:

        >>> assert Result.Ok(5).map_err(str) == Ok(5)
        >>> assert Result.Err(10).map_err(str) == Err("10")
        """

    def map_or(self, op: Callable[[T], U], default: U) -> U:
        """Returns the provided default (if [`Err`]), or
         applies a function to the contained value (if [`Ok`]).
        # Examples:

        >>> assert Result.Ok("foo").map_or(lambda v: len(v), 42) == 3
        >>> assert Result.Err("bar").map_or(lambda v: len(v), 42) == 42
        """

    def map_or_else(
        self,
        default: Callable[[E], U],
        op: Callable[[T], U],
    ) -> U:
        """Maps a Result<T, E> to U by applying fallback function default
         to a contained Err value, or function f to a contained Ok value.

        Caller needs to ensure that default fn can be called with the contained Err value.
        # Examples:

        >>> k = 21
        >>> assert Result.Ok("foo").map_or_else(lambda e: k * 2, lambda v: len(v)) == 3
        >>> assert Result.Err("bar").map_or_else(lambda e: k * 2, lambda v: len(v)) == 42
        """

    def ok(self) -> Option[T, N]:
        """Converts from `Result<T, E>` to [`Option<T>`].
        # Examples:

        >>> assert Result.Ok(2).ok() == 2
        >>> assert Result.Err("Nothing here").ok() is None
        """

    @staticmethod
    def Ok(inner_value: T) -> Result[T, Any]:
        """Creates a new [`Ok`] object from a given value.

        It is useful as a united way to create a new value from any container.
        # Examples:

        >>> from result import Result, Ok
        >>> assert Result.from_value(1) == Ok(1)"""
        return Ok(inner_value)

    def or_else(self, op: Callable[[E], Result[T, E]]) -> Result[T, E]:
        """Calls `op` if the result is [`Err`], otherwise returns the [`Ok`] value of `self`.
        This function can be used for control flow based on result values.
        # Examples:

        >>> def sq(x: int) -> Result[int, int]:
        ...    return Result.Ok(x * x)
        >>> def err(x: int) -> Result[int, int]:
        ...    return Result.Err(x * x)

        >>> assert Result.Ok(2).or_else(sq).or_else(sq) == Ok(2)
        >>> assert Result.Ok(2).or_else(err).or_else(sq) == Ok(2)
        >>> assert Result.Err(3).or_else(sq).or_else(err) == Ok(9)
        >>> assert Result.Err(3).or_else(err).or_else(err) == Err(3)
        """

    def unwrap(self) -> T:
        """
        Returns the contained [`Ok`] value, consuming the `self` value.
         Because this function may raise an exception, its use is generally discouraged.

        Instead, prefer to use pattern matching and handle the [`Err`] case explicitly,
         or call [`unwrap_or`], [`unwrap_or_else`], or [`unwrap_or_default`].

        # Examples:

        >>> assert Result.Ok(10).unwrap() == 10
        >>> with pytest.raises(
        ...     UnwrapFailedError,
        ...     match=re.escape("Called `.unwrap` on an [`Err`] value: 'Emergency failure'"),
        ... ):
        ...     Result.Err("Emergency failure").unwrap()
        """

    def unwrap_err(self) -> E:
        """Returns the contained [`Err`] value.
         Because this function may raise an exception, its use is generally discouraged.

         Instead, prefer to use pattern matching and handle the [`Err`] case explicitly,
          or call [`unwrap_or`], [`unwrap_or_else`], or [`unwrap_or_default`].
        # Examples:

        >>> assert Result.Err(10).unwrap_err() == 10
        >>> with pytest.raises(UnwrapFailedError, match=re.escape("Called `.unwrap_err()` on an [`Ok`] value: 10")):
        ...    Result.Ok(10).unwrap_err()
        """

    def unwrap_or(self, default: T) -> T:
        """Returns the contained [`Ok`] value or a provided default.
        # Examples:

        >>> assert Result.Ok(2).unwrap_or(10) == 2
        >>> assert Result.Err("Nothing here").unwrap_or(10) == 10
        """

    def unwrap_or_else(self, op: Callable[[E], T]) -> T:
        """Returns the contained [`Ok`] value or computes it from a closure.
        # Examples:

        >>> assert Result.Ok(2).unwrap_or_else(lambda x: 2 * x) == 2
        >>> assert Result.Err(3).unwrap_or_else(lambda x: 2 * x) == 6
        """

class Ok(Result[T, Any]):
    """
    `Ok` is a subclass of `Result` that represents a successful outcome.

    Attributes:
        _inner_value (T): The value contained in the `Ok` result.
    """

    __slots__: tuple[str, ...]
    __match_args__: tuple[str, ...] = ("_inner_value",)

    def __iter__(self) -> Iterator[T]: ...
    def __repr__(self) -> str: ...
    def __hash__(self) -> int: ...
    def __eq__(self, other: object) -> bool: ...
    def __ne__(self, value: object) -> bool: ...
    def __init__(self, inner_value: T) -> None: ...

class Err(Result[Any, E]):
    """
    `Err` is a subclass of `Result` that represents a failure outcome.

    Attributes:
        _inner_value (E): The error value contained in the `Err` result.
    """

    __slots__: tuple[str, ...]
    __match_args__: tuple[str, ...] = ("_inner_value",)
    def __iter__(self) -> Iterator[None]: ...
    def __repr__(self) -> str: ...
    def __eq__(self, other: object) -> bool: ...
    def __ne__(self, value: object) -> bool: ...
    def __hash__(self) -> int: ...
    def __init__(self, inner_value: E) -> None: ...
