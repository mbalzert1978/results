from __future__ import annotations

import abc
import functools
import typing

T = typing.TypeVar("T")
E = typing.TypeVar("E")
F = typing.TypeVar("F")
U = typing.TypeVar("U")
P = typing.ParamSpec("P")


class ResultError(Exception):
    """Base result error."""


class UnwrapFailedError(ResultError):
    """Unwrap failed error."""


class Result(abc.ABC, typing.Generic[T, E]):
    @abc.abstractmethod
    def and_then(self, op: typing.Callable[[T], Result[U, E]]) -> Result[U, E]:
        """Calls `op` if the result is [`Ok`], otherwise returns the [`Err`] value of `self`.
        # Examples:

        >>> assert Result.Ok(2).and_then(sq_then_to_string) == Ok("4")
        >>> assert Result.Err("Not a number").and_then(sq_then_to_string) == Err("Not a number")
        """

    @staticmethod
    def as_result(fn: typing.Callable[P, T]) -> typing.Callable[P, Result[T, E]]:
        """Decorates a function so that it returns a `Result<T, E>` instead of `T`.
        # Examples:

        >>> @Result.as_result
        >>> def div(a: int, b: int) -> float:
        ...     return a / b
        >>> assert div(10, 2) == Result.Ok(5.0)
        >>> assert div(10, 0).map_err(str) == Result.Err("division by zero")
        """

        @functools.wraps(fn)
        def inner(*args: P.args, **kwargs: P.kwargs) -> Result[T, Exception]:
            try:
                result = fn(*args, **kwargs)
            except Exception as exc:
                return Result.Err(exc)
            else:
                return Result.Ok(result)

        return inner

    @abc.abstractmethod
    def err(self) -> typing.Optional[E]:
        """Converts from `Result<T, E>` to [`Optional<E>`].
        # Examples:

        >>> assert Result.Ok(2).err() is None
        >>> assert Result.Err("Nothing here").err() == "Nothing here"
        """

    @classmethod
    def Err(cls, inner_value: E) -> Result[typing.Any, E]:
        """Creates a new [`Err`] object from a given value.

        It is useful as a united way to create a new value from any container.
        # Examples:

        >>> from result import Result, Err
        >>> assert Result.from_failure(1) == Err(1)"""
        return Err(inner_value)

    @abc.abstractmethod
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

    @abc.abstractmethod
    def expect_err(self, msg: str) -> E:
        """Returns the contained [`Err`] value.
         Because this function may raise an exception, its use is generally discouraged.

        # Examples:

        >>> assert Result.Err(10).expect_err("Something went wrong") == 10
        >>> with pytest.raises(UnwrapFailedError, match="Testing expect error"):
        ...    Result.Ok(10).expect_err("Testing expect error")
        """

    @abc.abstractmethod
    def is_err(self) -> bool:
        """Returns `True` if the result is [`Err`].
        # Examples:

        >>> assert not Result.Ok(-3).is_err()
        >>> assert Result.Err("Something went wrong").is_err()
        """

    @abc.abstractmethod
    def is_err_and(self, fn: typing.Callable[[E], bool]) -> bool:
        """Returns `True` if the result is [`Err`] and the value inside of it matches a predicate.
        # Examples:

        >>> assert Result.Err(get_test_error()).is_err_and(lambda x: isinstance(x, ValueError))
        >>> assert not Result.Err(get_test_error()).is_err_and(lambda x: isinstance(x, str))
        >>> assert not Result.Ok(-3).is_err_and(lambda x: isinstance(x, ValueError))
        """

    @abc.abstractmethod
    def is_ok(self) -> bool:
        """Returns `True` if the result is [`Ok`].
        # Examples:

        >>> assert Result.Ok(10).is_ok()
        >>> assert not Result.Err("Something went wrong").is_ok()
        """

    @abc.abstractmethod
    def is_ok_and(self, fn: typing.Callable[[T], bool]) -> bool:
        """Returns `True` if the result is [`Ok`] and the value inside of it matches a predicate.
        # Examples:

        >>> assert Result.Ok(2).is_ok_and(lambda x: x > 1)
        >>> assert not Result.Ok(0).is_ok_and(lambda x: x > 1)
        >>> assert not Result.Err("Something went wrong").is_ok_and(lambda x: x > 1)
        """

    @abc.abstractmethod
    def map(self, fn: typing.Callable[[T], U]) -> Result[U, E]:
        """Maps a `Result<T, E>` to `Result<U, E>` by applying a function to a
         contained [`Ok`] value, leaving an [`Err`] value untouched.

        # Examples:

        >>> assert parse("5").map(lambda i: i * 2) == Ok(10.0)
        >>> assert parse("Nothing here").map(lambda i: i * 2) == Err("Invalid format")
        """

    @abc.abstractmethod
    def map_err(self, op: typing.Callable[[E], F]) -> Result[T, F]:
        """Maps a `Result<T, E>` to `Result<T, F>` by applying a function to a
         contained [`Err`] value, leaving an [`Ok`] value untouched.
        # Examples:

        >>> assert Result.Ok(5).map_err(str) == Ok(5)
        >>> assert Result.Err(10).map_err(str) == Err("10")
        """

    @abc.abstractmethod
    def map_or(self, op: typing.Callable[[T], U], default: U) -> U:
        """Returns the provided default (if [`Err`]), or
         applies a function to the contained value (if [`Ok`]).
        # Examples:

        >>> assert Result.Ok("foo").map_or(lambda v: len(v), 42) == 3
        >>> assert Result.Err("bar").map_or(lambda v: len(v), 42) == 42
        """

    @abc.abstractmethod
    def map_or_else(
        self,
        default: typing.Callable[[E], U],
        op: typing.Callable[[T], U],
    ) -> U:
        """Maps a Result<T, E> to U by applying fallback function default
         to a contained Err value, or function f to a contained Ok value.

        Caller needs to ensure that default fn can be called with the contained Err value.
        # Examples:

        >>> k = 21
        >>> assert Result.Ok("foo").map_or_else(lambda e: k * 2, lambda v: len(v)) == 3
        >>> assert Result.Err("bar").map_or_else(lambda e: k * 2, lambda v: len(v)) == 42
        """

    @abc.abstractmethod
    def ok(self) -> typing.Optional[T]:
        """Converts from `Result<T, E>` to [`Optional<T>`].
        # Examples:

        >>> assert Result.Ok(2).ok() == 2
        >>> assert Result.Err("Nothing here").ok() is None
        """

    @classmethod
    def Ok(cls, inner_value: T) -> Result[T, typing.Any]:
        """Creates a new [`Ok`] object from a given value.

        It is useful as a united way to create a new value from any container.
        # Examples:

        >>> from result import Result, Ok
        >>> assert Result.from_value(1) == Ok(1)"""
        return Ok(inner_value)

    @abc.abstractmethod
    def or_else(self, op: typing.Callable[[E], Result[T, E]]) -> Result[T, E]:
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

    @abc.abstractmethod
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

    @abc.abstractmethod
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

    @abc.abstractmethod
    def unwrap_or(self, default: T) -> T:
        """Returns the contained [`Ok`] value or a provided default.
        # Examples:

        >>> assert Result.Ok(2).unwrap_or(10) == 2
        >>> assert Result.Err("Nothing here").unwrap_or(10) == 10
        """

    @abc.abstractmethod
    def unwrap_or_else(self, op: typing.Callable[[E], T]) -> T:
        """Returns the contained [`Ok`] value or computes it from a closure.
        # Examples:

        >>> assert Result.Ok(2).unwrap_or_else(lambda x: 2 * x) == 2
        >>> assert Result.Err(3).unwrap_or_else(lambda x: 2 * x) == 6
        """


@typing.final
class Ok(Result[T, typing.Any]):
    __slots__ = ("_inner_value",)
    __match_args__ = ("_inner_value",)

    UNWRAP_ERROR_MESSAGE = "Called `.%s` on an [`Ok`] value: %s"

    def __iter__(self) -> typing.Iterator[T]:
        yield self._inner_value

    def __repr__(self) -> str:
        return f"{type(self).__name__}({self._inner_value!r})"

    def __hash__(self) -> int:
        return hash(self._inner_value) * 41

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Ok) and self._inner_value == other._inner_value

    def __init__(self, inner_value: T) -> None:
        self._inner_value = inner_value

    def and_then(self, op: typing.Callable[[T], Result[U, E]]) -> Result[U, E]:
        return op(self._inner_value)

    def err(self) -> typing.Optional[typing.Any]:
        return None

    def expect(self, msg: str) -> T:
        return self._inner_value

    def expect_err(self, msg: str) -> typing.NoReturn:
        raise UnwrapFailedError(msg)

    def is_err(self) -> typing.Literal[False]:
        return False

    def is_err_and(self, fn: typing.Callable[[E], bool]) -> bool:
        return not self.is_ok()

    def is_ok(self) -> typing.Literal[True]:
        return True

    def is_ok_and(self, fn: typing.Callable[[T], bool]) -> bool:
        return fn(self._inner_value)

    def map(self, fn: typing.Callable[[T], U]) -> Result[U, E]:
        return Result.Ok(fn(self._inner_value))

    def map_err(self, fn: typing.Callable[[E], F]) -> Result[U, F]:
        return Result.Ok(typing.cast(U, self._inner_value))

    def map_or(self, fn: typing.Callable[[T], U], default_value: U) -> U:
        return fn(self._inner_value)

    def map_or_else(
        self,
        default: typing.Callable[[E], U],
        op: typing.Callable[[T], U],
    ) -> U:
        return op(self._inner_value)

    def ok(self) -> typing.Optional[T]:
        return self._inner_value

    def or_else(self, op: typing.Callable[[E], Result[T, E]]) -> Result[T, E]:
        return Result.Ok(self._inner_value)

    def unwrap(self) -> T:
        return self._inner_value

    def unwrap_err(self) -> typing.NoReturn:
        msg = self.UNWRAP_ERROR_MESSAGE % ("unwrap_err", repr(self._inner_value))
        raise UnwrapFailedError(msg)

    def unwrap_or(self, default_value: T) -> T:
        return self._inner_value

    def unwrap_or_else(self, op: typing.Callable[[E], T]) -> T:
        return self._inner_value


@typing.final
class Err(Result[typing.Any, E]):
    __slots__ = ("_inner_value",)
    __match_args__ = ("_inner_value",)

    UNWRAP_ERROR_MESSAGE = "Called `.%s` on an [`Err`] value: %s"

    def __iter__(self) -> typing.Iterator[None]:
        yield None

    def __repr__(self) -> str:
        return f"Err({self._inner_value!r})"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Err) and self._inner_value == other._inner_value

    def __hash__(self) -> int:
        return hash(self._inner_value) * 41

    def __init__(self, inner_value: E) -> None:
        self._inner_value = inner_value

    def and_then(self, op: typing.Callable[[T], Result[U, E]]) -> Result[U, E]:
        return self

    def err(self) -> typing.Optional[E]:
        return self._inner_value

    def expect(self, msg: str) -> typing.NoReturn:
        raise UnwrapFailedError(msg)

    def expect_err(self, msg: str) -> E:
        return self._inner_value

    def is_err(self) -> typing.Literal[True]:
        return True

    def is_err_and(self, fn: typing.Callable[[E], bool]) -> bool:
        return fn(self._inner_value)

    def is_ok(self) -> typing.Literal[False]:
        return False

    def is_ok_and(self, fn: typing.Callable[[T], bool]) -> bool:
        return False

    def map(self, fn: typing.Callable[[T], U]) -> Result[U, E]:
        return self

    def map_err(self, fn: typing.Callable[[E], F]) -> Result[U, F]:
        return Result.Err(fn(self._inner_value))

    def map_or(self, fn: typing.Callable[[T], U], default_value: U) -> U:
        return default_value

    def map_or_else(
        self,
        default: typing.Callable[[E], U],
        op: typing.Callable[[T], U],
    ) -> U:
        return default(self._inner_value)

    def ok(self) -> typing.Optional[T]:
        return None

    def or_else(self, op: typing.Callable[[E], Result[T, E]]) -> Result[T, E]:
        return op(self._inner_value)

    def unwrap(self) -> typing.NoReturn:
        exc = UnwrapFailedError(
            self.UNWRAP_ERROR_MESSAGE % ("unwrap", repr(self._inner_value)),
        )
        if isinstance(self._inner_value, BaseException):
            exc.__cause__ = self._inner_value
            raise exc from self._inner_value
        raise exc

    def unwrap_err(self) -> E:
        return self._inner_value

    def unwrap_or(self, default_value: T) -> T:
        return default_value

    def unwrap_or_else(self, fn: typing.Callable[[E], T]) -> T:
        return fn(self._inner_value)
