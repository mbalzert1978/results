from __future__ import annotations

import abc
import functools
from collections.abc import Callable, Iterator
from typing import TYPE_CHECKING, Any, Literal, NoReturn, cast, final

from .option import Null, Some

if TYPE_CHECKING:
    from .option import Option


class ResultError(Exception):
    """Base result error."""


class UnwrapFailedError(ResultError):
    """Unwrap failed error."""


class Result[T, E](abc.ABC):
    """
    `Result` is a type that represents either success ([`Ok`]) or failure ([`Err`]).
    """

    @abc.abstractmethod
    def and_then[U](self, op: Callable[[T], Result[U, E]]) -> Result[U, E]:
        """Calls `op` if the result is [`Ok`], otherwise returns the [`Err`] value of `self`.
        # Examples:

        >>> assert Result.Ok(2).and_then(sq_then_to_string) == Ok("4")
        >>> assert Result.Err("Not a number").and_then(sq_then_to_string) == Err("Not a number")
        """

    @staticmethod
    def as_result[**P](fn: Callable[P, T]) -> Callable[P, Result[T, Exception]]:
        """Decorates a function so that it returns a `Result<T, E>` instead of `T`.
        # Examples:

        >>> @Result.as_result
        >>> def div(a: int, b: int) -> float:
        ...     return a / b
        >>> assert div(10, 2) == Result.Ok(5.0)
        >>> assert div(10, 0).map_err(str) == Result.Err("division by zero")
        """

        # ponytail: from_fn is the single source of the catch rule
        @functools.wraps(fn)
        def inner(*args: P.args, **kwargs: P.kwargs) -> Result[T, Exception]:
            return Result.from_fn(fn, *args, **kwargs)

        return inner

    @staticmethod
    def from_fn[**P](
        fn: Callable[P, T], *args: P.args, **kwargs: P.kwargs
    ) -> Result[T, Exception]:
        try:
            result = fn(*args, **kwargs)
        except Exception as exc:
            return Err(exc)
        else:
            return Ok(result)

    @abc.abstractmethod
    def err(self) -> Option[E]:
        """Converts from `Result<T, E>` to [`Option<E>`].
        # Examples:
        """

    @abc.abstractmethod
    def expect(self, msg: str) -> T:
        """Returns the contained [`Ok`] value, consuming the `self` value.
        Raises an `UnwrapFailedError` with the provided message if the value is an [`Err`].
        """

    @abc.abstractmethod
    def expect_err(self, msg: str) -> E:
        """Returns the contained [`Err`] value, consuming the `self` value.
        Raises an `UnwrapFailedError` with the provided message if the value is an [`Ok`].
        """

    @abc.abstractmethod
    def is_err(self) -> bool:
        """Returns `True` if the result is an [`Err`] value."""

    @abc.abstractmethod
    def is_err_and(self, fn: Callable[[E], bool]) -> bool:
        """Returns `True` if the result is an [`Err`] and the value inside of it matches a predicate."""

    @abc.abstractmethod
    def is_ok(self) -> bool:
        """Returns `True` if the result is an [`Ok`] value."""

    @abc.abstractmethod
    def is_ok_and(self, fn: Callable[[T], bool]) -> bool:
        """Returns `True` if the result is an [`Ok`] and the value inside of it matches a predicate."""

    @abc.abstractmethod
    def map[U](self, fn: Callable[[T], U]) -> Result[U, E]:
        """Maps a `Result<T, E>` to `Result<U, E>` by applying a function to a contained [`Ok`] value,
        leaving an [`Err`] value untouched.
        """

    @abc.abstractmethod
    def map_err[F](self, op: Callable[[E], F]) -> Result[T, F]:
        """Maps a `Result<T, E>` to `Result<T, F>` by applying a function to a contained [`Err`] value,
        leaving an [`Ok`] value untouched.
        """

    @abc.abstractmethod
    def map_or[U](self, op: Callable[[T], U], default: U) -> U:
        """Returns the provided default result (if [`Err`]), or applies a function to the contained value (if [`Ok`])."""

    @abc.abstractmethod
    def map_or_else[U](self, default: Callable[[E], U], op: Callable[[T], U]) -> U:
        """Computes a default function result (if [`Err`]), or applies a function to the contained value (if [`Ok`])."""

    @abc.abstractmethod
    def ok(self) -> Option[T]:
        """Converts from `Result<T, E>` to [`Option<T>`]."""

    @abc.abstractmethod
    def or_else(self, op: Callable[[E], Result[T, E]]) -> Result[T, E]:
        """Returns the result if it is [`Ok`], otherwise calls `op` with the wrapped error and returns the result."""

    @abc.abstractmethod
    def unwrap(self) -> T:
        """Returns the contained [`Ok`] value, consuming the `self` value.
        Raises an `UnwrapFailedError` if the value is an [`Err`].
        """

    @abc.abstractmethod
    def unwrap_err(self) -> E:
        """Returns the contained [`Err`] value, consuming the `self` value.
        Raises an `UnwrapFailedError` if the value is an [`Ok`].
        """

    @abc.abstractmethod
    def unwrap_or(self, default: T) -> T:
        """Returns the contained [`Ok`] value or a provided default."""

    @abc.abstractmethod
    def unwrap_or_else(self, op: Callable[[E], T]) -> T:
        """Returns the contained [`Ok`] value or computes it from a closure."""


@final
class Ok[T](Result[T, Any]):
    __slots__ = ("_inner_value",)
    __match_args__ = ("_inner_value",)

    UNWRAP_ERROR_MESSAGE = "Called `.%s` on an [`Ok`] value: %s"

    def __iter__(self) -> Iterator[T]:
        yield self._inner_value

    def __repr__(self) -> str:
        return f"{type(self).__name__}({self._inner_value!r})"

    def __hash__(self) -> int:
        return hash(self._inner_value) * 41

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Ok) and self._inner_value == other._inner_value

    def __init__(self, inner_value: T) -> None:
        self._inner_value = inner_value

    def and_then[U, E](self, op: Callable[[T], Result[U, E]]) -> Result[U, E]:
        return op(self._inner_value)

    def err[E](self) -> Option[E]:
        return Null()

    def expect(self, msg: str) -> T:
        return self._inner_value

    def expect_err(self, msg: str) -> NoReturn:
        raise UnwrapFailedError(msg)

    def is_err(self) -> Literal[False]:
        return False

    def is_err_and[E](self, fn: Callable[[E], bool]) -> bool:
        return not self.is_ok()

    def is_ok(self) -> Literal[True]:
        return True

    def is_ok_and(self, fn: Callable[[T], bool]) -> bool:
        return fn(self._inner_value)

    def map[U, E](self, fn: Callable[[T], U]) -> Result[U, E]:
        return Ok(fn(self._inner_value))

    def map_err[U, E, F](self, fn: Callable[[E], F]) -> Result[U, F]:
        return Ok(cast(U, self._inner_value))

    def map_or[U](self, fn: Callable[[T], U], default_value: U) -> U:
        return fn(self._inner_value)

    def map_or_else[U, E](
        self,
        default: Callable[[E], U],
        op: Callable[[T], U],
    ) -> U:
        return op(self._inner_value)

    def ok(self) -> Option[T]:
        return Some(self._inner_value)

    def or_else[E](self, op: Callable[[E], Result[T, E]]) -> Result[T, E]:
        return Ok(self._inner_value)

    def unwrap(self) -> T:
        return self._inner_value

    def unwrap_err(self) -> NoReturn:
        msg = self.UNWRAP_ERROR_MESSAGE % ("unwrap_err", repr(self._inner_value))
        raise UnwrapFailedError(msg)

    def unwrap_or(self, default_value: T) -> T:
        return self._inner_value

    def unwrap_or_else[E](self, op: Callable[[E], T]) -> T:
        return self._inner_value


@final
class Err[E](Result[Any, E]):
    __slots__ = ("_inner_value",)
    __match_args__ = ("_inner_value",)

    UNWRAP_ERROR_MESSAGE = "Called `.%s` on an [`Err`] value: %s"

    def __iter__(self) -> Iterator[None]:
        yield None

    def __repr__(self) -> str:
        return f"Err({self._inner_value!r})"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Err) and self._inner_value == other._inner_value

    def __hash__(self) -> int:
        return hash(self._inner_value) * 41

    def __init__(self, inner_value: E) -> None:
        self._inner_value = inner_value

    def and_then[T, U](self, op: Callable[[T], Result[U, E]]) -> Result[U, E]:
        return self

    def err(self) -> Option[E]:
        return Some(self._inner_value)

    def expect(self, msg: str) -> NoReturn:
        raise UnwrapFailedError(msg)

    def expect_err(self, msg: str) -> E:
        return self._inner_value

    def is_err(self) -> Literal[True]:
        return True

    def is_err_and(self, fn: Callable[[E], bool]) -> bool:
        return fn(self._inner_value)

    def is_ok(self) -> Literal[False]:
        return False

    def is_ok_and[T](self, fn: Callable[[T], bool]) -> bool:
        return False

    def map[T, U](self, fn: Callable[[T], U]) -> Result[U, E]:
        return self

    def map_err[U, F](self, fn: Callable[[E], F]) -> Result[U, F]:
        return Err(fn(self._inner_value))

    def map_or[T, U](self, fn: Callable[[T], U], default_value: U) -> U:
        return default_value

    def map_or_else[T, U](
        self,
        default: Callable[[E], U],
        op: Callable[[T], U],
    ) -> U:
        return default(self._inner_value)

    def ok(self) -> Option[Any]:
        return Null()

    def or_else[T](self, op: Callable[[E], Result[T, E]]) -> Result[T, E]:
        return op(self._inner_value)

    def unwrap(self) -> NoReturn:
        exc = UnwrapFailedError(
            self.UNWRAP_ERROR_MESSAGE % ("unwrap", repr(self._inner_value)),
        )
        if isinstance(self._inner_value, BaseException):
            exc.__cause__ = self._inner_value
            raise exc from self._inner_value
        raise exc

    def unwrap_err(self) -> E:
        return self._inner_value

    def unwrap_or[T](self, default_value: T) -> T:
        return default_value

    def unwrap_or_else[T](self, fn: Callable[[E], T]) -> T:
        return fn(self._inner_value)
