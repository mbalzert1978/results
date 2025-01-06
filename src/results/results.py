from __future__ import annotations

import abc
import functools
from collections.abc import Callable, Iterator
from typing import Any, Literal, NoReturn, cast, final


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

        @functools.wraps(fn)
        def inner(*args: P.args, **kwargs: P.kwargs) -> Result[T, Exception]:
            try:
                result = fn(*args, **kwargs)
            except Exception as exc:
                return Err(exc)
            else:
                return Ok(result)

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

    def __ne__(self, other: object) -> bool:
        return not self.__eq__(other)

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

    def __ne__(self, other: object) -> bool:
        return not self.__eq__(other)

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


class OptionError(Exception):
    """Base result error."""


class TransposeError(OptionError):
    """Transpose failed error."""


def Some[T](value: T) -> Option[T]:
    """
    Creates an `Option` instance that contains `Some` value.

    Examples:
    >>> assert Option.some(10) == Some(10)
    """
    return Option[T].some(value)


def Null[T]() -> Option[T]:
    """
    Creates an `Option` instance that contains a `Null` value.

    Examples:
    >>> assert Option.null("Error") == Null("Error")
    """
    return Option[T].none()


class Option[T: object]:
    __slots__ = ("_content",)
    __match_args__ = ("_content",)

    def __init__(self, content: T | None = None) -> None:
        self._content = content

    @staticmethod
    def from_fn[**P](
        fn: Callable[P, T], *args: P.args, **kwargs: P.kwargs
    ) -> Option[T]:
        """Turns a function so that it returns a `Option<T, N>` instead of `T | None`.

        Caller is responsible for ensuring that the function does not raise an exception.
        # Examples:

        >>> def get(a: int, b: int) -> float:
        ...     return a / b
        ...
        >>> assert Result.from_fn(div, 10, 2) == Result.Ok(5.0)
        >>> assert Result.from_fn(div, 10, 0).map_err(str) == Result.Err("division by zero")
        """
        return Null() if (result := fn(*args, **kwargs)) is None else Some(result)

    @staticmethod
    def as_option[**P](fn: Callable[P, T]) -> Callable[P, Option[T]]:
        """
        Decorates a function so that it returns a `Optional<T>` instead of `T`.

        # Examples:

        >>> @Option.as_option
        >>> def div(a: int, b: int) -> float:
        ...     return a / b
        >>> assert div(10, 2) == 5.0
        >>> assert div(10, 0) is None
        """

        @functools.wraps(fn)
        def inner(*args: P.args, **kwargs: P.kwargs) -> Option[T]:
            return Null() if (option := fn(*args, **kwargs)) is None else Some(option)

        return inner

    def __str__(self):
        return f"{self._content}"

    def __repr__(self) -> str:
        return f"Some({self._content!r})" if self._content is not None else "Null()"

    def __hash__(self) -> int:
        return hash(self._content) * 41

    def __eq__(self, other: object) -> bool:
        return isinstance(other, type(self)) and self._content == other._content

    def __ne__(self, other: object) -> bool:
        return not self.__eq__(other)

    def __iter__(self) -> Iterator[T | None]:
        yield self._content or None

    @classmethod
    def some(cls, content: T) -> Option[T]:
        """
        Creates an `Option` instance that contains `Some` value.

        Examples:
        >>> assert Option.some(10) == Some(10)
        """
        return cls(content)

    @classmethod
    def none(cls) -> Option[T]:
        """
        Creates an `Option` instance that contains a `Null` value.

        Examples:
        >>> assert Option.null("Error") == Null("Error")
        """
        return cls()

    def and_then[U](self, op: Callable[[T], Option[U]]) -> Option[U]:
        """Returns [`Null`] if the option is [`Null`], otherwise calls `op` with the
        wrapped value and returns the result.
        Some languages call this operation flatmap.
        # Examples:

        >>> err = "Not a number"
        >>> assert Some(2).and_then(sq_then_to_string) == Some("4")
        >>> assert Null(err).and_then(sq_then_to_string) == Null(err)
        """
        return op(self._content) if self._content is not None else self

    def expect(self, msg: str) -> T:
        """
        Returns the contained [`Some`] value, consuming the `self` value.

        Raises
        ---
            Panics if the value is a [`Null`] with a custom panic message provided by `msg`.
        # Examples:

        >>> msg = "Something went wrong"
        >>> assert Some(10).expect(msg) == 10
        >>> with pytest.raises(UnwrapFailedError, match=msg):
        ...     Null("Emergency failure").expect(msg)
        """
        if self._content is None:
            raise UnwrapFailedError(msg)
        return self._content

    def filter(self, predicate: Callable[[T], bool]) -> Option[T]:
        """
        Returns [`Null`] if the option is [`Null`], otherwise calls `predicate`
        with the wrapped value and returns:

        - [`Some(t)`] if `predicate` returns `true` (where `t` is the wrapped
          value), and
        - [`Null`] if `predicate` returns `false`.

        This function works similar to [`Iterator`]. You can imagine
        the `Option<T>` being an iterator over one or zero elements. `filter()`
        lets you decide which elements to keep.
        # Examples:

        >>> assert Some(10).filter(is_even) == Some(10)
        >>> assert Some(15).filter(is_even) == Null(None)
        >>> assert Null(10).filter(is_even) == Null(10)
        """
        return self if self._content is None or predicate(self._content) else Null()

    def is_some(self) -> bool:
        """
        Returns `true` if the option is a [`Some`] value.

        # Examples:

        >>> assert not Null(10).is_some()
        >>> assert Some(10).is_some()
        """
        return self._content is not None

    def is_some_and(self, op: Callable[[T], bool]) -> bool:
        """
        Returns `true` if the option is a [`Some`] and the value inside of it matches a predicate.

        # Examples:

        >>> assert Some(10).is_some_and(is_even)
        >>> assert not Some(15).is_some_and(is_even)
        >>> assert not Null("Something went wrong").is_some_and(is_even)
        """
        return self.is_some() and op(self._content)

    def is_none(self) -> bool:
        """
        Returns `true` if the option is a [`Null`] value.

        # Examples:

        >>> assert Null(10).is_null()
        >>> assert not Some(10).is_null()
        """
        return not self.is_some()

    def map[U](self, op: Callable[[T], U]) -> Option[U]:
        """
        Maps an `Option<T>` to `Option<U>` by applying a function to a contained value
         (if `Some`) or returns `Null` (if `Null`).

        # Examples:

        >>> assert Some(10).map(lambda i: i * 2) == Some(20)
        >>> assert Null("Nothing here").map(lambda i: i * 2) == Null("Nothing here")
        """
        return self if self._content is None else Some(op(self._content))

    def map_or[U](self, default: U, op: Callable[[T], U]) -> U:
        """
        Returns the provided default result (if `Null`), or applies a function to the contained value (if `Some`).

        # Examples:

        >>> assert Some("foo").map_or(42, lambda v: len(v)) == 3
        >>> assert Null("bar").map_or(42, lambda v: len(v)) == 42
        """
        return default if self._content is None else op(self._content)

    def map_or_else[U](self, default: Callable[[], U], op: Callable[[T], U]) -> U:
        """
        Computes a default function result (if `Null`), or
        applies a different function to the contained value (if `Some`).

        # Examples:

        >>> assert Some("foo").map_or_else(lambda: 42, lambda v: len(v)) == 3
        >>> assert Null("bar").map_or_else(lambda: 42, lambda v: len(v)) == 42
        """
        return default() if self._content is None else op(self._content)

    def or_(self, default: Option[T]) -> Option[T]:
        """
        Transforms the `Option<T>` into a [`Result<T, E>`], mapping [`Some(v)`] to
        [`Ok(v)`] and [`Null`] to [`Err(err())`].

        # Examples:

        >>> msg = "Something went wrong"
        >>> assert Some(10).ok_or_else(lambda: msg) == Result.Ok(10)
        >>> assert Null(10).ok_or_else(lambda: msg) == Result.Err(msg)
        """
        return default if self._content is None else self

    def or_else(self, op: Callable[[], Option[T]]) -> Option[T]:
        """
        Returns the option if it contains a value, otherwise calls `f` and
        returns the result.

        # Examples

        >>> assert Some(10).or_else(lambda: Some(20)) == Some(10)
        >>> assert Some(10).or_else(lambda: Null(20)) == Some(10)
        >>> assert Null(10).or_else(lambda: Some(20)) == Some(20)
        """
        return op() if self._content is None else self

    def ok_or[E](self, err: E) -> Result[T, E]:
        """
        Transforms the `Option<T>` into a [`Result<T, E>`], mapping [`Some(v)`] to
        [`Ok(v)`] and [`Null`] to [`Err(err)`].

        Examples:

        >>> msg = "Something went wrong"
        >>> assert Some(10).ok_or(msg) == Result.Ok(10)
        >>> assert Null(10).ok_or(msg) == Result.Err(msg)
        """
        return Ok(self._content) if self._content is not None else Err(err)

    def ok_or_else[E](self, op: Callable[[], E]) -> Result[T, E]:
        """
        Transforms the `Option<T>` into a [`Result<T, E>`], mapping [`Some(v)`] to
        [`Ok(v)`] and [`Null`] to [`Err(err())`].

        # Examples:

        >>> msg = "Something went wrong"
        >>> assert Some(10).ok_or_else(lambda: msg) == Result.Ok(10)
        >>> assert Null(10).ok_or_else(lambda: msg) == Result.Err(msg)
        """
        return Ok(self._content) if self._content is not None else Err(op())

    def transpose[E](self) -> Result[Option[T], E]:
        """
        Transposes an `Option` of a [`Result`] into a [`Result`] of an `Option`.

        Null will be mapped to:
        #### Ok(Null)
        Some(Ok(_)) and Some(Err(_)) will be mapped to:
        #### Ok(Some(_)) and Err(_).

        # Examples:

        >>> msg = "Something went wrong"
        >>> no_result = "No result"
        >>> assert Some(Result.Ok("foo")).transpose() == Result.Ok(Some("foo"))
        >>> assert Some(Result.Err(msg)).transpose() == Result.Err(msg)
        >>> assert Null(Result.Ok("foo")).transpose() == Result.Ok(Some(None))
        >>> assert Null(Result.Err(msg)).transpose() == Result.Ok(Some(None))
        >>> assert Some(no_result).transpose() == Result.Ok(Some(no_result))
        >>> assert Null(no_result).transpose() == Result.Ok(Some(None))
        """
        match self._content:
            case None:
                return Ok(Null())
            case Ok(value):
                return Ok(Some(value))
            case Err() as err:
                return err
            case _:
                return Ok(self)

    def unwrap(self) -> T:
        """
        Returns the contained [`Some`] value.

        Because this function may panic, its use is generally discouraged.
        Instead, prefer to use pattern matching and handle the [`Null`]
        case explicitly, or call [`unwrap_or`], [`unwrap_or_else`], or
        [`unwrap_or_default`].

        # Raises
            Raises UnwrapFailedError when the value equals None.

        # Examples

        >>> assert Some(10).unwrap() == 10
        >>> assert Null(10).unwrap() == 10
        Traceback (most recent call last):
            ...
            option.option.UnwrapFailedError: Called `.unwrap` on an [`Null`] value.

        """
        if self._content is None:
            raise UnwrapFailedError("Called `.unwrap` on an [`Null`] value.")
        return self._content

    def unwrap_or(self, default: T) -> T:
        """
        Returns the contained [`Some`] value or a provided default.

        # Examples

        >>> assert Some(10).unwrap_or(42) == 10
        >>> assert Null(10).unwrap_or(42) == 42
        """
        return self._content or default

    def unwrap_or_else(self, op: Callable[[], T]) -> T:
        """
        Returns the contained [`Some`] value or computes it from a closure.

        # Examples

        >>> assert Some(10).unwrap_or_else(lambda: 42) == 10
        >>> assert Null(10).unwrap_or_else(lambda: 42) == 42
        """
        return self._content or op()
