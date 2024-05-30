from __future__ import annotations

import abc
import functools
import typing

from option import Null, Some

if typing.TYPE_CHECKING:
    from option import Option

T = typing.TypeVar("T")
E = typing.TypeVar("E")
F = typing.TypeVar("F")
N = typing.TypeVar("N")
U = typing.TypeVar("U")
P = typing.ParamSpec("P")


class ResultError(Exception):
    """Base result error."""


class UnwrapFailedError(ResultError):
    """Unwrap failed error."""


class Result(abc.ABC, typing.Generic[T, E]):
    @abc.abstractmethod
    def and_then(self, op: typing.Callable[[T], Result[U, E]]) -> Result[U, E]: ...

    @staticmethod
    def as_result(
        fn: typing.Callable[P, T],
    ) -> typing.Callable[P, Result[T, Exception]]:
        ...

        @functools.wraps(fn)
        def inner(*args: P.args, **kwargs: P.kwargs) -> Result[T, Exception]:
            try:
                result = fn(*args, **kwargs)
            except Exception as exc:
                return Err(exc)
            else:
                return Ok(result)

        return inner

    @abc.abstractmethod
    def err(self) -> typing.Optional[E]: ...

    @staticmethod
    def Err(inner_value: E) -> Result[typing.Any, E]:
        return Err(inner_value)

    @abc.abstractmethod
    def expect(self, msg: str) -> T: ...

    @abc.abstractmethod
    def expect_err(self, msg: str) -> E: ...

    @abc.abstractmethod
    def is_err(self) -> bool: ...

    @abc.abstractmethod
    def is_err_and(self, fn: typing.Callable[[E], bool]) -> bool: ...

    @abc.abstractmethod
    def is_ok(self) -> bool: ...

    @abc.abstractmethod
    def is_ok_and(self, fn: typing.Callable[[T], bool]) -> bool: ...

    @abc.abstractmethod
    def map(self, fn: typing.Callable[[T], U]) -> Result[U, E]: ...

    @abc.abstractmethod
    def map_err(self, op: typing.Callable[[E], F]) -> Result[T, F]: ...

    @abc.abstractmethod
    def map_or(self, op: typing.Callable[[T], U], default: U) -> U: ...

    @abc.abstractmethod
    def map_or_else(
        self,
        default: typing.Callable[[E], U],
        op: typing.Callable[[T], U],
    ) -> U: ...

    @abc.abstractmethod
    def ok(self) -> Option[T, N]: ...

    @staticmethod
    def Ok(inner_value: T) -> Result[T, typing.Any]:
        return Ok(inner_value)

    @abc.abstractmethod
    def or_else(self, op: typing.Callable[[E], Result[T, E]]) -> Result[T, E]: ...

    @abc.abstractmethod
    def unwrap(self) -> T: ...

    @abc.abstractmethod
    def unwrap_err(self) -> E: ...

    @abc.abstractmethod
    def unwrap_or(self, default: T) -> T: ...

    @abc.abstractmethod
    def unwrap_or_else(self, op: typing.Callable[[E], T]) -> T: ...


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

    def __ne__(self, other: object) -> bool:
        return not self.__eq__(other)

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
        return Ok(fn(self._inner_value))

    def map_err(self, fn: typing.Callable[[E], F]) -> Result[U, F]:
        return Ok(typing.cast(U, self._inner_value))

    def map_or(self, fn: typing.Callable[[T], U], default_value: U) -> U:
        return fn(self._inner_value)

    def map_or_else(
        self,
        default: typing.Callable[[E], U],
        op: typing.Callable[[T], U],
    ) -> U:
        return op(self._inner_value)

    def ok(self) -> typing.Optional[T]:
        return Some(self._inner_value)

    def or_else(self, op: typing.Callable[[E], Result[T, E]]) -> Result[T, E]:
        return Ok(self._inner_value)

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

    def __ne__(self, other: object) -> bool:
        return not self.__eq__(other)

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
        return Err(fn(self._inner_value))

    def map_or(self, fn: typing.Callable[[T], U], default_value: U) -> U:
        return default_value

    def map_or_else(
        self,
        default: typing.Callable[[E], U],
        op: typing.Callable[[T], U],
    ) -> U:
        return default(self._inner_value)

    def ok(self) -> typing.Optional[T]:
        return Null(None)

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
