from typing import Any, Callable, Generic, Optional, ParamSpec, TypeVar, Union

T = TypeVar("T")
E = TypeVar("E")
U = TypeVar("U")
F = TypeVar("F")
P = ParamSpec("P")

class ResultError(Exception):
    """Base result error."""

class UnwrapFailedError(ResultError):
    """Unwrap failed error."""

class Result(Generic[T, E]):
    def and_then(self, op: Callable[[T], Result[U, E]]) -> Result[U, E]: ...
    @staticmethod
    def as_result(fn: Callable[P, T]) -> Callable[P, Result[T, E]]: ...
    def err(self) -> Optional[E]: ...
    @classmethod
    def Err(cls, inner_value: E) -> Result[Union[T, None], E]: ...
    def expect(self, msg: str) -> T: ...
    def expect_err(self, msg: str) -> E: ...
    def is_err(self) -> bool: ...
    def is_err_and(self, fn: Callable[[E], bool]) -> bool: ...
    def is_ok(self) -> bool: ...
    def is_ok_and(self, fn: Callable[[T], bool]) -> bool: ...
    def map(self, fn: Callable[[T], U]) -> Result[U, E]: ...
    def map_err(self, op: Callable[[E], F]) -> Result[T, F]: ...
    def map_or(self, op: Callable[[T], U], default: U) -> U: ...
    def map_or_else(self, default: Callable[[E], U], op: Callable[[T], U]) -> U: ...
    def ok(self) -> Optional[T]: ...
    @classmethod
    def Ok(cls, inner_value: T) -> Result[T, Union[E, None]]: ...
    def or_else(self, op: Callable[[E], Result[T, E]]) -> Result[T, E]: ...
    def unwrap(self) -> T: ...

class Ok(Result[T, Any]):
    def __init__(self, inner_value: T) -> None: ...
    def and_then(self, op: Callable[[T], Result[U, E]]) -> Result[U, E]: ...
    def err(self) -> Optional[E]: ...
    def expect(self, msg: str) -> T: ...
    def expect_err(self, msg: str) -> Any: ...
    def is_err(self) -> bool: ...
    def is_err_and(self, fn: Callable[[E], bool]) -> bool: ...
    def is_ok(self) -> bool: ...
    def is_ok_and(self, fn: Callable[[T], bool]) -> bool: ...
    def map(self, fn: Callable[[T], U]) -> Result[U, E]: ...
    def map_err(self, op: Callable[[E], F]) -> Result[T, F]: ...
    def map_or(self, op: Callable[[T], U], default: U) -> U: ...
    def map_or_else(self, default: Callable[[E], U], op: Callable[[T], U]) -> U: ...
    def ok(self) -> Optional[T]: ...
    def or_else(self, op: Callable[[E], Result[T, E]]) -> Result[T, E]: ...
    def unwrap(self) -> T: ...

class Err(Result[Any, E]):
    def __init__(self, inner_value: E) -> None: ...
    def and_then(self, op: Callable[[T], Result[U, E]]) -> Result[U, E]: ...
    def err(self) -> Optional[E]: ...
    def expect(self, msg: str) -> Any: ...
    def expect_err(self, msg: str) -> E: ...
    def is_err(self) -> bool: ...
    def is_err_and(self, fn: Callable[[E], bool]) -> bool: ...
    def is_ok(self) -> bool: ...
    def is_ok_and(self, fn: Callable[[T], bool]) -> bool: ...
    def map(self, fn: Callable[[T], U]) -> Result[U, E]: ...
    def map_err(self, op: Callable[[E], F]) -> Result[T, F]: ...
    def map_or(self, op: Callable[[T], U], default: U) -> U: ...
    def map_or_else(self, default: Callable[[E], U], op: Callable[[T], U]) -> U: ...
    def ok(self) -> Optional[T]: ...
    def or_else(self, op: Callable[[E], Result[T, E]]) -> Result[T, E]: ...
    def unwrap(self) -> Any: ...
