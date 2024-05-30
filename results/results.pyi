from typing import Any, Callable, Generic, Iterator, Optional, ParamSpec, TypeVar

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

class OptionError(Exception):
    """Base result error."""

class TransposeError(OptionError):
    """Transpose failed error."""

class Option(Generic[T, N]):
    def and_then(self, f: Callable[[T], Option[U, N]]) -> Option[U, N]:
        """Returns [`Null`] if the option is [`Null`], otherwise calls `f` with the
        wrapped value and returns the result.
        Some languages call this operation flatmap.
        # Examples:

        >>> err = "Not a number"
        >>> assert Some(2).and_then(sq_then_to_string) == Some("4")
        >>> assert Null(err).and_then(sq_then_to_string) == Null(err)
        """
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

    def filter(self, predicate: Callable[[T], bool]) -> Option[T, N]:
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
    def is_null(self) -> bool:
        """
        Returns `true` if the option is a [`Null`] value.

        # Examples:

        >>> assert Null(10).is_null()
        >>> assert not Some(10).is_null()
        """
    def is_some(self) -> bool:
        """
        Returns `true` if the option is a [`Some`] value.

        # Examples:

        >>> assert not Null(10).is_some()
        >>> assert Some(10).is_some()
        """
    def is_some_and(self, f: Callable[[T], bool]) -> bool:
        """
        Returns `true` if the option is a [`Some`] and the value inside of it matches a predicate.

        # Examples:

        >>> assert Some(10).is_some_and(is_even)
        >>> assert not Some(15).is_some_and(is_even)
        >>> assert not Null("Something went wrong").is_some_and(is_even)
        """
    def map(self, f: Callable[[T], U]) -> Option[U, N]:
        """
        Maps an `Option<T>` to `Option<U>` by applying a function to a contained value
         (if `Some`) or returns `Null` (if `Null`).

        # Examples:

        >>> assert Some(10).map(lambda i: i * 2) == Some(20)
        >>> assert Null("Nothing here").map(lambda i: i * 2) == Null("Nothing here")
        """
    def map_or(self, default: U, f: Callable[[T], U]) -> U:
        """
        Returns the provided default result (if `Null`), or applies a function to the contained value (if `Some`).

        # Examples:

        >>> assert Some("foo").map_or(42, lambda v: len(v)) == 3
        >>> assert Null("bar").map_or(42, lambda v: len(v)) == 42
        """
    def map_or_else(self, default: Callable[[], U], f: Callable[[T], U]) -> U:
        """
        Computes a default function result (if `Null`), or
        applies a different function to the contained value (if `Some`).

        # Examples:

        >>> assert Some("foo").map_or_else(lambda: 42, lambda v: len(v)) == 3
        >>> assert Null("bar").map_or_else(lambda: 42, lambda v: len(v)) == 42
        """
    def ok_or(self, err: E) -> Result[T, E]:
        """
        Transforms the `Option<T>` into a [`Result<T, E>`], mapping [`Some(v)`] to
        [`Ok(v)`] and [`Null`] to [`Err(err)`].

        Examples:

        >>> msg = "Something went wrong"
        >>> assert Some(10).ok_or(msg) == Result.Ok(10)
        >>> assert Null(10).ok_or(msg) == Result.Err(msg)
        """
    def ok_or_else(self, err: Callable[[], E]) -> Result[T, E]:
        """
        Transforms the `Option<T>` into a [`Result<T, E>`], mapping [`Some(v)`] to
        [`Ok(v)`] and [`Null`] to [`Err(err())`].

        # Examples:

        >>> msg = "Something went wrong"
        >>> assert Some(10).ok_or_else(lambda: msg) == Result.Ok(10)
        >>> assert Null(10).ok_or_else(lambda: msg) == Result.Err(msg)
        """
    def or_(self, optb: Option[T, N]) -> Option[T, N]:
        """
        Returns the option if it contains a value, otherwise returns `optb`.

        # Examples

        >>> assert Some(10).or_(Some(20)) == Some(10)
        >>> assert Some(10).or_(Null(10)) == Some(10)
        >>> assert Null(10).or_(Some(20)) == Some(20)
        >>> assert Null(10).or_(Null(20)) == Null(10)
        """
    def or_else(self, f: Callable[[], Option[T, N]]) -> Option[T, N]:
        """
        Returns the option if it contains a value, otherwise calls `f` and
        returns the result.

        # Examples

        >>> assert Some(10).or_else(lambda: Some(20)) == Some(10)
        >>> assert Some(10).or_else(lambda: Null(20)) == Some(10)
        >>> assert Null(10).or_else(lambda: Some(20)) == Some(20)
        """
    def transpose(self) -> Result[Option[T, N], E]:
        """
        Transposes an `Option` of a [`Result`] into a [`Result`] of an `Option`.

        Null will be mapped to:
        #### Ok(Null)
        Some(Ok(_)) and Some(Err(_)) will be mapped to:
        #### Ok(Some(_)) and Err(_).

        # Examples:

        >>> msg = "Something went wrong"
        >>> no_rslt = "No result"
        >>> assert Some(Result.Ok("foo")).transpose() == Result.Ok(Some("foo"))
        >>> assert Some(Result.Err(msg)).transpose() == Result.Err(msg)
        >>> assert Null(Result.Ok("foo")).transpose() == Result.Ok(Some(None))
        >>> assert Null(Result.Err(msg)).transpose() == Result.Ok(Some(None))
        >>> assert Some(no_rslt).transpose() == Result.Ok(Some(no_rslt))
        >>> assert Null(no_rslt).transpose() == Result.Ok(Some(None))
        """
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
    def unwrap_or(self, default: T) -> T:
        """
        Returns the contained [`Some`] value or a provided default.

        # Examples

        >>> assert Some(10).unwrap_or(42) == 10
        >>> assert Null(10).unwrap_or(42) == 42
        """
    def unwrap_or_else(self, f: Callable[[], T]) -> T:
        """
        Returns the contained [`Some`] value or computes it from a closure.

        # Examples

        >>> assert Some(10).unwrap_or_else(lambda: 42) == 10
        >>> assert Null(10).unwrap_or_else(lambda: 42) == 42
        """
    @staticmethod
    def some(value: T) -> Option[T, N]:
        """
        Creates an `Option` instance that contains `Some` value.

        Examples:
        >>> assert Option.some(10) == Some(10)
        """
    @staticmethod
    def null(value: N) -> Option[T, N]:
        """
        Creates an `Option` instance that contains a `Null` value.

        Examples:
        >>> assert Option.null("Error") == Null("Error")
        """
    @staticmethod
    def as_option(fn: Callable[P, T]) -> Callable[P, Option[T, N]]:
        """
        Decorates a function so that it returns a `Optional<T>` instead of `T`.

        # Examples:

        >>> @Option.as_option
        >>> def div(a: int, b: int) -> float:
        ...     return a / b
        >>> assert div(10, 2) == 5.0
        >>> assert div(10, 0) is None
        """

class Some(Option[T, Any]):
    __slots__: tuple[str, ...]
    __match_args__: tuple[str, ...] = ("_inner_value",)
    def __iter__(self) -> Iterator[T | None]: ...
    def __repr__(self) -> str: ...
    def __hash__(self) -> int: ...
    def __eq__(self, other: object) -> bool: ...
    def __ne__(self, other: object) -> bool: ...
    def __init__(self, inner_value: T) -> None: ...

class Null(Option[Any, N]):
    __slots__: tuple[str, ...]
    __match_args__: tuple[str, ...] = ("_inner_value",)
    def __iter__(self) -> Iterator[N | None]: ...
    def __repr__(self) -> str: ...
    def __hash__(self) -> int: ...
    def __eq__(self, other: object) -> bool: ...
    def __ne__(self, other: object) -> bool: ...
    def __init__(self, inner_value: N) -> None: ...
