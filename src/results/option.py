from __future__ import annotations

import abc
import functools
from collections.abc import Callable, Iterator
from typing import TYPE_CHECKING, Literal, NoReturn, final

if TYPE_CHECKING:
    from .results import Result


class Option[T](abc.ABC):
    """
    `Option` is a sealed two-state type: a value is either present ([`Some`]) or
    absent ([`Null`]). Absence is encoded in the *type* (a separate [`Null`]
    variant), never in a stored sentinel value, and `None` is solely the absence
    sentinel, represented only by `Null()`. `Some(None)` is therefore forbidden
    and raises `ValueError` — as does any path that would wrap `None`
    (`map`/`transpose` producing `None`, `Ok(None).ok()`). Use `Null()` for an
    absent value, and `and_then` (`T -> Option[U]`) rather than `map` (`T -> U`)
    when a step may be absent. Behavior is selected by polymorphic dispatch on
    the two `@final` variants; the base class is abstract and cannot be
    instantiated directly.
    """

    @staticmethod
    def from_fn[**P](
        fn: Callable[P, T], *args: P.args, **kwargs: P.kwargs
    ) -> Option[T]:
        """Turns a function so that it returns a `Option<T>` instead of `T | None`.

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
            return Option.from_fn(fn, *args, **kwargs)

        return inner

    @classmethod
    def some(cls, content: T) -> Option[T]:
        """
        Creates an `Option` instance that contains `Some` value.

        Examples:
        >>> assert Option.some(10) == Some(10)
        """
        return Some(content)

    @classmethod
    def none(cls) -> Option[T]:
        """
        Creates an `Option` instance that contains a `Null` value.

        Examples:
        >>> assert Option.none() == Null()
        """
        return Null()

    @abc.abstractmethod
    def and_[U](self, optb: Option[U]) -> Option[U]:
        """Returns [`Null`] if the option is [`Null`], otherwise returns `optb`.

        This is the eager counterpart of [`and_then`]: the argument is evaluated
        unconditionally. Use [`and_then`] when computing the next option is expensive.

        # Examples:

        >>> assert Some(1).and_(Some(2)) == Some(2)
        >>> assert Some(1).and_(Null()) == Null()
        >>> assert Null().and_(Some(2)) == Null()
        >>> assert Null().and_(Null()) == Null()
        """

    @abc.abstractmethod
    def and_then[U](self, op: Callable[[T], Option[U]]) -> Option[U]:
        """Returns [`Null`] if the option is [`Null`], otherwise calls `op` with the
        wrapped value and returns the result.
        Some languages call this operation flatmap.
        # Examples:

        >>> assert Some(2).and_then(sq_then_to_string) == Some("4")
        >>> assert Null().and_then(sq_then_to_string) == Null()
        """

    @abc.abstractmethod
    def expect(self, msg: str) -> T:
        """
        Returns the contained [`Some`] value, consuming the `self` value.

        Raises
        ---
            Raises `UnwrapFailedError` with the provided message if the value is a [`Null`].
        # Examples:

        >>> msg = "Something went wrong"
        >>> assert Some(10).expect(msg) == 10
        >>> with pytest.raises(UnwrapFailedError, match=msg):
        ...     Null().expect(msg)
        """

    @abc.abstractmethod
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
        >>> assert Some(15).filter(is_even) == Null()
        >>> assert Null().filter(is_even) == Null()
        """

    @abc.abstractmethod
    def inspect(self, fn: Callable[[T], object]) -> Option[T]:
        """
        Calls `fn` with the contained value if [`Some`], returns `self` unchanged.
        If [`Null`], does nothing and returns `self`. The return value of `fn` is
        discarded; `inspect` is called purely for side effects (e.g. logging).

        # Examples:

        >>> log = []
        >>> assert Some(10).inspect(log.append) == Some(10)
        >>> assert log == [10]
        >>> assert Null().inspect(log.append) == Null()
        >>> assert log == [10]  # unchanged
        """

    @abc.abstractmethod
    def is_none(self) -> bool:
        """
        Returns `true` if the option is a [`Null`] value.

        # Examples:

        >>> assert Null().is_none()
        >>> assert not Some(10).is_none()
        """

    @abc.abstractmethod
    def is_none_or(self, fn: Callable[[T], bool]) -> bool:
        """
        Returns `true` if the option is [`Null`], or if it is [`Some`] and the
        value inside matches the predicate `fn`. The complement of `is_some_and`.

        # Examples:

        >>> assert Null().is_none_or(is_even)
        >>> assert Some(10).is_none_or(is_even)
        >>> assert not Some(15).is_none_or(is_even)
        """

    @abc.abstractmethod
    def map[U](self, op: Callable[[T], U]) -> Option[U]:
        """
        Maps an `Option<T>` to `Option<U>` by applying a function to a contained value
         (if `Some`) or returns `Null` (if `Null`).

        # Examples:

        >>> assert Some(10).map(lambda i: i * 2) == Some(20)
        >>> assert Null().map(lambda i: i * 2) == Null()
        """

    @abc.abstractmethod
    def map_or[U](self, default: U, op: Callable[[T], U]) -> U:
        """
        Returns the provided default result (if `Null`), or applies a function to the contained value (if `Some`).

        # Examples:

        >>> assert Some("foo").map_or(42, lambda v: len(v)) == 3
        >>> assert Null().map_or(42, lambda v: len(v)) == 42
        """

    @abc.abstractmethod
    def map_or_else[U](self, default: Callable[[], U], op: Callable[[T], U]) -> U:
        """
        Computes a default function result (if `Null`), or
        applies a different function to the contained value (if `Some`).

        # Examples:

        >>> assert Some("foo").map_or_else(lambda: 42, lambda v: len(v)) == 3
        >>> assert Null().map_or_else(lambda: 42, lambda v: len(v)) == 42
        """

    @abc.abstractmethod
    def or_(self, default: Option[T]) -> Option[T]:
        """
        Returns the option if it contains a value, otherwise returns `default`.

        # Examples:

        >>> assert Some(2).or_(Null()) == Some(2)
        >>> assert Null().or_(Some(100)) == Some(100)
        """

    @abc.abstractmethod
    def or_else(self, op: Callable[[], Option[T]]) -> Option[T]:
        """
        Returns the option if it contains a value, otherwise calls `f` and
        returns the result.

        # Examples

        >>> assert Some(10).or_else(lambda: Some(20)) == Some(10)
        >>> assert Some(10).or_else(lambda: Null()) == Some(10)
        >>> assert Null().or_else(lambda: Some(20)) == Some(20)
        """

    @abc.abstractmethod
    def ok_or[E](self, err: E) -> Result[T, E]:
        """
        Transforms the `Option<T>` into a [`Result<T, E>`], mapping [`Some(v)`] to
        [`Ok(v)`] and [`Null`] to [`Err(err)`].

        Examples:

        >>> msg = "Something went wrong"
        >>> assert Some(10).ok_or(msg) == Result.Ok(10)
        >>> assert Null().ok_or(msg) == Result.Err(msg)
        """

    @abc.abstractmethod
    def ok_or_else[E](self, op: Callable[[], E]) -> Result[T, E]:
        """
        Transforms the `Option<T>` into a [`Result<T, E>`], mapping [`Some(v)`] to
        [`Ok(v)`] and [`Null`] to [`Err(err())`].

        # Examples:

        >>> msg = "Something went wrong"
        >>> assert Some(10).ok_or_else(lambda: msg) == Result.Ok(10)
        >>> assert Null().ok_or_else(lambda: msg) == Result.Err(msg)
        """

    @abc.abstractmethod
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
        >>> assert Null().transpose() == Result.Ok(Null())
        >>> assert Some(no_result).transpose() == Result.Ok(Some(no_result))
        """

    @abc.abstractmethod
    def unwrap(self) -> T:
        """
        Returns the contained [`Some`] value.

        Because this function may panic, its use is generally discouraged.
        Instead, prefer to use pattern matching and handle the [`Null`]
        case explicitly, or call [`unwrap_or`], [`unwrap_or_else`].

        # Raises
            Raises UnwrapFailedError when the option is [`Null`].

        # Examples

        >>> assert Some(10).unwrap() == 10
        >>> Null().unwrap()
        Traceback (most recent call last):
            ...
            results.option.UnwrapFailedError: Called `.unwrap` on an [`Null`] value.

        """

    @abc.abstractmethod
    def unwrap_or(self, default: T) -> T:
        """
        Returns the contained [`Some`] value or a provided default.

        # Examples

        >>> assert Some(10).unwrap_or(42) == 10
        >>> assert Null().unwrap_or(42) == 42
        """

    @abc.abstractmethod
    def unwrap_or_else(self, op: Callable[[], T]) -> T:
        """
        Returns the contained [`Some`] value or computes it from a closure.

        # Examples

        >>> assert Some(10).unwrap_or_else(lambda: 42) == 10
        >>> assert Null().unwrap_or_else(lambda: 42) == 42
        """

    @abc.abstractmethod
    def xor(self, optb: Option[T]) -> Option[T]:
        """Returns [`Some`] iff exactly one of `self` and `optb` is [`Some`].

        Truth table::

            Some(a).xor(Null())    == Some(a)
            Null().xor(Some(b))    == Some(b)
            Some(a).xor(Some(b))   == Null()
            Null().xor(Null())     == Null()

        # Examples:

        >>> assert Some(1).xor(Null()) == Some(1)
        >>> assert Null().xor(Some(2)) == Some(2)
        >>> assert Some(1).xor(Some(2)) == Null()
        >>> assert Null().xor(Null()) == Null()
        """

    @abc.abstractmethod
    def zip[U](self, other: Option[U]) -> Option[tuple[T, U]]:
        """Zips `self` with another `Option`.

        If `self` is `Some(a)` and `other` is `Some(b)`, returns `Some((a, b))`.
        Otherwise returns `Null()`.

        Truth table::

            Some(a).zip(Some(b))   == Some((a, b))
            Some(a).zip(Null())    == Null()
            Null().zip(Some(b))    == Null()
            Null().zip(Null())     == Null()

        # Examples:

        >>> assert Some(1).zip(Some("x")) == Some((1, "x"))
        >>> assert Some(1).zip(Null()) == Null()
        >>> assert Null().zip(Some("x")) == Null()
        >>> assert Null().zip(Null()) == Null()
        """

    @abc.abstractmethod
    def unzip[A, B](self: Option[tuple[A, B]]) -> tuple[Option[A], Option[B]]:
        """Unzips an option containing a tuple of two values.

        If `self` is `Some((a, b))`, returns `(Some(a), Some(b))`.
        If `self` is `Null()`, returns `(Null(), Null())`.

        Invariante: Ist eine Tupelkomponente `None`, wirft `Some(None)` beim
        Konstruieren `ValueError` — der Guard in `Some.__init__` greift auch hier.

        # Examples:

        >>> assert Some((1, "x")).unzip() == (Some(1), Some("x"))
        >>> assert Null().unzip() == (Null(), Null())
        """


@final
class Some[T](Option[T]):
    __slots__ = ("_value",)
    __match_args__ = ("_value",)

    def __init__(self, value: T) -> None:
        # ponytail: None is absence, not a value — use Null() for absence and
        # and_then (T -> Option[U]) over map (T -> U). Runtime-only: PEP 695
        # generics can't express "T is not None".
        if value is None:
            raise ValueError("Some(None) is forbidden; use Null() for absence")
        self._value = value

    def __str__(self) -> str:
        return f"{self._value}"

    def __repr__(self) -> str:
        return f"Some({self._value!r})"

    def __hash__(self) -> int:
        return hash(self._value) * 41

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Some) and self._value == other._value

    def __iter__(self) -> Iterator[T]:
        yield self._value

    def and_[U](self, optb: Option[U]) -> Option[U]:
        return optb

    def and_then[U](self, op: Callable[[T], Option[U]]) -> Option[U]:
        return op(self._value)

    def expect(self, msg: str) -> T:
        return self._value

    def filter(self, predicate: Callable[[T], bool]) -> Option[T]:
        return self if predicate(self._value) else Null()

    def inspect(self, fn: Callable[[T], object]) -> Option[T]:
        fn(self._value)
        return self

    def is_none(self) -> Literal[False]:
        return False

    def is_none_or(self, fn: Callable[[T], bool]) -> bool:
        return fn(self._value)

    def is_some(self) -> Literal[True]:
        return True

    def is_some_and(self, op: Callable[[T], bool]) -> bool:
        return op(self._value)

    def map[U](self, op: Callable[[T], U]) -> Option[U]:
        return Some(op(self._value))

    def map_or[U](self, default: U, op: Callable[[T], U]) -> U:
        return op(self._value)

    def map_or_else[U](self, default: Callable[[], U], op: Callable[[T], U]) -> U:
        return op(self._value)

    def or_(self, default: Option[T]) -> Option[T]:
        return self

    def or_else(self, op: Callable[[], Option[T]]) -> Option[T]:
        return self

    def ok_or[E](self, err: E) -> Result[T, E]:
        # ponytail: deferred import breaks the results<->option cycle — Result
        # imports Some/Null at module top, so option may not import Result there.
        from .results import Ok

        return Ok(self._value)

    def ok_or_else[E](self, op: Callable[[], E]) -> Result[T, E]:
        # ponytail: deferred import — see ok_or.
        from .results import Ok

        return Ok(self._value)

    def transpose[E](self) -> Result[Option[T], E]:
        # ponytail: deferred import — see ok_or.
        from .results import Err, Ok

        match self._value:
            case Ok(value):
                return Ok(Some(value))
            case Err() as err:
                return err
            case _:
                return Ok(self)

    def unwrap(self) -> T:
        return self._value

    def unwrap_or(self, default: T) -> T:
        return self._value

    def unwrap_or_else(self, op: Callable[[], T]) -> T:
        return self._value

    def xor(self, optb: Option[T]) -> Option[T]:
        # ponytail: xor's dependence on optb's variant is intrinsic and is resolved
        # through optb's polymorphic dispatch, not a flag check — map_or returns
        # `default` (self) when optb is Null and `op(v)` (Null()) when optb is Some.
        return optb.map_or(self, lambda _: Null())

    def zip[U](self, other: Option[U]) -> Option[tuple[T, U]]:
        # ponytail: whether `other` is Some or Null is resolved through other.map —
        # no flag check or isinstance on self's variant; the dispatch lives in `other`.
        return other.map(lambda b: (self._value, b))

    def unzip[A, B](self: Some[tuple[A, B]]) -> tuple[Option[A], Option[B]]:
        a, b = self._value
        return (Some(a), Some(b))


@final
class Null[T](Option[T]):
    __slots__ = ()
    __match_args__ = ()

    def __str__(self) -> str:
        return "None"

    def __repr__(self) -> str:
        return "Null()"

    def __hash__(self) -> int:
        return hash(None) * 41

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Null)

    def __iter__(self) -> Iterator[None]:
        yield None

    def and_[U](self, optb: Option[U]) -> Option[U]:
        return Null()

    def and_then[U](self, op: Callable[[T], Option[U]]) -> Option[U]:
        return Null()

    def expect(self, msg: str) -> NoReturn:
        # ponytail: deferred import — Option reuses the Result-side error class.
        from .results import UnwrapFailedError

        raise UnwrapFailedError(msg)

    def filter(self, predicate: Callable[[T], bool]) -> Option[T]:
        return self

    def inspect(self, fn: Callable[[T], object]) -> Option[T]:
        return self

    def is_none(self) -> Literal[True]:
        return True

    def is_none_or(self, fn: Callable[[T], bool]) -> Literal[True]:
        return True

    def is_some(self) -> Literal[False]:
        return False

    def is_some_and(self, op: Callable[[T], bool]) -> Literal[False]:
        return False

    def map[U](self, op: Callable[[T], U]) -> Option[U]:
        return Null()

    def map_or[U](self, default: U, op: Callable[[T], U]) -> U:
        return default

    def map_or_else[U](self, default: Callable[[], U], op: Callable[[T], U]) -> U:
        return default()

    def or_(self, default: Option[T]) -> Option[T]:
        return default

    def or_else(self, op: Callable[[], Option[T]]) -> Option[T]:
        return op()

    def ok_or[E](self, err: E) -> Result[T, E]:
        # ponytail: deferred import — see Some.ok_or.
        from .results import Err

        return Err(err)

    def ok_or_else[E](self, op: Callable[[], E]) -> Result[T, E]:
        # ponytail: deferred import — see Some.ok_or.
        from .results import Err

        return Err(op())

    def transpose[E](self) -> Result[Option[T], E]:
        # ponytail: deferred import — see Some.ok_or.
        from .results import Ok

        return Ok(Null())

    def unwrap(self) -> NoReturn:
        # ponytail: deferred import — Option reuses the Result-side error class.
        from .results import UnwrapFailedError

        raise UnwrapFailedError("Called `.unwrap` on an [`Null`] value.")

    def unwrap_or(self, default: T) -> T:
        return default

    def unwrap_or_else(self, op: Callable[[], T]) -> T:
        return op()

    def xor(self, optb: Option[T]) -> Option[T]:
        return optb

    def zip[U](self, other: Option[U]) -> Option[tuple[T, U]]:
        return Null()

    def unzip[A, B](self: Null[tuple[A, B]]) -> tuple[Option[A], Option[B]]:
        return (Null(), Null())
