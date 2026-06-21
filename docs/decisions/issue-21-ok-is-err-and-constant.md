# Decision Log — Issue #21 (`Ok.is_err_and`: replace self-predicate dispatch with `return False`)

## Context

`Ok.is_err_and` previously read:

```python
def is_err_and[E](self, fn: Callable[[E], bool]) -> bool:
    return not self.is_ok()
```

This is the only variant method in the `Result` family whose body calls another
predicate on `self` instead of returning a flat polymorphic constant.

## Decision

Replace the body with:

```python
def is_err_and[E](self, fn: Callable[[E], bool]) -> bool:
    return False
```

## Rationale

**D1 — Polymorphism over self-predicate dispatch.** `CLAUDE.md` and `CONTEXT.md`
require that behavior be selected by *variant identity* (the type), never by
querying `self` with another predicate inside the method body. `return not
self.is_ok()` is an indirect flag check: it calls `is_ok()` (which is
`Literal[True]` on `Ok`) just to negate it. The constant `return False`
expresses the same invariant directly and is consistent with the sibling
`Err.is_ok_and`, which already returns `False` directly.

**D2 — Behavior-neutral.** `Ok.is_ok()` is typed `Literal[True]`, so
`not self.is_ok()` is always `False`. The predicate `fn` is never called before
or after the change. No observable behavior differs for any caller.

**D3 — Predicate non-invocation is now explicitly specified.** Three new
parametrized cases in `test_is_err_and` use `lambda _: 1/0` as the predicate.
If the predicate were ever called, the test would raise `ZeroDivisionError` and
fail immediately. The cases cover an `int`, a falsy `int` (`0`), and an empty
`str` — confirming the rule holds for all `Ok` values, not just truthy ones.

**D4 — Scope boundary.** Only `Ok.is_err_and` is touched. The abstract stub on
`Result` and `Err.is_err_and` are unchanged. Annotation kept as `-> bool`
(not narrowed to `Literal[False]`) to match the sibling.
