# Result Handling Library

This library provides a robust mechanism for handling operations that can result in success (`Ok`) or failure (`Err`). Inspired by Rust's `Result` type, it aims to facilitate error handling in a more functional programming style in Python.

## Features

- **Result Type**: Encapsulate successful outcomes with `Ok` and failures with `Err`.
- **Comprehensive API**: Methods for checking, transforming, and retrieving contained values or errors.
- **Functional Programming Friendly**: Supports `map`, `map_err`, `and_then`, and more to work with results without explicit error checking.
- **Option Type**: Provides `Some` and `Null` to handle optional values, similar to `Option` in Rust.
- **Error Handling**: Custom exceptions like `UnwrapFailedError` for robust error management.

## Classes and Methods

### Result

- **and_then**: Chains operations on `Ok` values.

  ```python
  >>> assert Ok(2).and_then(lambda n: Ok(str(n * n))) == Ok("4")
  >>> assert Err("Not a number").and_then(lambda n: Ok(str(n * n))) == Err("Not a number")
  ```

- **as_result**: Decorator to convert function return values to `Result`.

  ```python
  >>> @Result.as_result
  ... def div(a: int, b: int) -> float:
  ...     return a / b
  >>> assert div(10, 2) == Ok(5.0)
  >>> assert div(10, 0).map_err(str) == Err("division by zero")
  ```

- **from_fn**: Executes a function and returns a `Result`.

- **err, expect, expect_err**: Methods to handle and retrieve error values.

- **is_err, is_ok**: Check the state of the result.

- **map, map_err, map_or, map_or_else**: Transform contained values.

- **ok, or_else, unwrap, unwrap_err, unwrap_or, unwrap_or_else**: Retrieve values with error handling.

### Ok

- Represents a successful result.
- Methods to transform and retrieve the contained value.

### Err

- Represents a failed result.
- Methods to handle and transform the error value.

### Option

- **Some**: Represents a present value.

  ```python
  >>> assert Some(10).unwrap() == 10
  ```

- **Null**: Represents the absence of a value (takes no arguments).

  ```python
  >>> assert Null().unwrap_or(0) == 0
  ```

- **from_fn, as_option**: Methods to handle optional values.

## Error Handling

- **ResultError**: Base class for result-related errors.
- **UnwrapFailedError**: Raised when an unwrap operation fails.

## Project Structure

```text
├── .python-version
├── pyproject.toml
├── README.md
├── uv.lock
├── src
│   └── results
│       ├── __init__.py
│       ├── option.py
│       ├── py.typed
│       └── results.py
└── tests
    ├── __init__.py
    └── results
        ├── __init__.py
        ├── test_option.py
        ├── test_pattern_matching.py
        ├── test_public_api.py
        └── test_result.py
```
