# Result Handling Library

This library provides a robust mechanism for handling operations that can result in success (`Ok`) or failure (`Err`). Inspired by Rust's `Result` type, it aims to facilitate error handling in a more functional programming style in Python.

## Features

- **Result Type**: Encapsulate successful outcomes with `Ok` and failures with `Err`.
- **Comprehensive API**: Methods for checking, transforming, and retrieving contained values or errors.
- **Functional Programming Friendly**: Supports `map`, `map_err`, `and_then`, and more to work with results without explicit error checking.
- **Option Type**: Provides `Some` and `Null` to handle optional values, similar to `Option` in Rust.
- **Error Handling**: Custom exceptions like `UnwrapFailedError` and `TransposeError` for robust error management.

## Classes and Methods

### Result

- **and_then**: Chains operations on `Ok` values.
  ```python
  >>> assert Result.Ok(2).and_then(sq_then_to_string) == Ok("4")
  >>> assert Result.Err("Not a number").and_then(sq_then_to_string) == Err("Not a number")
  ```

- **as_result**: Decorator to convert function return values to `Result`.
  ```python
  >>> @Result.as_result
  >>> def div(a: int, b: int) -> float:
  ...     return a / b
  >>> assert div(10, 2) == Result.Ok(5.0)
  >>> assert div(10, 0).map_err(str) == Result.Err("division by zero")
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

- **Some**: Represents an optional value.
  ```python
  >>> assert Option.some(10) == Some(10)
  ```

- **Null**: Represents the absence of a value.
  ```python
  >>> assert Option.null("Error") == Null("Error")
  ```

- **from_fn, as_option**: Methods to handle optional values.

## Error Handling

- **ResultError**: Base class for result-related errors.
- **UnwrapFailedError**: Raised when an unwrap operation fails.
- **OptionError**: Base class for option-related errors.
- **TransposeError**: Raised when a transpose operation fails.

## Project Structure

```
├── .python-version
├── pyproject.toml
├── README.md
├── uv.lock
├── src
│   └── results
│       ├── __init__.py
│       ├── py.typed
│       ├── results.py
│       └── results.pyi
└── tests
    ├── __init__.py
    └── results
        ├── __init__.py
        ├── test_factories.py
        ├── test_option.py
        ├── test_pattern_matching.py
        └── test_result.py
```
