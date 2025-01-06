# Result Handling Library

This library provides a robust mechanism for handling operations that can result in success (`Ok`) or failure (`Err`). Inspired by Rust's `Result` type, it aims to facilitate error handling in a more functional programming style in Python.

## Features

- **Result Type**: Encapsulate successful outcomes with `Ok` and failures with `Err`.
- **Comprehensive API**: Methods for checking, transforming, and retrieving contained values or errors.
- **Functional Programming Friendly**: Supports map, map_err, and_then, and more to work with results without explicit error checking.

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

- **result/**: Contains the implementation of the `Result`, `Ok`, and `Err` classes along with error handling utilities.
- **tests/**: Houses unit tests to ensure the reliability of the library's functionality.

## Installation

This project uses [Poetry](https://python-poetry.org/) for dependency management and packaging. To install the dependencies, run:

```bash
poetry install
```

## Running Tests

To run all unit tests and verify that everything is working as expected, use the following command:

```bash
poetry run pytest
```

## Usage

Here's a quick example of how to use the `Result` type in your code:

```python
from result import Err, Ok, Result


def divide(a: int, b: int) -> Result[float, str]:
    if b == 0:
        return Err("Division by zero")
    return Ok(a / b)


def add(a: int, b: int) -> Result[int, str]:
    if not isinstance((a, b), int):
        return Result.from_failure("Invalid type.")
    return Result.from_value(a + b)


@Result.decorator
def substract(a: int, b: int) -> int:
    return a - b


division = divide(10, 2)
addition = add(10, 2)
subtraction: Result[int, Exception] = substract(10, 2)

if division.is_ok():
    print(division.ok())
else:
    print(division.err())

if addition.is_ok():
    print(addition.ok())
else:
    print(addition.err())

if subtraction.is_ok():
    print(subtraction.ok())
else:
    print(subtraction.err())

```

## Contributing

Contributions are welcome! Please feel free to submit a pull request or open an issue if you have suggestions or encounter any problems.

## License

This project is licensed under the MIT License - see the LICENSE file for details.