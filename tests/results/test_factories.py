import pytest

from results import Null, Option, Some


@pytest.mark.parametrize(
    "option, expected",
    [
        (Option.some(5), Some(5)),
        (Option.null(5), Null(5)),
    ],
    ids=[
        "Option.factories when some called should return Some instance with value",
        "Option.factories when none called should return Null instance with value",
    ],
)
def test_option_factories(option: Option, expected):
    assert option == expected
