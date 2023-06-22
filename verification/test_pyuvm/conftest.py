import pytest

def type_checker(value):
    msg = "UsageError --coverage=<all, branch, toggle, functional>"
    if value not in ["all", "branch", "toggle", "functional"]:
        raise pytest.UsageError(msg)
    return value

def pytest_addoption(parser):
    parser.addoption(
        "--coverage", action="store", default="toggle", help="--coverage=<all, branch, toggle, functional>",type=type_checker
    )

@pytest.fixture
def coverage_opt(request):
    return request.config.getoption("--coverage")