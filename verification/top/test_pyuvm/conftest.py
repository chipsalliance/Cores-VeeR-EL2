import pytest

def type_checker_cov(value):
    msg = "UsageError --coverage=<all, branch, toggle, functional>"
    if value not in ["all", "branch", "toggle", "functional"]:
        raise pytest.UsageError(msg)
    return value

def type_checker_sim(value):
    msg = "UsageError --sim=<verilator, vcs>"
    if value not in ["verilator", "vcs"]:
        raise pytest.UsageError(msg)
    return value

def pytest_addoption(parser):
    parser.addoption(
        "--coverage", action="store", default="toggle", help="--coverage=<all, branch, toggle, functional>",type=type_checker_cov
    )
    parser.addoption(
        "--sim", action="store", default="verilator", help="--sim=<verilator, vcs>",type=type_checker_sim
    )
    parser.addoption(
        "--conf_params", action="store", default="-set build_axi4", help="--conf_params='...'"
    )

@pytest.fixture
def coverage_opt(request):
    return request.config.getoption("--coverage")

@pytest.fixture
def sim_opt(request):
    return request.config.getoption("--sim")

@pytest.fixture
def conf_params(request):
    return request.config.getoption("--conf_params")
