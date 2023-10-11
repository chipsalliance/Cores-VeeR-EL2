from yaml import load, Loader
from json import dumps
from itertools import product
import sys

RISCV_DV_TESTS = ['riscv_arithmetic_basic_test']


if __name__ == "__main__":
    if sys.argv[1].strip() == 'run':
        with open('.github/workflows/test-riscv-dv.yml', 'rb') as fd:
            run_tests = load(fd, Loader=Loader)['jobs']['run-tests']
        matrix = run_tests['strategy']['matrix']
        isses = matrix['iss']
        coverages = matrix['coverage']
        result = [{
            "test": test,
            "iss": iss,
            "coverage": coverage,
            "version": "pyflow",
        } for test, iss, coverage in product(RISCV_DV_TESTS, isses, coverages)]
        print(dumps(result))
    elif sys.argv[1].strip() == 'generate':
        print(dumps(
            [{
                "test": test,
                "version": "pyflow",
            } for test in RISCV_DV_TESTS]
        ))
    else:
        exit(1)
