from yaml import load, Loader
from json import dumps
from itertools import product
import sys

RISCV_DV_TESTS = ['riscv_arithmetic_basic_test']


if __name__ == "__main__":
    arg1 = sys.argv[1].strip()

    # Entries with pyflow for every RISCV_DV_TESTS.
    # These are included in `generate` job matrix but it's also a base for `run*` jobs.
    entries = [{
        "test": test,
        "version": "pyflow",
    } for test in RISCV_DV_TESTS]

    # The argument passed needs to match the job name as variants are generated based on its matrix.
    if arg1.startswith('run'):
        with open('.github/workflows/test-riscv-dv.yml', 'rb') as fd:
            run_tests = load(fd, Loader=Loader)['jobs'][arg1]
        job_matrix = run_tests['strategy']['matrix']

        # Replicate matrix entries for all variants based on the job's matrix keys and values.
        #
        # For example, if the matrix only has `test`, `version` and `iss` keys, and `iss` values
        # are `renode` and `spike`, then `entries` will be doubled after `key=iss` iteration as
        # each entry will be replaced by two entries: one with additional `iss: renode` argument
        # and the other with additional `iss: spike`.
        for key in job_matrix.keys():
            if key in ['test', 'version', 'include', 'exclude']:
                continue
            entries = [{**entry, key: value} for entry, value in product(entries, job_matrix[key])]
        print(dumps(entries))
    elif arg1 == 'generate':
        print(dumps(entries))
    else:
        exit(1)
