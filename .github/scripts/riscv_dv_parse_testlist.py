import sys
import os
from json import dumps
from yaml import load, Loader
from typing import Generator

RISCV_DV_HOME = "third_party/riscv-dv/"


def parse_yaml(path: str) -> Generator[str, None, None]:
    with open(path, 'rb') as fd:
        tests = load(fd, Loader=Loader)
    for test in tests:
        if 'import' in test:
            import_path = test['import'].split('/', 1)[1]
            yield from parse_yaml(RISCV_DV_HOME + import_path)
        elif 'test' in test:
            yield test['test']


if __name__ == "__main__":
    if len(sys.argv) == 2:
        testlist = RISCV_DV_HOME + f'target/{sys.argv[1]}/testlist.yaml'

        # check if testlist.yaml is provided by RISCV-DV; if not - it's a
        # custom testlist file not provided by RISCV-DV by default; treat the
        # script argument as full a path
        if not os.path.isdir(testlist):
            testlist = sys.argv[1]

        testlist = parse_yaml(testlist)
    else:
        testlist = parse_yaml(RISCV_DV_HOME + 'yaml/base_testlist.yaml')
    testlist = list(testlist)
    # remove, will cause incomplete sim, need customized RTL
    testlist.remove("riscv_csr_test")
    print(dumps(testlist))
