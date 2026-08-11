import json
import random
import sys

if __name__ == "__main__":
    event_name, seed, sample_size, full_csv = sys.argv[1:5]
    exclude_csv = sys.argv[5] if len(sys.argv) > 5 else ""

    full_tests = full_csv.split(",")
    exclude = set(filter(None, exclude_csv.split(",")))
    sample_size = int(sample_size)

    if event_name == "pull_request":
        pool = [test for test in full_tests if test not in exclude]
        selected = sorted(random.Random(seed).sample(pool, min(sample_size, len(pool))))
    else:
        selected = full_tests

    print(json.dumps(selected))
