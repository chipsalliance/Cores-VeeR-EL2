#!/usr/bin/env python3
import argparse
import re

# =============================================================================


def get_test_status(log_file):
    """
    Reads the simulation log. Looks for test status reported by the running
    firmware / the testbench itself.
    """
    with open(log_file, "r") as fp:
        for line in fp:
            line = line.strip()

            if "TEST_FAILED" in line:
                return -1
            if "TEST_PASSED" in line:
                return 0

    return 1


def get_tmr_events(log_file):
    """
    Parse the log, count reported TMR events
    """
    TIMESTAMP_EXPR = re.compile(r"^\[\s*(?P<ts>[0-9]+)(?:\s+(?P<unit>ns))?\s*\].*")

    events = {
        "core_0_faults": [],
        "core_1_faults": [],
        "core_2_faults": [],
        "fatal_faults": [],
        "recovery_started": [],
        "recovery_finished": [],
    }

    with open(log_file, "r") as fp:
        for line in fp:
            line = line.strip()

            # Attempt to get timestamp
            tstamp = None
            match = TIMESTAMP_EXPR.fullmatch(line)
            if match is not None:
                groups = match.groupdict()
                tstamp = float(groups["ts"])
                # TODO: Use time unit. Right now the testbench always reports
                # "ns" so assume the timestamps to be in nanoseconds

            if "Core 0 failed" in line:
                events["core_0_faults"].append(tstamp)
            if "Core 1 failed" in line:
                events["core_1_faults"].append(tstamp)
            if "Core 2 failed" in line:
                events["core_2_faults"].append(tstamp)

            if "TMR fatal fault" in line:
                events["fatal_faults"].append(tstamp)
            if "TMR recovery started" in line:
                events["recovery_started"].append(tstamp)
            if "TMR recovery finished" in line:
                events["recovery_finished"].append(tstamp)

    return events

# =============================================================================


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--expect-pass",
        action = "store_true",
        help = "Expect the test program to report pass"
    )
    parser.add_argument(
        "--expect-fail",
        action = "store_true",
        help = "Expect the test program to report fail"
    )
    parser.add_argument(
        "--expect-tmr-fatal",
        action = "store_true",
        help = "Expect one or more TMR fatal faults"
    )
    parser.add_argument(
        "--expect-no-tmr-fatal",
        action = "store_true",
        help = "Expect no TMR fatal faults"
    )
    parser.add_argument(
        "--expect-core-faults",
        type = int,
        nargs = "+",
        default = [],
        help = "Expect cores with the provided indices to fail"
    )
    parser.add_argument(
        "--expect-no-core-faults",
        type = int,
        nargs = "+",
        default = [],
        help = "Expect cores with the provided indices not to fail"
    )
    parser.add_argument(
        "--expect-tmr-recovery",
        action = "store_true",
        help = "Expect one or more TMR recovery procedures to happen"
    )
    parser.add_argument(
        "--expect-no-tmr-recovery",
        action = "store_true",
        help = "Expect no TMR recovery procedures to happen"
    )

    args = parser.parse_args()
    exitcode = 0

    SIM_LOG = "run.log"

    # Test status
    test_status = get_test_status(SIM_LOG)
    if args.expect_pass and test_status == -1:
        print("Expected the test to pass but it failed")
        exitcode = -1
    if args.expect_fail and test_status == 0:
        print("Expected the test to fail but it passed")
        exitcode = -1
    if (args.expect_pass or args.expect_fail) and test_status == 1:
        print("Cannot determine test status")
        exitcode = -1

    # TMR status
    events = get_tmr_events(SIM_LOG)

    if args.expect_tmr_fatal:
        count = len(events["fatal_faults"]) 
        if count == 0:
            print("Expected a TMR fatal fault but none happened")
            exitcode = -1
    if args.expect_no_tmr_fatal:
        count = len(events["fatal_faults"]) 
        if count != 0:
            print(f"Expected no TMR fatal faults but {count} happened")
            exitcode = -1

    for core_id in args.expect_core_faults:
        key = f"core_{core_id}_faults"
        count = len(events[key])
        if count == 0:
            print(f"Expected core {core_id} to fail but it didn't")
            exitcode = -1

    for core_id in args.expect_no_core_faults:
        key = f"core_{core_id}_faults"
        count = len(events[key])
        if count != 0:
            print(f"Expected core {core_id} not to fail but it did")
            exitcode = -1

    if args.expect_tmr_recovery:
        starts = len(events["recovery_started"])
        finishes = len(events["recovery_finished"])
        if starts == 0:
            print(f"Expected at least one TMR recovery but none happened")
            exitcode = -1
        if abs(starts - finishes) != 0:
            print(f"Mismatch in recovery start ({starts}) and finish ({finishes}) count")
            exitcode = -1

    if args.expect_no_tmr_recovery:
        starts = len(events["recovery_started"])
        finishes = len(events["recovery_finished"])
        if starts != 0:
            print(f"Expected no TMR recovery but it happened")
            exitcode = -1
        if abs(starts - finishes) != 0:
            print(f"Mismatch in recovery start ({starts}) and finish ({finishes}) count")
            exitcode = -1

    exit(exitcode)


if __name__ == "__main__":
    main()
