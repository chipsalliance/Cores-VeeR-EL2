# Copyright (C) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import logging
import os
from xml.etree import ElementTree as ET

import nox

# nox quirk: in status.json, return code for failure is 0
# https://github.com/wntrblm/nox/blob/main/nox/sessions.py#L128C11-L128C11
nox.options.report = "status.json"
nox.options.reuse_existing_virtualenvs = True

# Test configuration
blockPath = "."
pipRequirementsPath = "requirements.txt"

# Coverage types to collect
coverageTypes = [
    "all",
    "branch",
    "toggle",
]


def isSimFailure(
    resultsFile="results.xml", testsuites_name="results", verbose=False, suppress_rc=False
):
    """
    Extract failure code from cocotb results.xml file
    Based on https://github.com/cocotb/cocotb/blob/master/bin/combine_results.py
    """
    rc = 0

    # Logging
    logger = logging.getLogger()
    logger.setLevel(logging.DEBUG)
    logHandler = logging.FileHandler(filename="parseResultsXML.log", mode="w", encoding="utf-8")
    logFormatter = logging.Formatter()
    logHandler.setFormatter(logFormatter)
    logger.addHandler(logHandler)
    logHandler.setLevel(logging.INFO)
    if verbose:
        logHandler.setLevel(logging.DEBUG)

    # Main
    result = ET.Element("testsuites", name=testsuites_name)
    logging.debug(f"Reading file {resultsFile}")
    tree = ET.parse(resultsFile)

    for ts in tree.iter("testsuite"):
        ts_name = ts.get("name")
        ts_package = ts.get("package")
        logging.debug(f"Testsuite name : {ts_name}, package : {ts_package}")
        use_element = None
        for existing in result:
            if existing.get("name") == ts.get("name") and existing.get("package") == ts.get(
                "package"
            ):
                use_element = existing
                break
        if use_element is None:
            result.append(ts)
        else:
            use_element.extend(list(ts))

    if verbose:
        ET.dump(result)

    for testsuite in result.iter("testsuite"):
        for testcase in testsuite.iter("testcase"):
            for failure in testcase.iter("failure"):
                rc = 1
                logging.info(
                    "Failure in testsuite: '{}' classname: '{}' testcase: '{}' with parameters '{}'".format(
                        testsuite.get("name"),
                        testcase.get("classname"),
                        testcase.get("name"),
                        testsuite.get("package"),
                    )
                )

    if suppress_rc:
        rc = 0
    logging.shutdown()
    return rc


def verify_block(session, blockName, testName, coverage=""):
    session.install("-r", pipRequirementsPath)
    testPath = os.path.join(blockPath, blockName)
    testNameXML = os.path.join(testName + ".xml")
    testNameXMLPath = os.path.join(testPath, testNameXML)
    testNameLog = os.path.join(testName + ".log")
    testNameLogPath = os.path.join(testPath, testNameLog)
    with open(testNameLogPath, "w") as testLog:
        session.run(
            "make",
            "-C",
            testPath,
            "all",
            "COVERAGE_TYPE=" + coverage,
            "MODULE=" + testName,
            "COCOTB_RESULTS_FILE=" + testNameXML,
            external=True,
            stdout=testLog,
            stderr=testLog,
        )
    # Prevent coverage.dat and test log from being overwritten
    if coverage != "":
        coveragePath = testPath
        coverageName = "coverage.dat"
        coverageNamePath = os.path.join(coveragePath, coverageName)
        newCoverageName = "coverage_" + testName + "_" + coverage + ".dat"
        newCoverageNamePath = os.path.join(coveragePath, newCoverageName)
        os.rename(coverageNamePath, newCoverageNamePath)
        newTestNameLog = testName + "_" + coverage + ".log"
        newTestNameLogPath = os.path.join(testPath, newTestNameLog)
        os.rename(testNameLogPath, newTestNameLogPath)
    # Add check from results.xml to notify nox that test failed
    isTBFailure = isSimFailure(resultsFile=testNameXMLPath)
    if isTBFailure:
        raise Exception("SimFailure: cocotb failed. See test logs for more information.")


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["pic"])
@nox.parametrize(
    "testName",
    [
        "test_reset",
        "test_clken",
        "test_config",
        "test_prioritization",
        "test_servicing",
    ],
)
@nox.parametrize("coverage", coverageTypes)
def pic_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["pic_gw"])
@nox.parametrize("testName", ["test_gateway"])
@nox.parametrize("coverage", coverageTypes)
def pic_gw_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["dec_tl"])
@nox.parametrize("testName", ["test_dec_tl"])
@nox.parametrize("coverage", "toggle")
def dec_tl_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["dma"])
@nox.parametrize(
    "testName",
    [
        "test_reset",
        "test_read",
        "test_write",
        "test_address",
        "test_ecc",
        "test_debug_read",
        "test_debug_write",
        "test_debug_address",
    ],
)
@nox.parametrize("coverage", coverageTypes)
def dma_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["ifu_compress"])
@nox.parametrize("testName", ["test_compress"])
@nox.parametrize("coverage", "toggle")  # No branches in the decompressor
def ifu_compress_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["exu_alu"])
@nox.parametrize(
    "testName",
    [
        "test_arith",
        "test_logic",
    ],
)
@nox.parametrize("coverage", coverageTypes)
def exu_alu_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["exu_mul"])
@nox.parametrize(
    "testName",
    [
        "test_mul",
    ],
)
@nox.parametrize("coverage", coverageTypes)
def exu_mul_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["exu_div"])
@nox.parametrize(
    "testName",
    [
        "test_div",
    ],
)
@nox.parametrize("coverage", coverageTypes)
def exu_div_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["iccm"])
@nox.parametrize(
    "testName",
    [
        "test_readwrite",
    ],
)
@nox.parametrize("coverage", coverageTypes)
def iccm_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["dccm"])
@nox.parametrize(
    "testName",
    [
        "test_readwrite",
    ],
)
@nox.parametrize("coverage", coverageTypes)
def dccm_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["lib_axi4_to_ahb"])
@nox.parametrize(
    "testName",
    [
        "test_axi",
        "test_axi_read_channel",
        "test_axi_write_channel",
    ],
)
@nox.parametrize("coverage", coverageTypes)
def lib_axi4_to_ahb_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["pmp"])
@nox.parametrize(
    "testName",
    [
        "test_xwr_access",
        "test_address_matching",
        "test_multiple_configs",
    ],
)
@nox.parametrize("coverage", coverageTypes)
def pmp_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session()
def isort(session: nox.Session) -> None:
    """Options are defined in pyproject.toml file"""
    session.install("isort")
    session.run("isort", ".")


@nox.session()
def flake8(session: nox.Session) -> None:
    """Options are defined in .flake8 file."""
    session.install("flake8")
    session.run("flake8", ".")


@nox.session()
def black(session: nox.Session) -> None:
    """Options are defined in pyproject.toml file"""
    session.install("black")
    session.run("black", ".")
