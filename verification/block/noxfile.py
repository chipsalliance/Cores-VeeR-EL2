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

# Used lint tools
lintTools = [
    "isort",  # config in pyproject.toml
    "black",  # config in pyproject.toml
    "flake8",  # config in .flake8
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
        "test_pending",
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
@nox.parametrize("blockName", ["dec_ib"])
@nox.parametrize("testName", ["test_dec_ib"])
@nox.parametrize("coverage", "toggle")
def dec_ib_verify(session, blockName, testName, coverage):
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
        "test_zbb",
        "test_zbs",
        "test_zbp",
        "test_zba",
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
@nox.parametrize("blockName", ["dcls"])
@nox.parametrize(
    "testName",
    [
        "test_lockstep",
    ],
)
@nox.parametrize("coverage", coverageTypes)
def dcls_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["lib_axi4_to_ahb"])
@nox.parametrize(
    "testName",
    [
        "test_axi",
        "test_axi_read_channel",
        "test_axi_read_channel_multiple",
        "test_axi_write_channel",
    ],
)
@nox.parametrize("coverage", coverageTypes)
def lib_axi4_to_ahb_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["lib_ahb_to_axi4"])
@nox.parametrize(
    "testName",
    [
        "test_write",
        "test_read",
    ],
)
@nox.parametrize("coverage", coverageTypes)
def lib_ahb_to_axi4_verify(session, blockName, testName, coverage):
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


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["pmp_random"])
@nox.parametrize(
    "testName",
    [
        "test_pmp_random",
    ],
)
@nox.parametrize("coverage", coverageTypes)
def pmp_random_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["dec_tlu_ctl"])
@nox.parametrize(
    "testName",
    [
        "test_dec_tl",
    ],
)
@nox.parametrize("coverage", coverageTypes)
def dec_tlu_ctl_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["dmi"])
@nox.parametrize(
    "testName",
    [
        "test_jtag_ir",
        "test_dmi_read_write",
    ],
)
@nox.parametrize("coverage", coverageTypes)
def dmi_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["lsu_tl"])
@nox.parametrize("testName", ["test_lsu_tl"])
@nox.parametrize("coverage", "toggle")
def lsu_tl_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(tags=["tests"])
@nox.parametrize("blockName", ["dec_pmp_ctl"])
@nox.parametrize("testName", ["test_dec_pmp_ctl"])
@nox.parametrize("coverage", "toggle")
def dec_pmp_ctl_verify(session, blockName, testName, coverage):
    verify_block(session, blockName, testName, coverage)


@nox.session(reuse_venv=True)
def lint(session: nox.Session) -> None:
    """Options are defined in pyproject.toml and .flake8 files"""
    session.install(*lintTools)
    session.run("isort", ".")
    session.run("black", ".")
    session.run("flake8", ".")


@nox.session()
def test_lint(session: nox.Session) -> None:
    session.install(*lintTools)
    session.run("isort", "--check", ".")
    session.run("black", "--check", ".")
    session.run("flake8", ".")
