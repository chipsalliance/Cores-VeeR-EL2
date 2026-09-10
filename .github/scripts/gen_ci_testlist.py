# SPDX-License-Identifier: Apache-2.0

import yaml
import itertools
import os
import glob
import argparse
import subprocess
import json

WORKFLOW_DIR = ".github/workflows"

def resolve_dynamic_value(val, file_path=""):
    """Dynamically resolves ${{ ... }} GitHub Actions output expressions using local helper scripts."""
    if not isinstance(val, str) or not val.startswith("${{"):
        return val

    try:
        if "needs.generate-config.outputs.test-types" in val:
            script = ".github/scripts/riscv_dv_parse_testlist.py"
            testlist = "tools/riscv-dv/testlist.yaml"
            if os.path.exists(script) and os.path.exists(testlist):
                return json.loads(subprocess.check_output(["python3", script, testlist]))
        elif "needs.generate-config.outputs.test-include-generate" in val:
            script = ".github/scripts/riscv_dv_matrix_include.py"
            if os.path.exists(script):
                return json.loads(subprocess.check_output(["python3", script, "generate"]))
        elif "needs.generate-config.outputs.test-include-run-custom" in val:
            script = ".github/scripts/riscv_dv_matrix_include.py"
            if os.path.exists(script):
                return json.loads(subprocess.check_output(["python3", script, "run-custom-tests"]))
        elif "needs.generate-config.outputs.test-include-run" in val:
            script = ".github/scripts/riscv_dv_matrix_include.py"
            if os.path.exists(script):
                return json.loads(subprocess.check_output(["python3", script, "run-tests"]))
        elif "needs.generate-config.outputs.test-exclude-run" in val:
            return [
                {"iss": "renode", "test": "riscv_illegal_instr_test"},
                {"iss": "renode", "test": "riscv_hint_instr_test"},
                {"iss": "renode", "test": "riscv_ebreak_test", "priv": "mu"},
                {"iss": "renode", "test": "riscv_ebreak_debug_mode_test", "priv": "mu"}
            ]
    except Exception as e:
        print(f"   ⚠️ Could not dynamically resolve {val}: {e}")

    return val

def generate_local_regression_script(simulator="vcs", workflow_file=None):
    generated_commands = []
    
    # 1. Verify directory exists
    if not os.path.exists(WORKFLOW_DIR):
        print(f"❌ ERROR: Directory '{WORKFLOW_DIR}' not found.")
        print("   Make sure you are running this script from the ROOT directory of your repository.")
        return

    if workflow_file:
        if not os.path.exists(workflow_file):
            fallback_path = os.path.join(WORKFLOW_DIR, workflow_file)
            if os.path.exists(fallback_path):
                workflow_file = fallback_path
            else:
                print(f"❌ ERROR: Workflow file '{workflow_file}' not found.")
                return
        workflow_files = [workflow_file]
    else:
        # 2. Find workflow files
        workflow_files = glob.glob(os.path.join(WORKFLOW_DIR, "test-*.yml"))
        
        if not workflow_files:
            print(f"❌ ERROR: No files matching 'test-*.yml' found in {WORKFLOW_DIR}.")
            return
            
        # Sort workflow files to put 'risc' related workflows at the very end
        workflow_files.sort(key=lambda x: (1 if "risc" in os.path.basename(x).lower() else 0, x))

    print(f"✅ Found {len(workflow_files)} test workflow files. Parsing matrices...")

    for file_path in workflow_files:
        with open(file_path, 'r') as f:
            try:
                workflow = yaml.safe_load(f)
            except Exception as e:
                print(f"   ⚠️ Skipping {file_path}: YAML parsing error: {e}")
                continue

        if not isinstance(workflow, dict):
            continue

        jobs = workflow.get('jobs', {})
        if not jobs:
            print(f"   ⚠️ No 'jobs' block found in {file_path}")
            continue

        for job_name, job_data in jobs.items():
            if not isinstance(job_data, dict):
                continue

            if 'strategy' in job_data and 'matrix' in job_data['strategy']:
                matrix = job_data['strategy']['matrix']
                if not isinstance(matrix, dict):
                    continue
                
                # Extract and resolve matrix components safely
                raw_base = {k: v for k, v in matrix.items() if k not in ('include', 'exclude')}
                base_matrix = {}
                for k, v in raw_base.items():
                    resolved_v = resolve_dynamic_value(v, file_path)
                    if isinstance(resolved_v, list):
                        base_matrix[k] = resolved_v
                    elif not any("${{" in str(x) for x in ([resolved_v] if not isinstance(resolved_v, list) else resolved_v)):
                        base_matrix[k] = [resolved_v]

                raw_excludes = resolve_dynamic_value(matrix.get('exclude', []), file_path)
                excludes = raw_excludes if isinstance(raw_excludes, list) else [raw_excludes]
                
                raw_includes = resolve_dynamic_value(matrix.get('include', []), file_path)
                includes = raw_includes if isinstance(raw_includes, list) else [raw_includes]

                if not base_matrix and not includes:
                    continue

                valid_combos = []

                if base_matrix:
                    # Generate Cartesian product of the base matrix
                    keys, values = zip(*base_matrix.items())
                    combinations = [dict(zip(keys, v)) for v in itertools.product(*values)]

                    # Filter out excluded combinations
                    for combo in combinations:
                        # Skip unresolved GitHub actions syntax which causes bash 'bad substitution' errors
                        if any("${{" in str(v) for v in combo.values()):
                            continue

                        is_excluded = False
                        for ex in excludes:
                            if isinstance(ex, dict):
                                # Check if all key-value pairs in the exclude rule match the combo
                                if all(str(combo.get(k)) == str(v) for k, v in ex.items()):
                                    is_excluded = True
                                    break
                        if not is_excluded:
                            valid_combos.append(combo)

                # Add explicitly included combinations
                for inc in includes:
                    if isinstance(inc, dict):
                        # Check for unresolved syntax in includes as well
                        if not any("${{" in str(v) for v in inc.values()):
                            valid_combos.append(inc)
                    elif isinstance(inc, str) and "${{" in inc:
                        # Unresolved dynamic include expression
                        continue
                    else:
                        print(f"   ⚠️ Skipping dynamic/unparseable include: {inc}")

                if not valid_combos:
                    continue

                # Format the bash commands
                print(f"   -> Extracted {len(valid_combos)} combinations from {os.path.basename(file_path)} (Job: {job_name})")
                generated_commands.append(f"\n# =========================================")
                generated_commands.append(f"# {os.path.basename(file_path)} - Job: {job_name}")
                generated_commands.append(f"# =========================================")
                
                for combo in valid_combos:
                    # Provide standard script parameters based on your bash script inputs
                    bus = combo.get('bus', 'axi')
                    if bus == 'axi4':
                        bus = 'axi'
                    elif bus == 'ahb_lite':
                        bus = 'ahb'
                    test = combo.get('test', 'hello_world')
                    coverage = combo.get('coverage', 'all')
                    priv = combo.get('priv', '1')
                    cache_waypack = combo.get('cache_waypack', '0')
                    extra_args = combo.get('tb_extra_args', '')
                    iss = combo.get('iss', 'spike')
                    version = combo.get('version', 'uvm')
                    
                    env_vars = job_data.get('env', {})
                    dcls_enable = env_vars.get('DCLS_ENABLE', combo.get('dcls_enable', '0'))

                    # DCLS_DELAY can come from matrix (delay/dcls_delay) or job env
                    dcls_delay = combo.get('delay', combo.get('dcls_delay', env_vars.get('DCLS_DELAY', '0')))
                    if str(dcls_delay).startswith("${{") or dcls_delay is None:
                        dcls_delay = '0'

                    # ICCM_ADDR_XOR and DCCM_WR_READBACK from env or matrix
                    iccm_addr_xor = env_vars.get('ICCM_ADDR_XOR', combo.get('iccm_addr_xor', '0'))
                    dccm_wr_readback = env_vars.get('DCCM_WR_READBACK', combo.get('dccm_wr_readback', '0'))

                    # Build the command string intelligently
                    env_prefix = ""
                    if str(dcls_enable) != '0':
                        env_prefix += f"DCLS_ENABLE={dcls_enable} "
                        if str(dcls_delay) != '':
                            env_prefix += f"DCLS_DELAY={dcls_delay} "
                    if str(iccm_addr_xor) == '1':
                        env_prefix += f"ICCM_ADDR_XOR={iccm_addr_xor} "
                    if str(dccm_wr_readback) == '1':
                        env_prefix += f"DCCM_WR_READBACK={dccm_wr_readback} "
                    if extra_args:
                        env_prefix += f"TB_EXTRA_ARGS='{extra_args}' "

                    config_str = ", ".join([f"{k}={v}" for k, v in combo.items()])
                    log_name = f"{os.path.basename(file_path)} ({job_name}) - {config_str}"
                    safe_log_name = log_name.replace('"', '\\"')

                    if "uarch" in os.path.basename(file_path):
                        test_dir = str(test).replace('block/', '')
                        args_dict = {'COVERAGE_TYPE': coverage}
                        for k, v in combo.items():
                            if k in ("tb_extra_args", "test", "coverage"):
                                continue
                            val = str(v).replace('block/', '')
                            args_dict[k.upper()] = val
                            if k == 'module':
                                args_dict['COCOTB_RESULTS_FILE'] = f"{val}.xml"
                        args = " ".join([f"{k}={v}" for k, v in args_dict.items()])
                        args_str = f" {args}" if args else ""
                        log_file = f"{test_dir}_{args_dict.get('MODULE', 'module')}.log"
                        cmd = f"{env_prefix}make -f $RV_ROOT/Makefile run_block_test TEST={test_dir} {args_str} SIMULATOR={simulator} SHELL=/bin/bash | tee {log_file}"
                        wrapped_cmd = f"{cmd}; if grep -q 'FAIL=0' {log_file} && grep -q 'TESTS=' {log_file}; then echo \"{safe_log_name}\" >> PASS; else echo \"{safe_log_name}\" >> FAIL; fi"
                    elif "riscv-dv" in os.path.basename(file_path):
                        if job_name == "generate-code":
                            cmd = f"{env_prefix}make -C tools/riscv-dv RISCV_DV_TEST={test} RISCV_DV_SIM={version} generate"
                        else:
                            cmd = f"{env_prefix}make -C tools/riscv-dv RISCV_DV_TEST={test} RISCV_DV_ISS={iss} RISCV_DV_PRIV={priv} COVERAGE={coverage} SIMULATOR={simulator} run"
                        wrapped_cmd = f"{cmd} && echo \"{safe_log_name}\" >> PASS || echo \"{safe_log_name}\" >> FAIL"
                    else:
                        cmd = (
                            f"{env_prefix}$RV_ROOT/.github/scripts/run_regression_test.sh "
                            f"./test_results {bus} {test} {coverage} {priv} {cache_waypack} {simulator}"
                        )
                        wrapped_cmd = f"{cmd} && echo \"{safe_log_name}\" >> PASS || echo \"{safe_log_name}\" >> FAIL"

                    generated_commands.append(wrapped_cmd)

    # Write to script
    output_script = "run_local_regression.sh"
    with open(output_script, 'w') as f:
        f.write("#!/bin/bash\n")
        f.write("export RV_ROOT=`pwd`\n")
        f.write("export PATH=/opt/verilator/bin:$PATH\n")
        f.write("TIMESTAMP=$(date +\"%Y%m%d_%H%M%S\")\n")
        f.write("TARGET_DIR=\"run_regress_$TIMESTAMP\"\n")
        f.write("mkdir -p \"$TARGET_DIR\"\n")
        f.write("cd \"$TARGET_DIR\"\n")
        f.write("\nrm -f PASS FAIL\n")
        f.write("touch PASS FAIL\n")
        if not generated_commands:
            f.write("\n# NO TESTS EXTRACTED. PLEASE CHECK PYTHON SCRIPT LOGS.\n")
        else:
            f.write("\n".join(generated_commands))
        
        f.write("\n\n# =========================================\n")
        f.write("# Regression Summary\n")
        f.write("# =========================================\n")
        f.write("{\n")
        f.write("echo \"\"\n")
        f.write("echo \"=========================================\"\n")
        f.write("echo \"Regression Summary:\"\n")
        f.write("echo \"=========================================\"\n")
        f.write("echo \"Passed tests: $(wc -l < PASS)\"\n")
        f.write("echo \"Failed tests: $(wc -l < FAIL)\"\n")
        f.write("echo \"=========================================\"\n")
        f.write("if [ -s FAIL ]; then\n")
        f.write("    echo \"The following tests failed:\"\n")
        f.write("    cat FAIL\n")
        f.write("else\n")
        f.write("    echo \"All tests passed!\"\n")
        f.write("fi\n")
        f.write("} | tee summary.log\n")
        f.write("if [ -s FAIL ]; then\n")
        f.write("    if [[ \"${BASH_SOURCE[0]}\" == \"${0}\" ]]; then exit 1; else return 1; fi\n")
        f.write("else\n")
        f.write("    if [[ \"${BASH_SOURCE[0]}\" == \"${0}\" ]]; then exit 0; else return 0; fi\n")
        f.write("fi\n")
        
    os.chmod(output_script, 0o755)
    print(f"\n✅ Done! Generated local regression script: {output_script}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate local regression script")
    parser.add_argument("--simulator", default="vcs", help="Simulator to use (default: vcs)")
    parser.add_argument("--workflow", default=None, help="Specific workflow file to parse (optional)")
    args = parser.parse_args()
    generate_local_regression_script(args.simulator, args.workflow)
