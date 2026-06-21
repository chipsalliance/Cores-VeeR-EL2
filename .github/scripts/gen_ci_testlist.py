import yaml
import itertools
import os
import glob

WORKFLOW_DIR = ".github/workflows"

def generate_local_regression_script():
    generated_commands = []
    
    # 1. Verify directory exists
    if not os.path.exists(WORKFLOW_DIR):
        print(f"❌ ERROR: Directory '{WORKFLOW_DIR}' not found.")
        print("   Make sure you are running this script from the ROOT directory of your repository.")
        return

    # 2. Find workflow files
    workflow_files = glob.glob(os.path.join(WORKFLOW_DIR, "test-*.yml"))
    
    if not workflow_files:
        print(f"❌ ERROR: No files matching 'test-*.yml' found in {WORKFLOW_DIR}.")
        return
        
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
                
                # Extract matrix components safely
                base_matrix = {k: v for k, v in matrix.items() if k not in ('include', 'exclude')}
                
                # Fix: Ensure all values are treated as lists
                for k, v in base_matrix.items():
                    if not isinstance(v, list):
                        base_matrix[k] = [v]

                excludes = matrix.get('exclude', [])
                if not isinstance(excludes, list): excludes = [excludes]
                
                includes = matrix.get('include', [])
                if not isinstance(includes, list): includes = [includes]

                if not base_matrix:
                    continue

                # Generate Cartesian product of the base matrix
                keys, values = zip(*base_matrix.items())
                combinations = [dict(zip(keys, v)) for v in itertools.product(*values)]

                # Filter out excluded combinations
                valid_combos = []
                for combo in combinations:
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
                        valid_combos.append(inc)
                    else:
                        print(f"   ⚠️ Skipping dynamic/unparseable include: {inc}")

                # Format the bash commands
                print(f"   -> Extracted {len(valid_combos)} combinations from {os.path.basename(file_path)} (Job: {job_name})")
                generated_commands.append(f"\n# =========================================")
                generated_commands.append(f"# {os.path.basename(file_path)} - Job: {job_name}")
                generated_commands.append(f"# =========================================")
                
                for combo in valid_combos:
                    # Provide standard script parameters based on your bash script inputs
                    bus = combo.get('bus', 'axi')
                    test = combo.get('test', 'hello_world')
                    coverage = combo.get('coverage', 'all')
                    priv = combo.get('priv', '1')
                    cache_waypack = combo.get('cache_waypack', '0')
                    extra_args = combo.get('tb_extra_args', '')
                    
                    env_vars = job_data.get('env', {})
                    dcls_enable = env_vars.get('DCLS_ENABLE', '0')

                    # Build the command string intelligently
                    env_prefix = ""
                    if str(dcls_enable) != '0':
                        env_prefix += f"DCLS_ENABLE={dcls_enable} "
                    if extra_args:
                        env_prefix += f"TB_EXTRA_ARGS='{extra_args}' "

                    cmd = (
                        f"{env_prefix}.github/scripts/run_regression_test.sh "
                        f"./test_results {bus} {test} {coverage} {priv} {cache_waypack} vcs"
                    )
                    generated_commands.append(cmd)
                    
    # Write to script
    output_script = "run_local_regression.sh"
    with open(output_script, 'w') as f:
        f.write("#!/bin/bash\n")
        f.write("set -e\n")
        f.write("export RV_ROOT=`pwd`\n")
        f.write("export PATH=/opt/verilator/bin:$PATH\n")
        if not generated_commands:
            f.write("\n# NO TESTS EXTRACTED. PLEASE CHECK PYTHON SCRIPT LOGS.\n")
        else:
            f.write("\n".join(generated_commands))
        
    os.chmod(output_script, 0o755)
    print(f"\n✅ Done! Generated local regression script: {output_script}")

if __name__ == "__main__":
    generate_local_regression_script()
