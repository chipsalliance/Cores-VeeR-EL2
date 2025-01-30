set -e
set -o pipefail

python3 -m venv venv
. venv/bin/activate

pip install git+https://github.com/antmicro/info-process@12d2522f

mkdir info_files
mv *.info info_files
tar acf verilator_coverage_single_data.tar.gz info_files
cd info_files
ls

ls *_toggle.info | xargs info-process merge --output coverage_toggle_verilator.info
ls *_branch.info | xargs info-process merge --output coverage_line_verilator.info

cp coverage_toggle_verilator.info ../
cp coverage_line_verilator.info ../

cd ../
rm -rf info_files

mv coverage_line_verilator.info line.info
python3 .github/scripts/split_info.py line.info --branch > coverage_branch_verilator.info
python3 .github/scripts/split_info.py line.info --line > coverage_line_verilator.info
rm line.info

for INFO in *.info
do
    info-process transform --strip-file-prefix '.*Cores-VeeR-EL2/' --filter 'design/' --normalize-hit-counts $INFO

    # Filter out `lockstep` and `el2_regfile_if` modules if DCLS tests are not enabled
    if [ -z "${DCLS_ENABLE}" ]; then
        info-process transform --filter-out '(lockstep|el2_regfile_if)' $INFO
    fi
done

info-process transform --set-block-ids --add-two-way-toggles --add-missing-brda-entries coverage_toggle_verilator.info

grep 'SF:' coverage_*.info | cut -d ":" -f 3 | sort | uniq > files.txt

if [ -z "${GITHUB_HEAD_REF}" ]; then
        # We're in merge triggered run
        export BRANCH=$GITHUB_REF_NAME
else
        # We're in PR triggered run
        export BRANCH=$GITHUB_HEAD_REF
fi
export COMMIT=$GITHUB_SHA
{
        while read file
                do
                        if [ -f $file ]; then
                                echo "### FILE: $file"
                                cat "$file"
                        else
                                echo "### SKIPPING: $file"
                        fi
                done
} < files.txt > sources.txt

mkdir test_data
cp coverage_line_*.info coverage_toggle_*.info coverage_branch_* sources.txt test_data

# add logo
cp docs/dashboard-styles/assets/chips-alliance-logo-mono.svg test_data/logo.svg

# add config.json
echo -n '{ "datasets": { "verilator": { "line": "coverage_line_verilator.info", "branch": "coverage_branch_verilator.info", "toggle": "coverage_toggle_verilator.info" } }, "title": "VeeR EL2 coverage dashboard", "commit": "' > test_data/config.json
echo -n $COMMIT >> test_data/config.json
echo -n '", "branch": "' >> test_data/config.json
echo -n $BRANCH >> test_data/config.json
echo -n '", "repo": "cores-veer-el2", "timestamp": "' >> test_data/config.json
echo -n `date +"%Y-%m-%dT%H:%M:%S.%3N%z"` >> test_data/config.json
echo -n '" }' >> test_data/config.json

cat test_data/config.json

cd test_data
zip ../data.zip *
cd ..
