set -e
set -o pipefail

cat <<EOF >> preprocess.py
import sys
filter = None
in_file = False
if sys.argv[2] == "--filter":
  filter = sys.argv[3]
print("TN:verilator_coverage")
with open(sys.argv[1], 'r') as file:
  for line in file:
    line = line.replace("\n", "")
    if line[0:3] == "SF:":
        if filter == None or line.startswith("SF:%s" % filter):
            in_file = True
            print(line)
            continue
        else:
            in_file = False
            continue
    if not in_file:
        continue
    if "end_of_record" in line:
        in_file = False
        print(line)
        continue
    if line[0:1] == "#":
      print(line)
    elif line[0:3] == "DA:":
      data = line.split(",")
      line = "%s,%d" % (data[0], int(data[1]) > 0)
      print(line)
    elif line[0:5] == "BRDA:":
      data = line.split(",")
      line = "%s,%s,%s,%d" % (data[0],data[1],data[2], int(data[3]) > 0)
      print(line)
    else:
      print(line)
EOF

git clone https://github.com/antmicro/info-process
cd info-process
git checkout 7c030a4625049726e998065e227e06bac77519d8
PATH="`pwd`:$PATH"
cd ..

mkdir info_files
mv *.info info_files
tar acf verilator_coverage_single_data.tar.gz info_files
cd info_files
ls

ls *_toggle.info | xargs info-merge.py --output coverage_toggle_verilator.info
ls *_branch.info | xargs info-merge.py --output coverage_line_verilator.info

cp coverage_toggle_verilator.info ../
cp coverage_line_verilator.info ../

cd ../
rm -rf info_files

mv coverage_line_verilator.info line.info
python3 .github/scripts/split_info.py line.info --branch > coverage_branch_verilator.info
python3 .github/scripts/split_info.py line.info --line > coverage_line_verilator.info

find . -type f -name 'coverage_*.info' -exec sed -i 's_^SF:.*Cores-VeeR-EL2/_SF:_g' {} \;

python3 preprocess.py coverage_line_verilator.info --filter "design/" > _coverage_line.info
python3 preprocess.py coverage_toggle_verilator.info --filter "design/" > _coverage_toggle.info
python3 preprocess.py coverage_branch_verilator.info --filter "design/" > _coverage_branch.info

if [ -z "${DCLS_ENABLE}" ]; then
        # filter out lockstep module, if DCLS tests are not enabled
        python3 info-process/info-process.py --filter-out 'lockstep' $(realpath _coverage_toggle.info)
        python3 info-process/info-process.py --filter-out 'lockstep' $(realpath _coverage_line.info)
        python3 info-process/info-process.py --filter-out 'lockstep' $(realpath _coverage_branch.info)

        python3 info-process/info-process.py --filter-out 'el2_regfile_if' $(realpath _coverage_toggle.info)
        python3 info-process/info-process.py --filter-out 'el2_regfile_if' $(realpath _coverage_line.info)
        python3 info-process/info-process.py --filter-out 'el2_regfile_if' $(realpath _coverage_branch.info)
fi

cp _coverage_line.info coverage_line_verilator.info
cp _coverage_branch.info coverage_branch_verilator.info
cp _coverage_toggle.info coverage_toggle_verilator.info

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

info-process.py --set-block-ids coverage_toggle_verilator.info
info-process.py --add-two-way-toggles --add-missing-brda-entries coverage_toggle_verilator.info

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
