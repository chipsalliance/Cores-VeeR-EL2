set -e
set -o pipefail

cat <<EOF >> split.py
import sys
files = {}
active_file = None
with open(sys.argv[1], 'r') as file:
 for line in file:
   if line[0:1] == "#":
       continue
   elif line[0:3] == "SF:":
       active_file = line.replace("\n", "").split(":")[1]
       files[active_file] = {}
       files[active_file]["da"] = []
       files[active_file]["brda"] = []
       files[active_file]["brf"] = 0
       files[active_file]["brh"] = 0
   elif line[0:3] == "DA:":
       files[active_file]["da"].append(line.replace("\n", "").split(":")[1:])
   elif line[0:5] == "BRDA:":
       files[active_file]["brda"].append(line.replace("\n", "").split(":")[1:])
   elif line[0:4] == "BRF:":
       files[active_file]["brf"] = int(line.replace("\n", "").split(":")[1])
   elif line[0:4] == "BRH:":
       files[active_file]["brh"] = int(line.replace("\n", "").split(":")[1])
   elif "end_of_record" in line:
       active_file = None
if sys.argv[2] == "--branch":
  print("TN:verilator_coverage")
  for f in files:
     print("SF:%s" % f)
     for brda in files[f]["brda"]:
       brda_line = brda[0].split(",")[0]
       for da in files[f]["da"]:
          da_line = da[0].split(",")[0]
          if da_line == brda_line:
            print("DA:%s" % (",".join(da)))
            files[f]["da"].remove(da)
       print("BRDA:%s" % (",".join(brda)))
     print("end_of_record")
elif sys.argv[2] == "--line":
  print("TN:verilator_coverage")
  for f in files:
     print("SF:%s" % f)
     for da in files[f]["da"]:
       da_line = da[0].split(",")[0]
       found = False
       for brda in files[f]["brda"]:
          brda_line = brda[0].split(",")[0]
          if da_line == brda_line:
            found = True
       if not found:
         print("DA:%s" % (",".join(da)))
     print("end_of_record")
  sys.exit(0)
EOF

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

mkdir info_files
mv *.info info_files
cd info_files
git clone https://github.com/linux-test-project/lcov -b v2.3-beta
PATH="`pwd`/lcov/bin:$PATH"

ls *_toggle.info | xargs printf -- '-a %s\n' | xargs echo | awk '{ print "lcov "$0" --ignore-errors inconsistent --rc lcov_branch_coverage=1 -o coverage_toggle_verilator.info" }' | bash
ls *_branch.info | xargs printf -- '-a %s\n' | xargs echo | awk '{ print "lcov "$0" --ignore-errors inconsistent --rc lcov_branch_coverage=1 -o coverage_line_verilator.info" }' | bash

cp coverage_toggle_verilator.info ../
cp coverage_line_verilator.info ../

cd ../
rm -rf info_files

mv coverage_line_verilator.info line.info
python3 split.py line.info --branch > coverage_branch_verilator.info
python3 split.py line.info --line > coverage_line_verilator.info

find . -type f -name 'coverage_*.info' -exec sed -i 's_^SF:.*Cores-VeeR-EL2/_SF:_g' {} \;

python3 preprocess.py coverage_line_verilator.info --filter "design/" > _coverage_line.info
python3 preprocess.py coverage_toggle_verilator.info --filter "design/" > _coverage_toggle.info
python3 preprocess.py coverage_branch_verilator.info --filter "design/" > _coverage_branch.info

cp _coverage_line.info coverage_line_verilator.info
cp _coverage_branch.info coverage_branch_verilator.info
cp _coverage_toggle.info coverage_toggle_verilator.info

grep 'SF:' coverage_*.info | cut -d ":" -f 3 | sort | uniq > files.txt

export BRANCH=$GITHUB_HEAD_REF
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
