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

cat <<EOF >> brda_filter.py
def filter(infile, outfile):
    out = open(outfile, 'w')

    with open(infile) as f:
        lines = f.readlines()
        n = 0

        while n < len(lines):
            hits = {}
            if 'BRDA' in lines[n]:
                data = lines[n].split(",")[2].split("_")
                lineno = lines[n].split(",")[0]
                typ = data[0]
                key = data[1]
                hit = int(data[2])
                val = int(lines[n].split(",")[3])

                hits[lineno] = {}
                hits[lineno][typ] = {}
                hits[lineno][typ][key] = {}
                hits[lineno][typ][key][0] = []
                hits[lineno][typ][key][1] = []
                hits[lineno][typ][key][val].append(hit)

                n += 1
                while lines[n].startswith(lineno):
                    lineno = lines[n].split(",")[0]
                    data = lines[n].split(",")[2].split("_")
                    typ = data[0]
                    key = data[1]
                    hit = int(data[2])
                    val = int(lines[n].split(",")[3])

                    if typ not in hits[lineno]:
                        hits[lineno][typ] = {}

                    if key not in hits[lineno][typ]:
                        hits[lineno][typ][key] = {}
                        hits[lineno][typ][key][0] = []
                        hits[lineno][typ][key][1] = []

                    if hit not in hits[lineno][typ][key][val]:
                        hits[lineno][typ][key][val].append(hit)
                    n += 1

                # normalize hits
                for h in hits:
                    for t in hits[h]:
                        for l in hits[h][t]:
                            for v in [0, 1]:
                                try:
                                    mi = min(hits[h][t][l][v])
                                    for i, k in enumerate(hits[h][t][l][v]):
                                        hits[h][t][l][v][i] -= mi
                                except ValueError:
                                    # allow empty lists (no hits or misses)
                                    pass

                new_hits = {}

                for h in hits:
                    for t in hits[h]:
                        for l in hits[h][t]:
                            for v in [0, 1]:
                                for k in hits[h][t][l][v]:
                                    if t not in new_hits:
                                       new_hits[t] = {}
                                    if not k in new_hits[t] or new_hits[t][k] != 1:
                                        new_hits[t][k] = v


                for t in new_hits.keys():
                    for k in sorted(new_hits[t].keys()):
                        if len(new_hits[t].keys()) > 1:
                            out.write(f"{lineno},0,{t}_{k},{new_hits[t][k]}\n")
                        else:
                            out.write(f"{lineno},0,{t},{new_hits[t][k]}\n")
            else:
                out.write(lines[n])
                n += 1

    out.close()

filter('coverage_branch_verilator.info',
       'coverage_branch_verilator_filtered.info')

filter('coverage_toggle_verilator.info',
       'coverage_toggle_verilator_filtered.info')
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
python3 .github/scripts/split_info.py line.info --branch > coverage_branch_verilator.info
python3 .github/scripts/split_info.py line.info --line > coverage_line_verilator.info

find . -type f -name 'coverage_*.info' -exec sed -i 's_^SF:.*Cores-VeeR-EL2/_SF:_g' {} \;

python3 preprocess.py coverage_line_verilator.info --filter "design/" > _coverage_line.info
python3 preprocess.py coverage_toggle_verilator.info --filter "design/" > _coverage_toggle.info
python3 preprocess.py coverage_branch_verilator.info --filter "design/" > _coverage_branch.info

cp _coverage_line.info coverage_line_verilator.info
cp _coverage_branch.info coverage_branch_verilator.info
cp _coverage_toggle.info coverage_toggle_verilator.info

python3 brda_filter.py
mv coverage_toggle_verilator.info coverage_toggle_verilator_orig.info_
mv coverage_toggle_verilator_filtered.info coverage_toggle_verilator.info

mv coverage_branch_verilator.info coverage_branch_verilator_orig.info_
mv coverage_branch_verilator_filtered.info coverage_branch_verilator.info

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
