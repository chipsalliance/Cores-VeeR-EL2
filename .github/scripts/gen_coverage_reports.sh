#!/bin/bash

#--------------#
#    LCOV
#--------------#
generate_coverage_reports(){
    # This function creates...
    # Args
    # OUTPUT_DIR - directory, where index.html will be placed
    # GIT_SHA - git revision
    OUTPUT_DIR=$1
    echo -e "${COLOR_WHITE}========== generate_coverage_reports =========${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}OUTPUT_DIR      = ${OUTPUT_DIR}${COLOR_CLEAR}"

    for info_file in `find . -name '*.info'`; do
        lcov --extract ${info_file} \*design\* -o ${info_file}
    done

    BRANCH_MERGED="./merged_branch.info"
    TOGGLE_MERGED="./merged_toggle.info"
    BRANCH_MERGED_SUMMMARY="./merged_branch.summary"
    TOGGLE_MERGED_SUMMMARY="./merged_toggle.summary"

    declare -A branch_files
    declare -A toggle_files

    FILES=`find . -name "coverage_*.info" -printf "%P\n"`

    for file in $FILES; do
        if [[ $file == *_branch.info ]]; then
            name_body=${file%_branch.info}
            branch_files[$name_body]=$file
        elif [[ $file == *_toggle.info ]]; then
            name_body=${file%_toggle.info}
            toggle_files[$name_body]=$file
        fi
    done

    for name_body in "${!branch_files[@]}"; do
        branch_file=${branch_files[$name_body]}
        toggle_file=${toggle_files[$name_body]}
        test_name=${name_body#coverage_}
        if [[ -f "$branch_file" ]]; then
            lcov -l $branch_file > "$name_body"_branch.summary
        fi
        if [[ -f "$toggle_file" ]]; then
            lcov -l $toggle_file > "$name_body"_toggle.summary
        fi
        mkdir -p $OUTPUT_DIR/all_"$test_name"/
        python3 $SELF_DIR/indexgen/genhtml.py "$name_body"_toggle.summary "$name_body"_branch.summary --output-dir $OUTPUT_DIR/all_"$test_name"/ --test-name "$test_name"
        cp $SELF_DIR/indexgen/dashboard-styles/gcov.css $OUTPUT_DIR/all_"$test_name"/
    done

    for branch_file in "${branch_files[@]}"; do
        lcov -a "$branch_file" -o "$BRANCH_MERGED"
    done
    if [[ -f $BRANCH_MERGED ]]; then
        lcov -l "$BRANCH_MERGED" > $BRANCH_MERGED_SUMMMARY
    fi

    for toggle_file in "${toggle_files[@]}"; do
        lcov -a "$toggle_file" -o "$TOGGLE_MERGED"
    done
    if [[ -f $TOGGLE_MERGED ]]; then
        lcov -l "$TOGGLE_MERGED" > $TOGGLE_MERGED_SUMMMARY
    fi

    mkdir -p $OUTPUT_DIR/all
    python3 $SELF_DIR/indexgen/genhtml.py "$TOGGLE_MERGED_SUMMMARY" "$BRANCH_MERGED_SUMMMARY" --output-dir $OUTPUT_DIR/all/ --test-name all
    cp $SELF_DIR/indexgen/dashboard-styles/gcov.css $OUTPUT_DIR/all/
}

#--------------#
#    Script
#--------------#
SELF_DIR="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"
. ${SELF_DIR}/common.inc.sh

# Get revision
GIT_SHA=`git describe --always`
if [ $? -ne 0 ]; then
    GIT_SHA="unknown"
fi
set -e
OUTPUT_DIR=report
mkdir -p ${OUTPUT_DIR}

echo -e "${COLOR_WHITE}========== gen_coverage_reports ==============${COLOR_CLEAR}"

generate_coverage_reports ${OUTPUT_DIR}

echo -e "${COLOR_WHITE}gen_coverage_reports ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
echo -e "${COLOR_WHITE}========== gen_coverage_reports ==============${COLOR_CLEAR}"
