# !/bin/bash

# Set flag to exit the script on first error
set -e

# Check if RV_ROOT is set
if [ -z "$RV_ROOT" ]; then
  echo "Error: RV_ROOT is not set."
  exit 1
fi

# Prefix that will be added to all required macro/struct/module names
PREFIX="${PREFIX:-veer0_}"
# Path to directory where common_defines.vh, el2_param.vh, el2_pdef.vh and pd_defines.vh reside
DEFINES_PATH="${DEFINES_PATH:-${RV_ROOT}/snapshots/default}"
# Path to directory hierarchy where RTL sources reside
DESIGN_DIR="${DESIGN_DIR:-${RV_ROOT}/design}"

COMMON_DEFINES="$DEFINES_PATH/common_defines.vh"
EL2_PARAM="$DEFINES_PATH/el2_param.vh"
EL2_PDEF="$DEFINES_PATH/el2_pdef.vh"
PD_DEFINES="$DEFINES_PATH/pd_defines.vh"
EL2_DEF="$DESIGN_DIR/include/el2_def.sv"
EL2_IFU_IC_MEM="$DESIGN_DIR/ifu/el2_ifu_ic_mem.sv"

echo "Starting script with following settings:"
echo "PREFIX=$PREFIX"
echo "DEFINES_PATH=$DEFINES_PATH"
echo -e "DESIGN_DIR=$DESIGN_DIR\n"

# Define regex patterns for matching defines
DEFINES_REGEX="s/((\`define)|(\`ifndef)|(\`undef)) ([A-Z0-9_]+).*/\5/p"
DEFINES_REPLACE_REGEX="s/((\`define)|(\`ifndef)|(\`undef)) ([A-Z0-9_]+)/\1 "$PREFIX"\5/"
STRUCT_REPLACE_REGEX="s/el2_param_t/"$PREFIX"el2_param_t/g"
MODULES_REGEX="s/^module ([\`A-Za-z0-9_]+).*/\1/p"

# Extract unique defines from all sources
DEFINES="$(sed -nr "$DEFINES_REGEX" $COMMON_DEFINES $PD_DEFINES $EL2_IFU_IC_MEM | sort -ur)"

# Skip files that should not be processed
SKIP_DESIGN_FILES="el2_param.vh\|el2_pdef.vh\|common_defines.vh\|pd_defines.vh"
DESIGN_FILES="$(find $DESIGN_DIR -name "*.sv" -o -name "*.vh" -o -name "*.v" | grep -v $SKIP_DESIGN_FILES)"
DESIGN_FILES+=" $EXTRA_DESIGN_FILES"
MODULES="$(sed -nr "$MODULES_REGEX" $DESIGN_FILES | sort -ur)"

if [ "${DEBUG}" = "1" ]; then
	echo "DEBUG: DEFINES_REGEX=$DEFINES_REGEX"
	echo "DEBUG: DEFINES_REPLACE_REGEX=$DEFINES_REPLACE_REGEX"
	echo "DEBUG: STRUCT_REPLACE_REGEX=$STRUCT_REPLACE_REGEX"
	echo "DEBUG: MODULES_REGEX=$MODULES_REGEX"
	echo
	echo "DEBUG: DEFINES=$DEFINES"
	echo "DEBUG: DESIGN_FILES=$DESIGN_FILES"
	echo "DEBUG: MODULES=$MODULES"
	echo
fi

# Add prefix to macro names
OUTPUT_COMMON_DEFINES=$DEFINES_PATH/"$PREFIX"common_defines.vh
OUTPUT_PD_DEFINES=$DEFINES_PATH/"$PREFIX"pd_defines.vh
echo "Adding prefix to macro names in $OUTPUT_COMMON_DEFINES and $OUTPUT_PD_DEFINES"
sed -E "$DEFINES_REPLACE_REGEX" $COMMON_DEFINES >$OUTPUT_COMMON_DEFINES
sed -E "$DEFINES_REPLACE_REGEX" $PD_DEFINES >$OUTPUT_PD_DEFINES

# Add prefix to RV_RCG macros
RV_RCG_REPLACE_REGEX="s/^(\`define "${PREFIX}"\w+_RV_ICG )(\w+)/\1"${PREFIX}"\2/g"
sed -i -E "$RV_RCG_REPLACE_REGEX" $OUTPUT_COMMON_DEFINES

# Add prefix to VeeR config struct
OUTPUT_EL2_PARAM=$DEFINES_PATH/"$PREFIX"el2_param.vh
OUTPUT_EL2_PDEF=$DEFINES_PATH/"$PREFIX"el2_pdef.vh
echo "Adding prefix to VeeR config struct in $OUTPUT_EL2_PARAM and $OUTPUT_EL2_PDEF"

sed "$STRUCT_REPLACE_REGEX" "$EL2_PARAM" >$OUTPUT_EL2_PARAM
sed "$STRUCT_REPLACE_REGEX" "$EL2_PDEF" >$OUTPUT_EL2_PDEF
sed -i "$STRUCT_REPLACE_REGEX" $DESIGN_FILES

# Replace renamed macros in RTL sources
echo "Replacing renamed macros in RTL sources"
for DEFINE in $DEFINES; do
	sed -i "s/\`$DEFINE/\`"$PREFIX"$DEFINE/g" $DESIGN_FILES
	sed -i -E "s/((\`ifdef)|(\`ifndef)) $DEFINE/\1 "$PREFIX"$DEFINE/g" $DESIGN_FILES
done

# Replace include names in RTL sources
echo "Replacing include names in RTL sources"
sed -i "s/include \"el2_param.vh\"/include \""$PREFIX"el2_param.vh\"/g" $DESIGN_FILES
sed -i "s/include \"el2_pdef.vh\"/include \""$PREFIX"el2_pdef.vh\"/g" $DESIGN_FILES
sed -i "s/include \"common_defines.vh\"/include \""$PREFIX"common_defines.vh\"/g" $OUTPUT_PD_DEFINES

# Replace package name and its imports in RTL sources
echo "Replacing package name and its imports in RTL sources"
sed -i "s/import el2_pkg/import "$PREFIX"el2_pkg/g" $DESIGN_FILES
sed -i "s/package el2_pkg/package "$PREFIX"el2_pkg/g" $EL2_DEF

# Add prefix to all module names
echo "Adding prefix to all module names"
perl -pi -e "s/module \`?(?!${PREFIX})([A-Za-z0-9_]+)/module ${PREFIX}\1/g" $DESIGN_FILES

# Add prefix to all module instantiations
echo "Adding prefix to all module instantiations"
for MODULE in $MODULES; do
    # Exclude the prefix from the MODULE name if it already contains the prefix
    MODULE=$(echo $MODULE | perl -pe "s/${PREFIX}//")
    echo "Processing MODULE=$MODULE"
    perl -pi -e "s/(^|[^A-Za-z0-9_])(?<!${PREFIX})${MODULE}([^A-Za-z0-9_]+)/\1${PREFIX}${MODULE}\2/g" $DESIGN_FILES
done

# Remove old header files to avoid redefining their contents during elaboration
echo "Removing old header files"
rm -f $COMMON_DEFINES $EL2_PARAM $EL2_PDEF $PD_DEFINES

# Add prefix to el2_mem_if interface
echo "Adding prefix to el2_mem_if interface"
perl -pi -e "s/(?<!${PREFIX})el2_mem_if/"$PREFIX"el2_mem_if/g" $DESIGN_FILES

# prefix memory macro names in el2_ifu_ic_mem.sv
echo "Prefixing memory macro names in $EL2_IFU_IC_MEM"
perl -pi -e "s/(?<!${PREFIX})EL2_IC_TAG_PACKED_SRAM/${PREFIX}EL2_IC_TAG_PACKED_SRAM/g" $EL2_IFU_IC_MEM
perl -pi -e "s/(?<!${PREFIX})EL2_IC_TAG_SRAM/${PREFIX}EL2_IC_TAG_SRAM/g" $EL2_IFU_IC_MEM
perl -pi -e "s/(?<!${PREFIX})EL2_PACKED_IC_DATA_SRAM/${PREFIX}EL2_PACKED_IC_DATA_SRAM/g" $EL2_IFU_IC_MEM
perl -pi -e "s/(?<!${PREFIX})EL2_IC_DATA_SRAM/${PREFIX}EL2_IC_DATA_SRAM/g" $EL2_IFU_IC_MEM

# Add prefix to design file names
echo "Adding prefix to VeeR design file names"
for FILE_SRC in $DESIGN_FILES; do
    FILE_DIR="$(dirname -- "$(realpath "$FILE_SRC")")"
    FILE_NAME="$(basename "$FILE_SRC")"
    FILE_DEST="$FILE_DIR"/"$PREFIX""$FILE_NAME"
    echo "Renaming $FILE_SRC to $FILE_DEST"
    mv "$FILE_SRC" "$FILE_DEST"
done

echo "Script finished successfully"
