# !/bin/bash

# Prefix that will be added to all required macro/struct/module names
PREFIX="veer0_"
# Path to directory where common_defines.vh, el2_param.vh, el2_pdef.vh and pd_defines.vh reside
DEFINES_PATH="."
# Path to directory hierarchy where RTL sources reside
DESIGN_DIR="."

COMMON_DEFINES="$DEFINES_PATH/common_defines.vh"
EL2_PARAM="$DEFINES_PATH/el2_param.vh"
EL2_PDEF="$DEFINES_PATH/el2_pdef.vh"
PD_DEFINES="$DEFINES_PATH/pd_defines.vh"
EL2_DEF="$DESIGN_DIR/include/el2_def.sv"

DEFINES_REGEX="s/((\`define)|(\`ifndef)|(\`undef)) ([A-Z0-9_]+).*/\5/p"
DEFINES_REPLACE_REGEX="s/((\`define)|(\`ifndef)|(\`undef)) ([A-Z0-9_]+)/\1 "$PREFIX"\5/"
DEFINES="$(sed -nr "$DEFINES_REGEX" $COMMON_DEFINES $PD_DEFINES | sort -ur)"
SKIP_DESIGN_FILES="el2_param.vh\|el2_pdef.vh\|common_defines.vh\|pd_defines.vh"
DESIGN_FILES="$(find $DESIGN_DIR -name "*.sv" -o -name "*.vh" | grep -v $SKIP_DESIGN_FILES)"

# add prefix to macro names
sed -E "$DEFINES_REPLACE_REGEX" $COMMON_DEFINES > $DEFINES_PATH/"$PREFIX"common_defines.vh
sed -E "$DEFINES_REPLACE_REGEX" $PD_DEFINES > $DEFINES_PATH/"$PREFIX"pd_defines.vh

# replace renamed macros in RTL sources
for DEFINE in $DEFINES; do
    sed -i "s/\`$DEFINE/\`"$PREFIX"$DEFINE/g" $DESIGN_FILES
done

# add prefix to VeeR config struct
STRUCT_SED="s/el2_param_t/"$PREFIX"el2_param_t/g"
sed "$STRUCT_SED" "$EL2_PARAM" > $DEFINES_PATH/"$PREFIX"el2_param.vh
sed "$STRUCT_SED" "$EL2_PDEF" > $DEFINES_PATH/"$PREFIX"el2_pdef.vh
sed -i "$STRUCT_SED" $DESIGN_FILES

# replace include names in RTL sources
sed -i "s/include \"el2_param.vh\"/include \""$PREFIX"el2_param.vh\"/g" $DESIGN_FILES
sed -i "s/include \"el2_pdef.vh\"/include \""$PREFIX"el2_pdef.vh\"/g" $DESIGN_FILES

# replace package name and its imports in RTL sources
sed -i "s/import el2_pkg/import "$PREFIX"el2_pkg/g" $DESIGN_FILES
sed -i "s/package el2_pkg/package "$PREFIX"el2_pkg/g" $EL2_DEF

MODULES_REGEX="s/^module ([A-Za-z0-9_]+).*/\1/p"
MODULES="$(sed -nr "$MODULES_REGEX" $DESIGN_FILES | sort -ur)"

# add prefix to all module names
sed -i -E "s/module ([A-Za-z0-9_]+)/module "$PREFIX"\1/g" $DESIGN_FILES

# add prefix to all module instantiations
for MODULE in $MODULES; do
    sed -i -E "s/(^|[^A-Za-z0-9_])$MODULE([^A-Za-z0-9_])/\1"$PREFIX"$MODULE\2/g" $DESIGN_FILES
done

# remove old header files to avoid redefining their contents during elaboration
rm $COMMON_DEFINES $EL2_PARAM $EL2_PDEF $PD_DEFINES
