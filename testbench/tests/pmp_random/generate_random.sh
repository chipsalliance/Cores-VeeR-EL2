#!/usr/bin/env bash

set -e

outfile=random_data.h
iterations=100

printf '// This file was generated with generate_random.sh\n\n' > $outfile

echo "#define RANDOM_ITERATIONS $iterations" >> $outfile
echo 'const uint32_t rand_address [] = {' >> $outfile

# generate random data in hex, fold each 8 hex digits, prepend '0x', append ',' 
tr -dc 'A-F0-9' < /dev/urandom | dd bs=1 count=$((8 * $iterations)) 2>/dev/null | \
     fold -w8 | \
     sed 's/^/    0x/' | \
     sed 's/$/,/' >> $outfile
echo >> $outfile
echo '};' >> $outfile

echo 'const uint32_t rand_config [] = {' >> $outfile
# generate random data in hex, fold each 8 hex digits, prepend '0x', append ',' 
tr -dc 'A-F0-9' < /dev/urandom | dd bs=1 count=$((8 * $iterations)) 2>/dev/null | \
     fold -w8 | \
     sed 's/^/    0x/' | \
     sed 's/$/,/' >> $outfile
echo >> $outfile
echo '};' >> $outfile

