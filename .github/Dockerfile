FROM ubuntu:22.04

ARG VERILATOR_VERSION
ARG VERILATOR_UVM_VERSION
ARG OPENOCD_VERSION
ARG RENODE_VERSION
ARG SPIKE_VERSION

ENV VERILATOR_VERSION=$VERILATOR_VERSION
ENV VERILATOR_UVM_VERSION=$VERILATOR_UVM_VERSION
ENV OPENOCD_VERSION=$OPENOCD_VERSION
ENV RENODE_VERSION=$RENODE_VERSION
ENV SPIKE_VERSION=$SPIKE_VERSION

# All versions shall be stated explicitly
RUN : "${VERILATOR_VERSION:?Environment variable VERILATOR_VERSION is not set or empty}" && \
    : "${VERILATOR_UVM_VERSION:?Environment variable VERILATOR_UVM_VERSION is not set or empty}" && \
    : "${OPENOCD_VERSION:?Environment variable OPENOCD_VERSION is not set or empty}" && \
    : "${RENODE_VERSION:?Environment variable RENODE_VERSION is not set or empty}" && \
    : "${SPIKE_VERSION:?Environment variable SPIKE_VERSION is not set or empty}"

# Install prerequisites
RUN apt-get update && apt-get install -y --no-install-recommends \
    autoconf \
    automake \
    autotools-dev \
    bc \
    bison \
    build-essential \
    ccache \
    curl \
    device-tree-compiler \
    flex \
    gawk \
    git \
    gperf \
    help2man \
    libexpat-dev \
    libfl-dev \
    libfl2 \
    libgmp-dev \
    libmpc-dev \
    libmpfr-dev \
    libtool \
    make \
    ninja-build \
    patchutils \
    pkg-config \
    python3 \
    python3-pip \
    python3-venv \
    sudo \
    texinfo \
    wget \
    zlib1g \
    zlib1g-dev

# Clone and build Verilator
RUN git clone https://github.com/verilator/verilator verilator && \
    cd verilator && \
    git checkout ${VERILATOR_VERSION} && \
    autoconf && \
    ./configure --prefix=/opt/verilator && \
    make -j $(nproc) && \
    make install && \
    cd .. && \
    rm -rf verilator

# TODO We're using a separate version of verilator for uvm tests.
# TODO Handle this properly.
# TODO We may use docker compose or at least clean the previous tree and rebuild instead of cloning again.
# Clone and build Verilator (UVM)
RUN git clone https://github.com/verilator/verilator verilator && \
    cd verilator && \
    git checkout ${VERILATOR_UVM_VERSION} && \
    autoconf && \
    ./configure --prefix=/opt/verilator_uvm && \
    make -j $(nproc) && \
    make install && \
    cd .. && \
    rm -rf verilator

# Clone and build OpenOCD
RUN git clone https://github.com/antmicro/openocd openocd && \
    cd openocd && \
    git checkout ${OPENOCD_VERSION} && \
    ./bootstrap && \
    ./configure --prefix=/opt/openocd --enable-remote-bitbang CFLAGS="-Wno-error=misleading-indentation -Wno-error=stringop-overflow" && \
    make -j$(nproc) && \
    make install && \
    cd .. && \
    rm -rf openocd

# Download and unpack Renode
RUN wget https://builds.renode.io/renode-${RENODE_VERSION}.linux-portable.tar.gz && \
    mv renode-*.tar.gz /opt/renode.tar.gz && \
    mkdir -p /opt/renode && \
    tar -zxvf /opt/renode.tar.gz --strip-components=1 -C /opt/renode && \
    rm /opt/renode.tar.gz

# Clone and build Spike
# FIXME: sed replacements in this part should be done in a VeeR-specific Spike fork
#
# Rationale: VeeR pulls down bits 31 and 30 of pmpaddrn CSRs to 0.
# This change is required so that we don't get mismatches related
# to read/write operations on PMP CSRs:
#
#   Mismatch[1]:
#   ISS[23] : pc[80000068] csrrw   a1, pmpaddr0, a1: a1:f75f83f1 c944_pmpaddr0:2000044f
#   HDL[23] : pc[80000068] : a1:375f83f1 c3b0:2000044f
RUN git clone https://github.com/riscv-software-src/riscv-isa-sim spike && \
    cd spike && \
    git checkout ${SPIKE_VERSION} && \
    sed -i 's/((reg_t(1) << (MAX_PADDR_BITS - PMP_SHIFT)) - 1);/0x3fffffff;/g' riscv/csrs.cc && \
    sed -i 's/return (addr >> MAX_PADDR_BITS) == 0;/return (addr >> 32) == 0;/g' riscv/sim.cc && \
    mkdir build && \
    cd build && \
    ../configure --prefix=/opt/spike && \
    make -j$(nproc) && \
    make install && \
    cd ../.. && \
    rm -rf /opt/spike/include /opt/spike/lib spike

ENV PATH="$PATH:/opt/renode:/opt/verilator/bin:/opt/openocd/bin:/opt/spike/bin"

RUN verilator --version
RUN /opt/verilator_uvm/bin/verilator --version
RUN openocd --version
RUN renode --version
RUN spike 2>&1 | head -n1
