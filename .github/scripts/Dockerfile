FROM debian:trixie AS base

# Install prerequisites
RUN apt-get update && apt-get install -y --no-install-recommends \
    autoconf \
    automake \
    autotools-dev \
    bc bison \
    build-essential \
    ccache \
    curl \
    cpanminus \
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
    libpython3-all-dev \
    make \
    ninja-build \
    patchutils \
    pkg-config \
    python3 \
    python3-dev \
    python3-pip \
    python3-venv \
    sudo \
    texinfo \
    wget \
    zlib1g \
    zlib1g-dev \
    libbit-vector-perl \
    meson

RUN cpanm File::Slurp
RUN cpanm --notest Module::Pluggable
RUN cpanm Bit::Vector Capture::Tiny DateTime DateTime::Format::W3CDTF Devel::Cover Digest::MD5 File::Spec JSON::XS Memory::Process Time::HiRes

FROM base AS riscv-toolchain-build
# Clone and build RISC-V toolchain
RUN git clone https://github.com/riscv-collab/riscv-gnu-toolchain.git riscv
# This is a workaround for unstable upstream dependency servers
RUN cd riscv && sed -i \
  -e 's#url = https://sourceware.org/git/binutils-gdb.git#url = git://sourceware.org/git/binutils-gdb.git#' \
  -e 's#url = https://sourceware.org/git/glibc.git#url = git://sourceware.org/git/glibc.git#' \
  -e 's#url = https://gcc.gnu.org/git/gcc.git#url = git://gcc.gnu.org/git/gcc.git#' \
  -e 's#url = https://sourceware.org/git/newlib-cygwin.git#url = git://sourceware.org/git/newlib-cygwin.git#' \
  .gitmodules
RUN cd riscv && ./configure --prefix=/opt/riscv --enable-multilib && \
  make -j$(nproc) && \
  cd .. && \
  rm -rf riscv

FROM base AS verilator-build
ARG VERILATOR_VERSION
ENV VERILATOR_VERSION=$VERILATOR_VERSION
RUN : "${VERILATOR_VERSION:?Environment variable VERILATOR_VERSION is not set or empty}"

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

FROM base AS openocd-build
ARG OPENOCD_VERSION
ENV OPENOCD_VERSION=$OPENOCD_VERSION
RUN : "${OPENOCD_VERSION:?Environment variable OPENOCD_VERSION is not set or empty}"

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

FROM base AS renode-build
ARG RENODE_VERSION
ENV RENODE_VERSION=$RENODE_VERSION
RUN : "${RENODE_VERSION:?Environment variable RENODE_VERSION is not set or empty}"

# Download and unpack Renode
RUN wget https://builds.renode.io/renode-${RENODE_VERSION}.linux-portable.tar.gz && \
  mv renode-*.tar.gz /opt/renode.tar.gz && \
  mkdir -p /opt/renode && \
  tar -zxvf /opt/renode.tar.gz --strip-components=1 -C /opt/renode && \
  rm /opt/renode.tar.gz

FROM base AS spike-build
ARG SPIKE_VERSION
ENV SPIKE_VERSION=$SPIKE_VERSION
RUN : "${SPIKE_VERSION:?Environment variable SPIKE_VERSION is not set or empty}"

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


FROM base AS aggregate
ARG VERILATOR_VERSION
ARG OPENOCD_VERSION
ARG RENODE_VERSION
ARG SPIKE_VERSION

COPY --from=riscv-toolchain-build /opt/riscv /opt/riscv
COPY --from=renode-build /opt/renode /opt/renode
COPY --from=verilator-build /opt/verilator /opt/verilator
COPY --from=openocd-build /opt/openocd /opt/openocd
COPY --from=spike-build /opt/spike /opt/spike

ENV PATH="$PATH:/opt/riscv/bin:/opt/renode:/opt/verilator/bin:/opt/openocd/bin:/opt/spike/bin"
RUN riscv64-unknown-elf-gcc --version
RUN verilator --version
RUN openocd --version
RUN renode --version
RUN spike 2>&1 | head -n1
