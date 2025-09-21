FROM ubuntu:22.04

RUN apt-get update && \
    apt-get install -y \
    g++ gcc make git \
    python3 \
    nano vim

# Clone Z3 repository and build it
RUN git clone https://github.com/Z3Prover/z3.git && \
    cd z3 && \
    python3 scripts/mk_make.py && \
    cd build && \
    make -j2

# Set working directory
WORKDIR /MultiTheoryHorn

# Copy source code of MultiTheoryHorn
COPY benchmarks ./benchmarks
COPY ext ./ext
COPY src ./src
COPY Makefile ./Makefile

# Set Z3_ROOT environment variable
ENV Z3_ROOT=/z3
ENV LD_LIBRARY_PATH=${Z3_ROOT}/build
# Build MultiTheoryHorn
RUN cd /MultiTheoryHorn && \
    make -j4