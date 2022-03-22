ARG VARIANT="hirsute"
FROM mcr.microsoft.com/vscode/devcontainers/base:0-${VARIANT}

RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y install --no-install-recommends \
        cmake \
        pkg-config \
        make \
        gcc \
        g++ \
        gcc-mingw-w64-x86-64 \
        libssl-dev \
        nasm \
        gdb

WORKDIR /
