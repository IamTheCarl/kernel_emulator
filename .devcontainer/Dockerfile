# See here for image contents: https://github.com/microsoft/vscode-dev-containers/tree/v0.217.4/containers/ubuntu/.devcontainer/base.Dockerfile

# [Choice] Ubuntu version (use hirsuite or bionic on local arm64/Apple Silicon): hirsute, focal, bionic
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
        libssl-dev

COPY unicorn /tmp/unicorn
WORKDIR /tmp/unicorn/build_linux
RUN cmake .. -DCMAKE_BUILD_TYPE=Release \
 && make -j$(nproc) install

WORKDIR /tmp/unicorn/build_windows
RUN cmake .. -DCMAKE_TOOLCHAIN_FILE=../mingw-w64.cmake \
 && make -j$(nproc) install

RUN rm -rf /tmp/unicorn

WORKDIR /
