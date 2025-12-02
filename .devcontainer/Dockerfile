FROM mcr.microsoft.com/devcontainers/base:ubuntu

RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y install --no-install-recommends ant xvfb \
    && apt-get clean -y && rm -rf /var/lib/apt/lists/*
