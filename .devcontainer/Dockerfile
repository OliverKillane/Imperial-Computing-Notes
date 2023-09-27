FROM ubuntu:latest


# Install basic packages
RUN apt-get update -q 
RUN apt-get install -qy build-essential wget curl sudo openssh-client git

# LATEX:
# Install full texlive distribution (very large)
ARG TL_VERSION=2023
ARG TL_MIRROR=https://mirror.ctan.org/systems/texlive/tlnet/install-tl-unx.tar.gz
RUN cd /tmp && \
    wget --directory-prefix /tmp ${TL_MIRROR} && \
    zcat < install-tl-unx.tar.gz | tar xf - && \
    cd install-tl-* && \
    perl ./install-tl --no-interaction --no-doc-install --no-src-install
ENV PATH="${PATH}:/usr/local/texlive/${TL_VERSION}/bin/x86_64-linux"

# Update packages and tlmgr
RUN tlmgr init-usertree
RUN tlmgr update --self --all
RUN tlmgr install latexindent chktex

# install inkscape (for tikz) and minted (for code highlighting) 
RUN apt-get install -qy inkscape python3 python3-pip
RUN pip install pygments

# C++
# Already installed GCC as part of build-essential
RUN apt-get install -qy clang-format

# Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -qy

# Elixir
RUN apt-get install -qy elixir

# TLA
# Required Java, toolbox used is included in the VSCode extension
RUN apt-get install -qy default-jdk

# Haskell
RUN apt-get install -qy libffi-dev libffi8ubuntu1 libgmp-dev libgmp10 libncurses-dev libncurses5 libtinfo5
RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | BOOTSTRAP_HASKELL_NONINTERACTIVE=1 BOOTSTRAP_HASKELL_GHC_VERSION=latest BOOTSTRAP_HASKELL_CABAL_VERSION=latest BOOTSTRAP_HASKELL_INSTALL_STACK=1 BOOTSTRAP_HASKELL_INSTALL_HLS=1 BOOTSTRAP_HASKELL_ADJUST_BASHRC=P sh

# Clean up to reduce image size
RUN apt-get clean autoclean && apt-get autoremove -y
RUN rm -rf /var/lib/{apt,dpkg,cache,log}/ /tmp/* /usr/local/texlive/${TL_VERSION}/*.log

CMD /usr/bin/bash