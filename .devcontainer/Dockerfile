FROM ubuntu:latest

ARG TL_VERSION=2023
ARG TL_MIRROR=https://mirror.ctan.org/systems/texlive/tlnet/install-tl-unx.tar.gz

# Install basic packages
RUN apt-get update -q 
RUN apt-get install -qy build-essential wget sudo

# Clean up to reduce image size
RUN apt-get clean autoclean && apt-get autoremove -y
RUN rm -rf /var/lib/{apt,dpkg,cache,log}/ /tmp/* /usr/local/texlive/${TL_VERSION}/*.log

# Install basic texlive distribution
RUN cd /tmp && \
    wget --directory-prefix /tmp ${TL_MIRROR} && \
    zcat < install-tl-unx.tar.gz | tar xf - && \
    cd install-tl-* && \
    perl ./install-tl --scheme=small --no-interaction 
ENV PATH="${PATH}:/usr/local/texlive/${TL_VERSION}/bin/x86_64-linux"

# Update packages and tlmgr
RUN tlmgr init-usertree
RUN tlmgr update --self --all
