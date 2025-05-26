FROM coqorg/coq:8.16.1-ocaml-4.12.1-flambda

ARG REPO="https://github.com/sovesti/mcscoqsat.git"

RUN sudo apt-get update

RUN sudo apt-get install haskell-stack git -y

RUN git clone --depth 1 ${REPO} \
    && cd mcscoqsat \
    && make
