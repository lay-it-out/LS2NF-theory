FROM docker.io/coqorg/coq:8.13-ocaml-4.12-flambda

COPY . .
RUN opam repository add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git --set-default
RUN make builddep
# RUN opam switch create . ocaml-base-compiler.4.12.0

ENTRYPOINT [ "./entrypoint.sh" ]
