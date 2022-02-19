FROM docker.io/coqorg/coq:8.13-ocaml-4.12-flambda

COPY . .
RUN opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
RUN OPAMYES=true make builddep

CMD ["/usr/bin/make"]
