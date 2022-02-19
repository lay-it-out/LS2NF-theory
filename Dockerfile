FROM docker.io/coqorg/coq:8.13-ocaml-4.12-flambda

COPY . .
RUN opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
ENV OPAMYES=true
RUN opam install dune
RUN make builddep

CMD ["/usr/bin/make"]
