FROM alpine:3.16.0

# install dependencies
RUN apk update
RUN apk add bash gcc g++ make git rsync diffutils
RUN apk add opam findutils gmp-dev

# create opam user, initialize
RUN adduser -D -s /bin/bash opam
USER opam
WORKDIR /home/opam
ENV OPAMYES=1
RUN opam init

# copy repo
RUN mkdir LS2NF-Theory
WORKDIR /home/opam/LS2NF-Theory
COPY --chown=opam:opam . .
RUN opam repo add coq-released "https://coq.inria.fr/opam/released"
RUN opam repo add iris-dev "https://gitlab.mpi-sws.org/iris/opam.git"
RUN make builddep
RUN eval $(opam env) && make

ENTRYPOINT ["bash"]
