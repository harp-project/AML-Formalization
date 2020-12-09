ARG coq_image="coqorg/coq:latest"
FROM ${coq_image}
RUN opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
RUN opam update && opam install coq-stdpp
