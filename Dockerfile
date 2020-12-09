ARG coq_image="coqorg/coq:latest"
FROM ${coq_image}
RUN opam update && opam install coq-stdpp
