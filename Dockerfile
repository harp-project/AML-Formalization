#ARG coq_image="coqorg/coq:latest"
ARG coq_image="coqorg/coq:8.12.2"
FROM ${coq_image}
RUN opam update && opam install coq-stdpp
