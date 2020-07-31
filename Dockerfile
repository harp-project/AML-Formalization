ARG coq_image="coqorg/coq:latest"
FROM ${coq_image}
RUN sudo chown -R coq:coq .
