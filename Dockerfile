# Get coq image w/ Coq version 8.12
FROM coqorg/coq:8.12-ocaml-4.11-flambda

# Copy our artifact code to dc dir
Copy ./ dc
RUN sudo chown -R coq dc
WORKDIR dc

# This adds executables like coqtop, et al, to PATH
RUN eval "$(opam env)"

# Our development's dependencies are all installed with coq-idt.
# This installation may take a wee bit...
RUN opam repo add coq-released https://coq.inria.fr/opam/released &&\
    opam install coq-idt --yes

# make our entry-point executable
RUN chmod +x make-all

