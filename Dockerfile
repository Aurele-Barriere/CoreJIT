FROM ocaml/opam2:4.09

ADD https://releases.llvm.org/9.0.0/clang+llvm-9.0.0-x86_64-pc-linux-gnu.tar.xz /tmp/
ADD src /home/opam/

ADD container-install.sh /home/opam/
RUN "/home/opam/container-install.sh"

ADD aec.sh /home/opam/
CMD ["/home/opam/aec.sh"]
