FROM ubuntu:focal

ENV DEBIAN_FRONTEND noninteractive
RUN apt-get update &&                                                           \
    apt-get install -qq                                                         \
                    cpio                                                        \
                    gcc-8                                                       \
                    git                                                         \
                    libdata-printer-perl                                        \
                    m4                                                          \
                    make                                                        \
                    ocaml                                                       \
                    opam                                                        \
                    perl-doc                                                    \
                    sudo                                                        \
                    wget                                                        \
                    sagemath &&                                                 \
    useradd -d /home/eval -m -s /bin/bash eval &&                               \
    echo "eval ALL=(ALL) NOPASSWD: ALL" > /etc/sudoers.d/eval &&                \
    chmod 0440 /etc/sudoers.d/eval &&                                           \
    passwd -l eval &&                                                           \
    chown -R eval:eval /home/eval &&                                            \
    rm -rf /var/lib/apt/lists/*

USER eval
ENV HOME /home/eval
ENV PATH $HOME/tornado/:$PATH
WORKDIR /home/eval

# Bring Coq & Menhir
RUN opam init --disable-sandboxing -a -y && \
    opam install -y -j4 coq.8.8.1           \
                        menhir.20180905

# Add instructions on Bash startup
COPY docker/motd.sh $HOME/.motd.sh
RUN echo ". ~/.motd.sh" >> $HOME/.bashrc

# Include documentation
COPY Readme.md $HOME/

# Copy & compile Usuba and Tightprove+
COPY --chown=eval:eval src $HOME/tornado

# Copy the config file for Sage & Tightprove+
COPY --chown=eval:eval docker/config.json $HOME/tornado/usuba/

# Copy a unit test
COPY --chown=eval:eval simple_test/ $HOME/simple_test/

RUN cd $HOME/tornado/usuba &&             \
    opam config exec -- ./configure.pl && \
    cd $HOME/tornado &&                   \
    opam config exec -- make


ENTRYPOINT [ "opam", "config", "exec", "--" ]
CMD ["/bin/bash", "-c", "perl simple_test/run.pl" ]