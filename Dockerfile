FROM ubuntu:17.10
RUN apt-get update
RUN apt-get install -y apt-utils

RUN apt-get install -y urweb

RUN apt-get install -y z3=4.4.1\*
RUN apt-get install -y ruby
RUN apt-get install -y smlnj libsmlnj-smlnj ml-yacc ml-ulex
RUN apt-get install -y mlton

ENV TIML /timl

ADD . $TIML
ENV PATH $PATH:$TIML

WORKDIR $TIML/urweb

ENTRYPOINT ./timl.exe -p 8888
EXPOSE 8888
