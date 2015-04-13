# Spin
FROM ubuntu:14.10
MAINTAINER Guillaume Claret

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y curl
RUN apt-get install -y make gcc bison

WORKDIR /root
RUN curl -L http://spinroot.com/spin/Src/src643.tar.gz |tar -xz
WORKDIR Src6.4.3
RUN make
RUN cp spin /usr/local/bin/

WORKDIR /root/spin
