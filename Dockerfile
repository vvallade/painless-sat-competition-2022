FROM satcomp-base:leader
USER root
WORKDIR /

#  Install required softwares
RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt install -y cmake build-essential zlib1g-dev libopenmpi-dev wget unzip build-essential zlib1g-dev cmake python3 build-essential gfortran wget curl

ADD run.sh /competition/run.sh
ADD solver /competition/solver
RUN chmod +x /competition/run.sh
RUN chmod +x /competition/solver

ADD painless painless
RUN cd painless && make -j 4
USER ecs-user
