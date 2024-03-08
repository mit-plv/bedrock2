Live Verification Artifact
==========================

We provide two ways to evaluate our artifact:
* Docker: Using a docker image with all software pre-installed and all files pre-compiled
* From source: Does not require docker, but requires a system with Coq, an IDE for it (preferably ProofGeneral), and gcc, and up to 1 hour of compilation time
The headings below indicate for which options they apply.


Getting Started (aka kick-the-tires phase)
------------------------------------------

### Install Docker [Docker only]

Install the Docker Engine (Docker CE) as described on https://docs.docker.com/engine/install/.
The docs try to convince you to install Docker Desktop, but Docker Desktop is not necessary and we did not use it.
We only use the Docker Engine (Docker CE). On the other hand, if you really like Docker Desktop, it probably also works with our image.
We used Docker version 25.0.4, but other versions could work too.
Note: On some systems (eg Fedora), after installing docker, you need to start the docker daemon explicitly using a command like eg `sudo systemctl start docker`, while on others, this seems to happen automatically.


### Import & start the image [Docker only]

Download `LiveVerifArtifactDockerImage.tar` and import it into docker:

```
sudo docker load -i /path/to/LiveVerifArtifactDockerImage.tar
```

After that, `sudo docker images` should list a "repository" named `LiveVerifArtifact`.
Then the image:

```
sudo docker run -it LiveVerifArtifact
```

This should open a command prompt inside the docker image, where you can use `ls` and `cd` to look around to see what's there.
`~/bedrock2-LiveVerifArtifact-coq-8.17.1` is the *toplevel directory* containing the artifact.


### Install dependencies [from-source only]

You need the following software:
* Coq 8.17.1, installed using your preferred installation method. Versions < 8.17 will not work, version 8.18 and 8.19 probably work too.
* An IDE for Coq. We use Emacs + Proof General, but if you are familiar with another IDE, that might work too.
* GCC (we use version 9.4.0, but other versions probably work too)


### Compile Coq files [from-source only]

In the *toplevel directory* of the artifact, run `make LiveVerifCompile`.
This might take up to an hour. If you have 16GB of RAM, it should be safe to add `-j4` to get some parallelism (but too much parallelism can cause the system to run out of memory).


### Check that you can step through a proof in your IDE [docker & from-source]

The following instructions are for emacs + proof general, but if you prefer a different Coq IDE, that should work too.

In the *toplevel directory* of the artifact, run `emacs LiveVerif/src/LiveVerifExamples/memset.v`.
Navigate to the line just after the one starting with `uintptr_t i = 0`.
Process the proof up to that point (Ctrl-c Ctrl-Enter), and make sure you see the source window and the window with the proof goal.
Process a few more lines of the proof (Ctrl-c Ctrl-n), and make sure you can see how this stepping affects the proof goal.


Step-by-step instructions [docker & from-source]
------------------------------------------------

### Overview

The artifact contains the following dependencies:
* `deps/coqutil`: Generic Coq library
* `deps/riscv-coq`: Specification of the RISC-V ISA
* `bedrock2`: The bedrock2 source language
* `compiler`: The bedrock2-to-RISC-V compiler

And it contains the following directories related to the paper:
* `LiveVerif/src/LiveVerif`: The LiveVerif framework
* `LiveVerif/src/LiveVerifExamples`: Sample programs verified in the LiveVerif framework
* `LiveVerifCompile`: A small demo illustrating that the bedrock2 compiler indeed compiles a LiveVerif-generated Bedrock2 program

The project dependency structure looks as follows (right depends on left):

```
                   LiveVerif
                  /         \
         bedrock2            LiveVerifCompile
       /          \         /
coqutil            compiler
       \          /
         riscv-coq
```
