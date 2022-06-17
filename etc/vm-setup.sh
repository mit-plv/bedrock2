#!/usr/bin/env bash

sudo -s <<-EOS
	echo '* APT'

	# Add sources for latest LLVM and GCC

	wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key|sudo apt-key add -
	cat > /etc/apt/sources.list.d/llvm.list <<- EEOS
		deb http://apt.llvm.org/focal/ llvm-toolchain-focal main
		deb-src http://apt.llvm.org/focal/ llvm-toolchain-focal main
		# 13
		deb http://apt.llvm.org/focal/ llvm-toolchain-focal-13 main
		deb-src http://apt.llvm.org/focal/ llvm-toolchain-focal-13 main
		# 14
		deb http://apt.llvm.org/focal/ llvm-toolchain-focal-14 main
		deb-src http://apt.llvm.org/focal/ llvm-toolchain-focal-14 main
	EEOS

	add-apt-repository -y ppa:ubuntu-toolchain-r/test

	# Install packages

	apt-get -y update
	apt-get -y upgrade
	apt-get -y install \
		build-essential make perl bleachbit fonts-inconsolata \
		pkg-config make patch unzip git aspcud curl emacs \
		autoconf m4 libgmp-dev opam python3 python3-pip \
		libcairo2-dev libexpat1-dev libgtk-3-dev libgtksourceview-3.0-dev \
		gcc-10 gcc-11 clang-13
    apt-get -y purge libreoffice*
	apt-get -y autoremove
	apt-get -y clean

	echo '* PIP'

	pip3 install numpy matplotlib pandas seaborn
EOS

export OPAMYES=true
echo '* OPAM init'
opam init --auto-setup --compiler=4.09.1
eval $(opam env)
echo '* OPAM repo add'
opam repo add --all-switches coq-released https://coq.inria.fr/opam/released
echo '* OPAM update'
opam update
echo '* OPAM install (will take a while; maybe 15 minutes)'
opam install -j2 coq=8.14.1 coqide stdlib-shims
opam pin add https://github.com/janestreet/ocaml_intrinsics.git
echo '* OPAM cleanup (to save space)'
opam clean

mkdir -p ~/.emacs.d/
cat > ~/.emacs.d/init.el <<-EOS
	(add-to-list 'load-path "~/.emacs.d/lisp/PG/generic")

	(require 'package)
	(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/"))
	(package-initialize)

	;; Basic usability
	(xterm-mouse-mode)
	(load-theme 'tango t)

	(setq-default proof-splash-seen t
				  inhibit-startup-screen t)
	(add-to-list 'default-frame-alist '(fullscreen . maximized))
EOS

emacs --batch --load ~/.emacs.d/init.el \
	  --eval "(package-refresh-contents)" \
	  --eval "(package-install 'proof-general)" \
	  --eval "(package-install 'company-coq)"

cd ~
git clone --recursive https://github.com/mit-plv/rupicola.git -b pldi2022-ae rupicola

cd ~/rupicola
make -j

# Local Variables:
# indent-tabs-mode: t
# End:
