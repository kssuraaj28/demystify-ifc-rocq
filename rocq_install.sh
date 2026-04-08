#!/usr/bin/env bash
set -e

script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd "$script_dir"

# https://rocq-prover.org/docs/using-opam
opam update
opam switch create nmif 4.14.2  
##I hope that these new things get installed in the new switch
opam install rocq-prover rocq-core=9.1.1
opam pin add rocq-core 9.1.1 #I wonder what would happen if you ran this without the previous commad. TODO
opam install rocqide
opam repo add rocq-released https://rocq-prover.org/opam/released
