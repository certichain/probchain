# probchain
Probabilistic reasoning about blockchain protocols

Note: to use this, you will need the development version of coq.
Can be installed with the following:
```
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam install coq-mathcomp-ssreflect.dev -j3
```

Alongside this, the field mathcomp library must also be installed:
```
opam install coq-mathcomp-field
```
Finally, as the infotheo probability library doesn't seem to be on opam, it has been included as a submodule to this repo.
To load the files from the external repo, simply run from the root of this repo:
```
git submodule update --recursive --remote --init .
```
