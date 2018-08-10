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
opam install coq-mathcomp-character coq-mathcomp-field
```

Finally, the build script is set up to do the rest.
```
make
```
