# cryptolib

Formal proof of correctness of different ciphers.

Currently for learning purposes.

Forked from https://github.com/JoeyLupo/cryptolib

## Install cryptolib

```console
$ git clone https://github.com/oxarbitrage/cryptolib
$ cd cryptolib
$ leanproject build
```

## Files in cryptolib
	
- `elgamal.lean` - contains the formal specification of the ElGamal public key encryption protocol, and the formal proofs of correctness and semantic 
    
- `pke.lean` - provides formal definitions for correctness and semantic security of a public key encryption scheme

- `tactics.lean` - provides the `bindskip` and `bindconst` tactics to help prove equivalences between pmfs

- `to_mathlib.lean` - includes general lemmas for inclusion into mathlib

- `uniform.lean` - defines the uniform distribution over a finite group as a pmf, including the special case of Z_q, the integers modulo q, and provides two useful lemmas regarding uniform probabilities 

- `rsa.lean` - contains proof of correctness of the RSA public key encryption protocol

- `substitution.lean` - contains basic formalization and proof of correctness of different substitution ciphers

- `stream.lean` - contains basic formalization and proof of correctness of stream ciphers