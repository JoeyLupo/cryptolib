# cryptolib

Formal proof of correctness and game-based proof of semantic security for the ElGamal public key encryption protocol using the Lean theorem prover. Our implementation draws from Adam Petcher's Foundational Cryptographic Framework (FCF) Coq library at https://github.com/adampetcher/fcf. My master's dissertation which describes this project in more depth can be found [here](https://1drv.ms/b/s!AkAJTM1hbeSD4wcF1T4NYiRG5b_D?e=0Yp8Hx).

Files in cryptolib:

- `ddh.lean` - provides a formal specification of the decisional Diffie-Hellman assumption on a finite cyclic group
	
- `elgamal.lean` - contains the formal specification of the ElGamal public key encryption protocol, and the formal proofs of correctness and semantic 
    
- `negligible.lean` - defines negligible functions and provides several useful lemmas regarding negligible functions

- `pke.lean` - provides formal definitions for correctness and semantic security of a public key encryption scheme

- `tactics.lean` - provides the `bindskip` and `bindconst` tactics to help prove equivalences between pmfs

- `to_mathlib.lean` - includes general lemmas for inclusion into mathlib

- `uniform.lean` - defines the uniform distribution over a finite group as a pmf, including the special case of Z_q, the integers modulo q, and provides two useful lemmas regarding uniform probabilities 

- `rsa.lean` - contains proof of correctness of the RSA public key encryption protocol