/-
 --------------------------------------------------------------
  Correctness of Fesitel networks and ciphers
 --------------------------------------------------------------
-/

import data.bitvec.basic
import data.bitvec.core

import to_mathlib

namespace fesitel

/--
For encryption and for each round:
  - A swap of the two sides is done: Lᵢ₊₁ = Rᵢ
  - Encryption is done: Rᵢ₊₁ = Lᵢ + F(K, Rᵢ)
-/

-- the size of a full plaintext (or cipher) block
def block_size : ℕ := 64
-- block is splitted into two (left and right)
def h : ℕ := block_size / 2

-- an f function that just add each bit
def f (K R : bitvec h) : bitvec h := K + R

-- the key vector is of the same size of half block
variable K : bitvec h

-- the left and right parts
variables L R : bitvec h 

-- encryption is only done in one side
def encrypt (K L R: bitvec h) : bitvec h := L + (f K R)
-- decryption is just doing encryption again
def decrypt (K L R: bitvec h) : bitvec h := encrypt K L R

-- proof of correctness
lemma dec_undoes_enc : R = decrypt K L (encrypt K L R) :=
begin
  unfold decrypt,
  unfold encrypt,
  unfold f,
  rw ←bitvec.add_assoc_self_reduce,
end


end fesitel
