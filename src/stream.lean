/-
 -----------------------------------------------------------
  Formalization and correctness of stream ciphers
 -----------------------------------------------------------
-/

import data.bitvec.basic
import data.zmod.basic

import to_mathlib

-- a single bit encryption/descryption stream cipher
namespace stream_bit

-- a random single key bit
variable k : zmod 2

-- x is a plain text bit and y is a cipher text bit
variables x y : zmod 2

def encrypt : zmod 2 := x + k
def decrypt : zmod 2 := y + k

-- proof of correctness
lemma dec_undoes_enc : 
  x = decrypt k (encrypt k x) :=
begin
  unfold encrypt,
  unfold decrypt,
  ring_nf,
  finish,
end

end stream_bit

-- a vector of bits encryption/descryption stream cipher
namespace stream_bits

-- size of the text and the key
variable n : nat

-- xv = plaintext, yv = ciphertext, kv = keystream (all size n) 
variables xv yv kv: bitvec n

def encrypt : bitvec n := xv + kv
def decrypt : bitvec n := yv + kv

-- proof of correctness
lemma dec_undoes_enc_stream : 
  xv = decrypt n kv (encrypt n kv xv) :=
begin
  unfold encrypt,
  unfold decrypt,
  rw ← bitvec.add_self_assoc,
end

end stream_bits