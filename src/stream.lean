/-
 -----------------------------------------------------------
  Formalization and correctness of stream ciphers
 -----------------------------------------------------------
-/

import data.bitvec.basic
import data.zmod.basic

-- stream cipher : a single bit encryption/descryption scheme

-- a random single key bit
variable k : zmod 2

-- x is a plain text bit and y is a cipher text bit
variables x y : zmod 2

def encrypt_bit : zmod 2 := x + k
def decrypt_bit : zmod 2 := y + k

-- proof of correctness
lemma dec_undoes_enc_bit : 
  x = decrypt_bit k (encrypt_bit k x) :=
begin
  unfold encrypt_bit,
  unfold decrypt_bit,
  ring_nf,
  finish,
end

-- stream cipher : a vector of bits encryption/descryption scheme

-- size of the text and the key
variable n : nat

-- xv = plaintext, yv = ciphertext, kv = keystream (all size n) 
variables xv yv kv: bitvec n

def encrypt_stream : bitvec n := xv + kv
def decrypt_stream : bitvec n := yv + kv

-- missing bitvec lemmas. TODO: they need proof
lemma bitvec_add_self (a : bitvec n) : a + a = bitvec.zero n := by sorry
lemma bitvec_add_assoc (a b c: bitvec n) : a + b + c = a + (b + c) := by sorry
lemma bitvec_zero_add (a : bitvec n) : a = bitvec.zero n + a := by sorry
lemma bitvec_add_self_assoc (a b : bitvec n) : b = a + (a + b) :=
  by rw [←bitvec_add_assoc, bitvec_add_self, ←bitvec_zero_add]

-- proof of correctness
lemma dec_undoes_enc_stream : 
  xv = decrypt_stream n kv (encrypt_stream n kv xv) :=
begin
  unfold encrypt_stream,
  unfold decrypt_stream,
  rw ← bitvec_add_self_assoc,
end
