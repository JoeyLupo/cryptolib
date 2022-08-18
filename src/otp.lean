/-
  One-Time Pad correctness
-/

import data.zmod.basic
import data.bitvec.basic

namespace otp

/- 
  There are 2 ways to do it:
  1- By modular arithmetic.
  2- by bitwise arithmetic.
  Difference is performance, bitwise should be faster to implement.
-/

namespace modulo

-- the mod we use is irrelevant, 26 is common but we keep it random.
variable mod : ℕ 

-- secret message and key of the same size
variables p k : zmod mod

def encrypt : zmod mod := p - k

variable c : zmod mod
def decrypt : zmod mod := c + k

-- correctness
lemma dec_undoes_enc : p = decrypt mod (encrypt mod p k) k :=
begin
  unfold encrypt,
  unfold decrypt,
  finish
end

-- lets have 2 random keys
variables k1 k2 : zmod mod

-- assuming the keys are always different,
-- then the ciphertext will be always different too.
lemma always_different (h: k1 ≠ k2) : 
  encrypt mod p k1 ≠ encrypt mod p k2 :=
begin
  unfold encrypt,
  finish,
end

-- Example: otp is inmune to letter frequency
section exampl

-- lets use mod 26 to encrypt and decrypt the word `happy`.
-- https://www.youtube.com/watch?v=2_w9l9visH8
def example_mod : ℕ := 26

def H : zmod example_mod := 8
def A : zmod example_mod := 1
def P : zmod example_mod := 16
def Y : zmod example_mod := 25

def K1 : zmod example_mod := 8
def K2 : zmod example_mod := 19
def K3 : zmod example_mod := 13
def K4 : zmod example_mod := 4
def K5 : zmod example_mod := 23

-- encrypt
#eval (H + K1)
#eval (A + K2)

-- as we use different keys, same letter gets encrypted different.
-- this makes otp inmune to letter frequency
#eval (P + K3)
#eval (P + K4)

#eval (Y + K5)

-- decrypt
#eval ((H + K1) - K1)
#eval ((A + K2) - K2)
#eval ((P + K3) - K3)
#eval ((P + K4) - K4)
#eval ((Y + K5) - K5)


end exampl

end modulo

namespace xor

-- size of the bitvectors
variable len : ℕ 

-- plaintext and keys of the same size
variables p k : bitvec len 

-- encrypt is the same as decrypt
def encrypt : bitvec len := p.xor k
def decrypt : bitvec len := p.xor k

-- TODO: xor properties that need to be proved
def xor_self_inverse (A : bitvec len) : Prop :=
  A.xor A = bitvec.zero len

def xor_assoc (A : bitvec len) (B : bitvec len) (C : bitvec len) :
  Prop := (A.xor B).xor C = (A.xor C).xor B

-- Appling xor to a bitvector A with B and then appling xor
-- to the result with B gives A. 
lemma xor_twice (A: bitvec len) (B: bitvec len) : 
  (A.xor B).xor B = A :=
begin
  sorry,
end

-- Example: A vector A xored twice with the same key K 
--          returns the vector A.
section exampl

def A : bitvec 3 := 6
def K : bitvec 3 := 3 
#eval ((A.xor K).xor K).to_nat

end exampl

lemma dec_undoes_enc : p = decrypt len (encrypt len p k) k :=
begin
  unfold encrypt,
  unfold decrypt,
  rw xor_twice,
end


end xor

end otp
