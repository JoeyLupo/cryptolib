/-
 -----------------------------------------------------------
  Formalization and correctness of substitution ciphers
 -----------------------------------------------------------
-/

import data.zmod.basic

import uniform

-- All substitution cipher operations will be mod 26.
-- (the number of letters in the english/latin alphabet)
def m : ℕ := 26

-- the key that both parties share, aka: shift
variable k : ℤ

-- x is the plain text and y is the cipher text
variables x y : zmod m


-- ceasar cipher
namespace ceasar

def encrypt : zmod m := x + k
def decrypt : zmod m := y - k

lemma dec_undoes_enc : 
  x = decrypt k (encrypt k x) :=
begin
  unfold encrypt,
  unfold decrypt,
  simp only [add_sub_cancel],
end

end ceasar


-- rot13 cipher
namespace rot13

-- the shared key in rot13 is fixed.
def krot : ℤ := 13

def encrypt : zmod m := x + krot
def decrypt : zmod m := y + krot

lemma dec_undoes_enc : 
  x = decrypt (encrypt x) :=
begin
  unfold encrypt,
  unfold decrypt,
  ring,
end

end rot13

-- affine cipher
namespace affine

-- additional multiplier
variable a : zmod m

def encrypt : zmod m := (a * x) + k
def decrypt : zmod m := a⁻¹ * (y - k)

-- gcd between 26 and multiplier a must be 1
lemma dec_undoes_enc (h : a.val.gcd m = 1) : 
  x = decrypt k (encrypt k x a) a :=
begin
  unfold encrypt,
  unfold decrypt,
  simp only [add_sub_cancel],
  ring_nf,
  rw [mul_assoc, zmod.mul_inv_eq_gcd],
  finish,
end

end affine
