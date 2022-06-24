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

def ceasar_encrypt : zmod m := x + k
def ceasar_decrypt : zmod m := y - k

lemma ceasar_dec_undoes_enc : 
  x = ceasar_decrypt k (ceasar_encrypt k x) :=
begin
  unfold ceasar_encrypt,
  unfold ceasar_decrypt,
  simp only [add_sub_cancel],
end

-- the probability of guessing the key in this cipher is 1/26
lemma ceasar_probability [fact (0 < m)] :
  ∀ (p : zmod m), (uniform_zmod m) p = 1/m :=
begin
  exact uniform_zmod_prob,
end


-- rot13 cipher

-- the shared key in rot13 is fixed.
def rot13_k : ℤ := 13

def rot13_encrypt : zmod m := x + rot13_k
def rot13_decrypt : zmod m := y + rot13_k

lemma rot13_dec_undoes_enc : 
  x = rot13_decrypt (rot13_encrypt x) :=
begin
  unfold rot13_encrypt,
  unfold rot13_decrypt,
  ring,
end

-- the probability of guessing rot13 is being used is 1/26
lemma rot13_probability [fact (0 < m)] :
  ∀ (p : zmod m), (uniform_zmod m) p = 1/m :=
begin
  exact uniform_zmod_prob,
end


-- affine cipher

-- additional multiplier
variable a : zmod m

def encrypt_affine : zmod m := (a * x) + k
def decrypt_affine : zmod m := a⁻¹ * (y - k)

-- gcd between 26 and multiplier a must be 1
lemma affine_dec_undoes_enc (h : a.val.gcd m = 1) : 
  x = decrypt_affine k (encrypt_affine k x a) a :=
begin
  unfold encrypt_affine,
  unfold decrypt_affine,
  simp only [add_sub_cancel],
  ring_nf,
  rw [mul_assoc, zmod.mul_inv_eq_gcd],
  finish,
end

variables b P : zmod m

-- there are 12 coprimes that we can use as multiplier,
-- and 26 possibilities for the key → prob of guessing the 
-- key used is 12 x 26 → 1/312
lemma affine_probability [fact (a.val.gcd m = 1)] : ∀ (a b P), (uniform_zmod 26) (a * P + b) = 1/312 :=
begin
  sorry,
end
