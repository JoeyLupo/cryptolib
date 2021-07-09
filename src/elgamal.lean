/-
 -----------------------------------------------------------
  Correctness and semantic security of ElGamal public-key 
  encryption scheme
 -----------------------------------------------------------
-/

import ddh
import security

noncomputable theory

section elgamal

parameters (G : Type) [fintype G] [group G] [decidable_eq G] 
           (g : G) (hGg : ∀ (x : G), x ∈ subgroup.gpowers g)
           (q : ℕ) [fact (0 < q)] (hGq : fintype.card G = q) 

def M := G
def C := G × G 

variables (A1 : G → pmf (M × M))
          (A2 : G × C → pmf (zmod 2))

-- g^x is the public key, and x is the secret key
def keygen : pmf (G × (zmod q)) := 
do 
  x ← uniform_zmod q,
  return (g^x.val, x)

-- encrypt takes a pair (pk, m)
def encrypt (m : G × M) : pmf C := 
do
  y ← uniform_zmod q,
  return (g^y.val, (m.1)^y.val * m.2)

-- TO-DO want zmod q × C, but want nicer way to 
-- get at input than c.1.1
def decrypt (x : zmod q) (c : C) : G := 
  (c.2 / (c.1^x.val))

def enc_dec (m : M) : pmf (zmod 2) := 
do
  (α, x) ← keygen,
  return 1
  --(β, ζ) ← encrypt(α, m),
  --return (if m = decrypt(x, (β, ζ)) then 1 else 0)

theorem elgamal_correct : ∀ (m : M), enc_dec m = return 1 := 
begin
  intro m,
  simp [enc_dec],
  simp [keygen],
  simp [return],
  simp [pure],
  simp [pmf.pure],
  ext,
  simp,
  simp [enc_dec._match_1],
  -- need tactic or lemma that binding with a pure dist is just passing 
  -- that constant along 
  -- lemma ∀ y, (return x) y = x 
end

#check SSG G (zmod q) M C keygen encrypt A1 A2 1
local notation `ElGamal_adv` := abs((SSG G (zmod q) M C keygen encrypt A1 A2 1) - 1/2) 

theorem elgamal_secure : is_semantically_secure ElGamal:= sorry

end elgamal