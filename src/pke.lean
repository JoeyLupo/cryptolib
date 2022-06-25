/-
 -----------------------------------------------------------
  PKE correctness using pmfs 
 -----------------------------------------------------------
-/

import uniform

noncomputable theory 

/-
  G1 = public key space, G2 = private key space, 
  M = message space, C = ciphertext space 
  A_state = type for state A1 passes to A2
-/
variables {G1 G2 M C A_state: Type} [decidable_eq M]
          (keygen : pmf (G1 × G2))
          (encrypt : G1 → M → pmf C)
          (decrypt : G2 → C → M)
          (A1 : G1 → pmf (M × M × A_state))
          (A2 : C → A_state → pmf (zmod 2))

/- 
  Executes the a public-key protocol defined by keygen,
  encrypt, and decrypt
-/
def enc_dec  (m : M) : pmf (zmod 2) := 
do 
  k ← keygen,
  c ← encrypt k.1 m,
  pure (if decrypt k.2 c = m then 1 else 0)

/- 
  A public-key encryption protocol is correct if decryption undoes 
  encryption with probability 1
-/
def pke_correctness : Prop := ∀ (m : M), enc_dec keygen encrypt decrypt m = pure 1 
