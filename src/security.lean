/-
 -----------------------------------------------------------
  Security games as pmfs 
 -----------------------------------------------------------
-/

import data.zmod.basic
import measure_theory.probability_mass_function
import negligible
import to_mathlib
import uniform

noncomputable theory 

/-
  G1 = public key space, G2 = private key space, 
  M = message space, C = ciphertext space 
-/
variables (G1 G2 M C : Type) 
          (keygen : pmf (G1 × G2))
          (encrypt : G1 × M → pmf C)
          -- TO-DO model state as in Petcher?
          (A1 : G1 → pmf (M × M))
          (A2 : G1 × C → pmf (zmod 2))

/- 
  The semantic security game. 
  Returns 1 if the attacker A2 guesses the correct bit
-/
def SSG : pmf (zmod 2):= 
do 
  (pk, sk) ← keygen, 
  (m0, m1) ← A1(pk),
  b' ← uniform_2,
  c ← if b' = 0 then encrypt(pk, m0) else encrypt(pk, m1),
  b ← A2(pk, c),
  return (1 + b + b')


local notation `SSG_Adv` := abs ((SSG G1 G2 M C keygen encrypt A1 A2 1) - 1/2)

-- TO-DO Need to handle security parameter η, whether to ignore it as in Nowak, or 
-- make it fully explicit as in Boneh and Shoup
def is_semantically_secure 
(keygen : pmf (G1 × G2)) (encrypt : G1 × M → pmf C): Prop := negligible SSG_Adv
