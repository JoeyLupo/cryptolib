/-
 -----------------------------------------------------------
  Security games as pmfs 
 -----------------------------------------------------------
-/

import data.zmod.basic
import measure_theory.probability_mass_function
import to_mathlib
import uniform

noncomputable theory 

/-
  G1 = public key space, G2 = private key space, 
  M = message space, C = ciphertext space 
  A_state = type for state A1 passes to A2
-/
variables {G1 G2 M C A_state: Type} 
          (keygen : pmf (G1 × G2))
          (encrypt : G1 → M → pmf C)
          (A1 : G1 → pmf (M × M × A_state))
          (A2 : C → A_state → pmf (zmod 2))

/- 
  The semantic security game. 
  Returns 1 if the attacker A2 guesses the correct bit
-/
def SSG : pmf (zmod 2):= 
do 
  k ← keygen, 
  m ← A1 k.1, 
  b ← uniform_2,
  c ← encrypt k.1 (if b = 0 then m.1 else m.2.1),
  b' ← A2 c m.2.2,
  pure (1 + b + b')

local notation `SSG_Adv` := abs ((SSG keygen encrypt A1 A2 1 : ℝ) - 1/2)

def is_semantically_secure (ε : nnreal) : Prop := SSG_Adv ≤ ε
