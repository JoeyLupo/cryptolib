/-
 -----------------------------------------------------------
  The decisional Diffie-Hellman assumption as a security game
 -----------------------------------------------------------
-/

import measure_theory.probability_mass_function 
import to_mathlib
import uniform

noncomputable theory 

section DDH

variables (G : Type) [fintype G] [group G]
          (g : G) (g_gen_G : ∀ (x : G), x ∈ subgroup.gpowers g) 
          (q : ℕ) [fact (0 < q)] (G_card_q : fintype.card G = q) 
          -- check Mario, 0 < q necessary for fintype.card?
          (A : G → G → G → pmf (zmod 2))

include g_gen_G G_card_q

def DDH0 : pmf (zmod 2) := 
do 
  x ← uniform_zmod q,
  y ← uniform_zmod q,
  b ← A (g^x.val) (g^y.val) (g^(x.val * y.val)),
  pure b

def DDH1 : pmf (zmod 2) := 
do 
  x ← uniform_zmod q,
  y ← uniform_zmod q,
  z ← uniform_zmod q,
  b ← A (g^x.val) (g^y.val) (g^z.val),
  pure b

local notation `Pr[DDH0]` := (DDH0 G g g_gen_G q G_card_q A 1 : ℝ)
local notation `Pr[DDH1]` := (DDH1 G g g_gen_G q G_card_q A 1 : ℝ)

def DDH (ε : nnreal) : Prop := abs (Pr[DDH0] - Pr[DDH1]) ≤ ε

end DDH
