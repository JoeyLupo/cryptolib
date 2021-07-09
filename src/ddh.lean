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
          (g : G) (hGg : ∀ (x : G), x ∈ subgroup.gpowers g)
          (q : ℕ) [fact (0 < q)] (hGq : fintype.card G = q) 
          -- check Mario, 0 < q necessary for fintype.card?
          -- A a variable or parameter? 
          -- See https://leanprover.github.io/theorem_proving_in_lean/interacting_with_lean.html
          -- Petcher uses variable and then in ElGamal specializes for their fixed group
          (A : G × G × G → pmf (zmod 2))

def DDH0 : pmf (zmod 2) := 
do 
  x ← uniform_zmod q,
  y ← uniform_zmod q,
  b0 ← A (g^x.val, g^y.val, g^(x*y).val),
  b1 ← uniform_2,
  return (1 + b0 + b1)

def DDH1 : pmf (zmod 2) := 
do 
  x ← uniform_zmod q,
  y ← uniform_zmod q,
  z ← uniform_zmod q,
  b0 ← A(g^x.val, g^y.val, g^z.val),
  b1 ← uniform_2,
  return (1 + b0 + b1)

local notation `Pr[DDH0]` := DDH0 G g q A 1 
local notation `Pr[DDH1]` := DDH1 G g q A 1

def DDH_Adv : ℝ := abs (Pr[DDH0] - Pr[DDH1])

-- TO-DO need to figure out how to connect with negligible file (or if even necessary)
def DDH_Adv1 : ℝ := abs (DDH0 1)
#check DDH0
--def DDH : Prop := DDH_Adv < ε

end DDH