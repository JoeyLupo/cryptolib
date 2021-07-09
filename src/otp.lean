/-
 -----------------------------------------------------------
  One-time pad definitions and proofs for groups and bitvecs
 -----------------------------------------------------------
-/

import data.bitvec.basic
import uniform

noncomputable theory 

variables {n : ℕ} 

def xor_const (x : bitvec n) : pmf (bitvec n) := 
do 
  y ← uniform_bitvec n,
  return (x.xor y)

theorem bitvec_OTP : ∀ (x : bitvec n), xor_const x = uniform_bitvec n :=  
begin
  intro x,
  simp [xor_const],
  simp [uniform_bitvec],
  sorry,
end

variables {G : Type} [fintype G] [group G]
          (uniform_grp : pmf G)
          -- TO-DO ? Define uniform_grp in probability

def grp_const (g : G) : pmf G := 
do 
  h ← uniform_grp, 
  return (h*g)

theorem grp_OTP : ∀ (g : G), grp_const uniform_grp g = uniform_grp := sorry 