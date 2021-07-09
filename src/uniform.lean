/-
 -----------------------------------------------------------
  Uniform distributions over zmod q, bitvecs, and finite groups
 -----------------------------------------------------------
-/

import data.bitvec.basic
import data.zmod.basic 
import measure_theory.probability_mass_function 
import to_mathlib

lemma zmod_ne_zero (n : ℕ) [fact (0 < n)] : (zmod.fintype n).elems.val ≠ 0 := 
begin
  apply (multiset.card_pos).mp,
  have h : multiset.card (fintype.elems (zmod n)).val = n := zmod.card n,
  rw h,
  exact _inst_1.out,
end

lemma bitvec_ne_zero (n : ℕ) : (bitvec.fintype n).elems.val ≠ 0 := 
begin
  apply (multiset.card_pos).mp,
  have h : multiset.card (fintype.elems (bitvec n)).val = 2^n := bitvec.card n,
  rw h,
  simp,
end

-- TO-DO finite group G? needed?

noncomputable theory 

-- TO-DO remove n_pos hypothesis 
def uniform_zmod (n : ℕ) [fact (0 < n)] : pmf (zmod n) := 
  pmf.of_multiset (zmod.fintype n).elems.val (zmod_ne_zero n)

def uniform_2 := uniform_zmod 2

def uniform_bitvec (n : ℕ) : pmf (bitvec n) := 
  pmf.of_multiset (bitvec.fintype n).elems.val (bitvec_ne_zero n)

lemma prob_half : uniform_2 1 = (0.5 : nnreal) := 
begin
  simp [uniform_2],
  simp [uniform_zmod],
  simp [pmf.of_multiset],
  have h : multiset.card (fintype.elems (zmod 2)).val = 2 := rfl,
  rw h,
  sorry,
end
