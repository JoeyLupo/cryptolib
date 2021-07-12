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

variables (G : Type) [fintype G] [group G] 

lemma grp_ne_zero : (fintype.elems G).val ≠ 0 := 
begin
  have e : G := (_inst_2.one),
  have h1 : e ∈ (fintype.elems G).val :=  finset.mem_univ e,
  have h2 : 0 < multiset.card (fintype.elems G).val := 
  begin
    apply (multiset.card_pos_iff_exists_mem).mpr,
    exact Exists.intro e h1,
  end,
  exact multiset.card_pos.mp h2,
end

noncomputable theory 

-- TO-DO remove n_pos hypothesis 
def uniform_zmod (n : ℕ) [fact (0 < n)] : pmf (zmod n) := 
  pmf.of_multiset (zmod.fintype n).elems.val (zmod_ne_zero n)

def uniform_2 := uniform_zmod 2

lemma prob_half : uniform_2 1 = (0.5 : nnreal) := 
begin
  simp [uniform_2],
  simp [uniform_zmod],
  simp [pmf.of_multiset],
  have h : multiset.card (fintype.elems (zmod 2)).val = 2 := rfl,
  rw h,
  sorry,
end

def uniform_bitvec (n : ℕ) : pmf (bitvec n) := 
  pmf.of_multiset (bitvec.fintype n).elems.val (bitvec_ne_zero n)

def uniform_grp : pmf G := 
  pmf.of_multiset (fintype.elems G).val (grp_ne_zero G)
