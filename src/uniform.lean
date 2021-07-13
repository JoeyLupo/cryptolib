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

variables (G : Type) [fintype G] [group G] [decidable_eq G]

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

lemma uniform2_prob : uniform_2 1 = (0.5 : nnreal) := 
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

theorem uniform_prob : ∀ (g : G), (uniform_grp G) g = 1 / multiset.card (fintype.elems G).val :=
begin
  intro g,
  simp [uniform_grp],
  have h1 : 
  (pmf.of_multiset (fintype.elems G).val (grp_ne_zero G)) g = 
    multiset.count g (fintype.elems G).val / multiset.card (fintype.elems G).val := 
  begin
    sorry,
  end,
  rw h1,
  have h2 : multiset.count g (fintype.elems G).val = 1 := 
  begin
    -- fintype => no duplicates => count = 1 forall elts 
    suggest,
  end,
  rw h2,
  simp,
end