/-
 -----------------------------------------------------------
  Uniform distributions over zmod q, bitvecs, and finite groups
 -----------------------------------------------------------
-/

import to_mathlib

variables (G : Type) [fintype G] [group G] [decidable_eq G]

noncomputable theory 

def uniform_bitvec (n : ℕ) : pmf (bitvec n) := 
  pmf.of_multiset (bitvec.fintype n).elems.val (bitvec.multiset_ne_zero n)

def uniform_grp : pmf G := 
  pmf.of_multiset (fintype.elems G).val (group.multiset_ne_zero G)

#print uniform_grp

def uniform_zmod (n : ℕ) [ne_zero n] [group (zmod n)] : pmf (zmod n) := uniform_grp (zmod n)

def uniform_2 [group (zmod 2)]: pmf (zmod 2) := uniform_zmod 2 

lemma uniform_grp_prob : 
  ∀ (g : G), (uniform_grp G) g = 1 / multiset.card (fintype.elems G).val :=
begin
  intro g,
  have h1 : ⇑(uniform_grp G) = (λ (a : G), 
    (multiset.count a (fintype.elems G).val : nnreal) / multiset.card (fintype.elems G).val) := 
  begin 
    ext,
    simp [uniform_grp, pmf.of_multiset, coe_fn],
    simp [has_coe_to_fun.coe],
    congr,
  end,
  have h2 : (uniform_grp G) g = 
    multiset.count g (fintype.elems G).val / multiset.card (fintype.elems G).val := 
  begin
    exact congr_fun h1 g,
  end,
  rw h2,
  have h3 : multiset.count g (fintype.elems G).val = 1 := multiset.count_univ g,
  rw h3,
  simp only [nat.cast_one],
end 

lemma uniform_zmod_prob {n : ℕ} [ne_zero n] [group (zmod n)] : 
  ∀ (a : zmod n), (uniform_zmod n) a = 1/n := 
begin
  intro a,
  simp [uniform_zmod],
  have h1 := uniform_grp_prob (zmod n) a,
  have h2 : multiset.card (fintype.elems (zmod n)).val = n := zmod.card n,
  rw h2 at h1,
  rw inv_eq_one_div (n : nnreal),
  exact h1,
end
