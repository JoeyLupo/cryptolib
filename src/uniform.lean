/-
 -----------------------------------------------------------
  Uniform distributions over zmod q, bitvecs, and finite groups
 -----------------------------------------------------------
-/

import to_mathlib

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

def uniform_bitvec (n : ℕ) : pmf (bitvec n) := 
  pmf.of_multiset (bitvec.fintype n).elems.val (bitvec_ne_zero n)

def uniform_grp : pmf G := 
  pmf.of_multiset (fintype.elems G).val (grp_ne_zero G)

def uniform_zmod (n : ℕ) [fact (0 < n)] : pmf (zmod n) := uniform_grp (zmod n)

def uniform_2 : pmf (zmod 2) := uniform_zmod 2 

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
  simp,
end 

lemma uniform_zmod_prob {n : ℕ} [fact (0 < n)] : 
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