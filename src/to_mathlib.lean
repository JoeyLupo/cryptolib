import data.bitvec.basic
import data.zmod.basic 
import group_theory.specific_groups.cyclic
import group_theory.subgroup
import measure_theory.probability_mass_function 

/-
 ---------------------------------------------------------
  To measure_theory.probability_mass_function 
  with help from Yakov Pechersky 
 ---------------------------------------------------------
-/

noncomputable theory

instance : monad pmf := 
{ pure := @pmf.pure,
  bind := @pmf.bind }

instance : is_lawful_functor pmf :=
{ id_map := @pmf.map_id,
  comp_map := λ _ _ _ f g x, (pmf.map_comp x f g).symm }

instance : is_lawful_monad pmf :=
{ pure_bind := @pmf.pure_bind,
  bind_assoc := @pmf.bind_bind }



/-
 ---------------------------------------------------------
  To multiset.range
 ---------------------------------------------------------
-/

lemma range_pos_ne_zero (n : ℕ) (n_pos : 0 < n): multiset.range n ≠ 0 := 
begin
  apply (multiset.card_pos).mp,
  rw multiset.card_range,
  exact n_pos,
end



/-
 ---------------------------------------------------------
  To group_theory.is_cyclic
 ---------------------------------------------------------
-/

def is_cyclic.generator {G : Type} [group G] [is_cyclic G] (g : G): Prop :=
   ∀ (x : G), x ∈ subgroup.gpowers g


/-
 ---------------------------------------------------------
  To bitvec.basic
 ---------------------------------------------------------
-/

namespace bitvec

instance fintype : Π (n : ℕ), fintype (bitvec n) := by {intro n, exact vector.fintype}

lemma card (n : ℕ) : fintype.card (bitvec n) = 2^n := card_vector n

lemma multiset_ne_zero (n : ℕ) : (bitvec.fintype n).elems.val ≠ 0 := 
begin
  apply (multiset.card_pos).mp,
  have h : multiset.card (fintype.elems (bitvec n)).val = 2^n := bitvec.card n,
  rw h,
  simp,
end

end bitvec 



/-
 ---------------------------------------------------------
  To data.basic.zmod, TO-DO Ask why this isn't already there
 ---------------------------------------------------------
-/

namespace zmod 

instance group : Π (n : ℕ) [fact (0 < n)], group (zmod n) := 
  by {intros n h, exact multiplicative.group}

end zmod 



/-
 ---------------------------------------------------------
  To group_theory.subgroup (Already there, on newer update)
 ---------------------------------------------------------
-/

namespace subgroup 

variables {G : Type*} [group G]

lemma mem_gpowers_iff {g h : G} : 
  h ∈ subgroup.gpowers g ↔ ∃ (k : ℤ), g^k = h := iff.rfl 

end subgroup



/-
 ---------------------------------------------------------
  To nat
 ---------------------------------------------------------
-/

lemma exists_mod_add_div (a b: ℕ) : ∃ (m : ℕ), a = a % b + b * m := 
begin
  use (a/b),
  exact (nat.mod_add_div a b).symm,
end



/-
 ---------------------------------------------------------
  To group
 ---------------------------------------------------------
-/

variables (G : Type) [fintype G] [group G]

namespace group

lemma multiset_ne_zero : (fintype.elems G).val ≠ 0 := 
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

end group 

lemma inv_pow_eq_card_sub_pow (g : G) (m : ℕ) (h : m ≤ fintype.card G) :
  (g ^ m)⁻¹ = g ^ (fintype.card G - m) := 
begin
  have h : (g ^ m) * g ^ (fintype.card G - m) = 1 := 
  begin
    rw <- pow_add,
    rw nat.add_sub_of_le,
    exact pow_card_eq_one, 
    exact h,
  end,
  exact inv_eq_of_mul_eq_one h,
end

-- (Already there, on newer update as pow_eq_mod_card m )
lemma pow_eq_mod_card (g : G) (m : ℕ) : g ^ m = g ^ (m % fintype.card G) :=
begin
  conv_lhs {rw <- nat.mod_add_div m (fintype.card G), rw pow_add},
  rw pow_mul,
  simp only [one_pow, pow_card_eq_one],
  exact (self_eq_mul_right.mpr rfl).symm,
end
