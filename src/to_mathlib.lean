import data.bitvec.basic
import data.zmod.basic 
import group_theory.specific_groups.cyclic
import group_theory.subgroup.basic
import group_theory.subgroup.pointwise
import group_theory.order_of_element
import measure_theory.probability_mass_function.basic
import measure_theory.probability_mass_function.constructions
import measure_theory.probability_mass_function.monad

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
   ∀ (x : G), x ∈ subgroup.zpowers g


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
