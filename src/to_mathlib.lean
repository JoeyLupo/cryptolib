import data.bitvec.basic
import group_theory.specific_groups.cyclic
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

-- TO-DO name? 
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

end bitvec 
