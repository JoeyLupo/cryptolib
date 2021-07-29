import measure_theory.probability_mass_function

variables {A B : Type}

lemma bind_skip' (p : pmf A) (f g : A → pmf B) : 
  (∀ (a : A), f a = g a) → p.bind f = p.bind g :=
begin
  intro ha, 
  ext,
  simp,
  simp_rw ha,
end

lemma bind_skip_const' (pa : pmf A) (pb : pmf B) (f : A → pmf B) : 
  (∀ (a : A), f a = pb) → pa.bind f = pb :=
begin
  intro ha, 
  ext,
  simp,
  simp_rw ha,
  simp [nnreal.tsum_mul_right],
end

setup_tactic_parser
meta def tactic.interactive.bind_skip  (x : parse (tk "with" *> ident)?) : tactic unit :=
do `[apply bind_skip'],
  let a := x.get_or_else `_,
  tactic.interactive.intro a

meta def tactic.interactive.bind_skip_const  (x : parse (tk "with" *> ident)?) : tactic unit :=
do `[apply bind_skip_const'],
  let a := x.get_or_else `_,
  tactic.interactive.intro a
