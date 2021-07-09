import measure_theory.probability_mass_function
import to_mathlib

noncomputable theory

--def pmf_equiv {A:Type}(P:A->bool)(epsilon:R)(d1 d2:T A) : Prop :=
  --Rle (Rabs (probability P d1 - probability P d2)) epsilon.

-- A section for getting a feel for proving easy equivalences between pmfs
section jo
parameters {α β γ : Type}
          (c1 : pmf α) (c2 : pmf β)
          (c3 : α → β → γ)

def a8 : pmf α := 
do 
  a ← c1,
  return a

theorem b_p : a8 = c1 := 
begin
  exact pmf.bind_pure _,
end

def comm1 : pmf γ := 
do 
  a ← c1,
  b ← c2, 
  return (c3 a b)

def comm2 : pmf γ := 
do 
  b ← c2, 
  a ← c1,
  return (c3 a b)

theorem comm : comm1 = comm2 :=
begin
  exact pmf.bind_comm c1 c2 (λ (a : α) (b : β), (λ (b1 : β), return (c3 a b1)) b),
  --exact pmf.bind_comm _ _ _,
end

def a1 : pmf α := 
do 
  a ← c1,
  b ← c2,
  return a 

def b1 : pmf α := 
do
  b ← c2,
  a ← c1,
  return a

lemma t1 : a1 = b1 := 
begin
  exact pmf.bind_comm c1 c2 _,
end

lemma t2 : b1 = c2.bind (λ (b : β), c1) := 
begin
  conv_rhs {rw ← pmf.bind_pure c1},
  exact rfl,
end

lemma t3 : c2.bind (λ (b : β), c1) = c1 := 
begin
  ext,
  simp,
  rw nnreal.tsum_mul_right c2 (c1 a),
  simp,
end

example : a1 = c1 :=
begin
  rw t1,
  rw t2,
  exact t3,
end

def p (x : α): pmf α := 
do 
  return x

/-lemma bdqa (x : α): ∀ (a : α), (p x) a = x :=
begin

end-/
  
end jo

variables (α : Type)
def prob_pred (p : pmf α) (P : α → bool) : nnreal := ∑'(a : α), if P(a) then p a else 0 
/-
  TO-DO

  2. A notion of equivalence (up to negligible) of distributions or probabilities

  3. Prove a one-step equivalence (i.e. via pure_bind) from the DDH assumption, or
     perhaps a simpler pmf (zmod 2)

-/