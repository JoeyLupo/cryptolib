/-
 -----------------------------------------------------------
  Probability lemmas, from Section 3 of (Nowak, 2009) 
 -----------------------------------------------------------
-/

import uniform

noncomputable theory 

variables {G H: Type} 
          (P : G → (zmod 2))
          (δ : pmf G)
          
def prob_pred : nnreal := 
  ∑' (a : G), (if P a = 1 then δ a else 0)  

lemma t35 (ϕ : G → H) (P' : H → (zmod 2)): 
  prob_pred P' (do x ← δ, return (ϕ x)) = ∑' (a : G), ((δ a) * prob_pred P' (return (ϕ a))):= 
begin
  sorry,
  -- rw pmf.bind_pure_comp ϕ δ,
end 

variables {A B C : Type} [fintype A] [group A] [decidable_eq A] [fintype B] [group B] [decidable_eq B]
          (f : A → B) (h : function.bijective f)
          (g : B → C)

theorem multiset_bijection (s : multiset A) (hs : s ≠ 0) (t : multiset B) (ht : t ≠ 0) : 
  pmf.map f (pmf.of_multiset s hs) = pmf.of_multiset t ht :=
begin
  simp [pmf.of_multiset],
  simp [pmf.map],
  simp [pmf.bind],
  --let b : B,
  --by_cases 
  sorry,
end

lemma t315b : pmf.map f (uniform_grp A) = uniform_grp B := 
begin
  simp [uniform_grp],
  exact multiset_bijection f _ _ _ _,
end

theorem t315  (P' : C → (zmod 2)) : 
  prob_pred P' (do x ← uniform_grp A, return (g (f x))) = prob_pred P' (do y ← uniform_grp B, return (g y)) := 
begin
  rw <- t315b f,
  simp [pmf.map],
  simp [bind],
end