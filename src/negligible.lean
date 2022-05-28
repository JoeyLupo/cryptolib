/-
 -----------------------------------------------------------
  Negligible functions. 

  TO-DO connect with security parameter, (or not, as in Nowak),
  and refactor proofs/improve variable naming
 -----------------------------------------------------------
-/

import analysis.special_functions.pow
import data.nat.basic
import data.real.basic

/- 
  A function f : ℤ≥1 → ℝ is called negligible if 
  for all c ∈ ℝ>0 there exists n₀ ∈ ℤ≥1 such that 
  n₀ ≤ n →  |f(n)| < 1/n^c
-/
def negligible (f : ℕ → ℝ) := 
  ∀ c > 0, ∃ n₀, ∀ n, 
  n₀ ≤ n → abs (f n) <  1 / (n : ℝ)^c

def negligible' (f : ℕ → ℝ) :=
  ∀ (c : ℝ), ∃ (n₀ : ℕ), ∀ (n : ℕ),
  0 < c → n₀ ≤ n → abs (f n) < 1 / n^c

lemma negl_equiv (f : ℕ → ℝ) : negligible f ↔ negligible' f := 
begin
  split,
  {-- Forward direction
    intros h c,
    have arch := exists_nat_gt c,
    cases arch with k hk,
    let k₀ := max k 1,
    have k_leq_k₀ : k ≤ k₀ := le_max_left k 1,
    have kr_leq_k₀r : (k:ℝ) ≤ k₀ := nat.cast_le.mpr k_leq_k₀,
    have k₀_pos : 0 < k₀ := by {apply le_max_right k 1},
    have a := h k₀ k₀_pos,
    cases a with n' hn₀,
    let n₀ := max n' 1,
    have n₀_pos : 0 < n₀ := by apply le_max_right n' 1,
    have n'_leq_n₀ : n' ≤ n₀ := le_max_left n' 1,
    use n₀,
    intros n c_pos hn,
    have hnnn : n' ≤ n := by linarith,
    
    have b : (n : ℝ)^c ≤ (n : ℝ)^(k₀ : ℝ) := 
    begin
      apply real.rpow_le_rpow_of_exponent_le,
      norm_cast,
      linarith,
      linarith,
    end,
    have daf : (n : ℝ)^(k₀ : ℝ) = (n : ℝ)^k₀ := (n : ℝ).rpow_nat_cast k₀,
    rw daf at b,
    have d : 1 / (n : ℝ)^k₀ ≤ 1 / n^c := 
    begin
      apply one_div_le_one_div_of_le,
      { -- Proving 0 < (n:ℝ) ^ c
        apply real.rpow_pos_of_pos,
        norm_cast,
        linarith,
      },
      {exact b},
    end,
    have goal :  abs (f n) < 1 / n^c := 
    calc
      abs(f n) < 1 / (n : ℝ)^k₀ : hn₀ n hnnn
           ... ≤ 1 / n^c : d,
    exact goal,
  },

  {-- Reverse direction 
    intros h c hc,
    cases h c with n₀ hn₀,
    use n₀,
    intros n hn,
    have goal := hn₀ n (nat.cast_pos.mpr hc) hn,
    rw (n : ℝ).rpow_nat_cast c at goal,
    exact goal,
  },
end

lemma zero_negl : negligible (λn, 0) := 
begin
  intros c hc,
  use 1,
  intros n hn,
  norm_num,
  apply one_div_pos.mpr,
  apply pow_pos, 
  have h : 0 < n := by linarith,
  exact nat.cast_pos.mpr h,
end

lemma negl_add_negl_negl {f g : ℕ → ℝ} : negligible f → negligible g → negligible (f + g) := 
begin
  intros hf hg,
  intros c hc,
  have hc1 : (c+1) > 0 := nat.lt.step hc,
  have hf2 := hf (c+1) hc1,
  have hg2 := hg (c+1) hc1,
  cases hf2 with nf hnf,
  cases hg2 with ng hng,
  let n₀ := max (max nf ng) 2,
  use n₀,
  intros n hn,
  let nr := (n:ℝ),
  have n_eq_nr : (n:ℝ) = nr := by refl,

  have tn : max nf ng ≤ n₀ := le_max_left (max nf ng) 2,
  have t2n₀ : 2 ≤ n₀ := le_max_right (max nf ng) 2,
  have t2n : 2 ≤ n := by linarith,
  have t2nr : 2 ≤ nr := 
  begin
    have j := nat.cast_le.mpr t2n,
    rw n_eq_nr at j,
    norm_num at j,
    exact j,
    exact real.nontrivial,
  end,
  have tnr_pos : 0 < nr := by linarith,

  have t2na : (1 / nr) * (1/nr^c) ≤ (1 / (2 : ℝ)) * (1 / nr^c) := 
  begin
    have ht2 : 0 < (1 / nr^c) := by {apply one_div_pos.mpr, exact pow_pos tnr_pos c},
    apply (mul_le_mul_right ht2).mpr,
    apply one_div_le_one_div_of_le,
    exact zero_lt_two,
    exact t2nr,
  end,

  have tnr2 : 1 / nr^(c + 1) ≤ (1 / (2 : ℝ)) * (1 / nr^c) := 
  calc
    1 / nr ^ (c + 1) = (1 / nr)^(c + 1) : by rw one_div_pow
                 ... = (1 / nr) * (1 / nr)^c  : pow_succ (1 / nr) c
                 ... = (1 / nr) * (1 / nr^c) : by rw one_div_pow
                 ... ≤ (1 / (2 : ℝ)) * (1 / nr^c) : t2na,
  
  have tnf : nf ≤ n :=
  calc 
    nf  ≤ n₀ : le_of_max_le_left tn
    ... ≤ n : hn,
  have tfn := hnf n tnf,
  have tf : abs (f n) < (1 / (2 : ℝ)) * (1 / nr^c) := by linarith,

  have tng : ng ≤ n :=
  calc ng  ≤ n₀ : le_of_max_le_right tn
       ... ≤ n : hn,
  have tgn := hng n tng,
  have tg : abs (g n) < (1/(2:ℝ)) * (1/nr^c) := by linarith,

  have goal : abs ((f + g) n) < 1 / nr ^ c := 
  calc
    abs ((f + g) n) = abs (f n + g n) : by rw pi.add_apply f g n
                ... ≤ abs (f n) + abs (g n) : abs_add (f n) (g n)
                ... < (1/(2:ℝ)) * (1/nr^c) + abs (g n): by linarith
                ... < (1/(2:ℝ)) * (1/nr^c) + (1/(2:ℝ)) * (1/nr^c) : by linarith
                ... = 1/nr^c : by ring_nf,
  exact goal,
end

lemma bounded_negl_negl {f g : ℕ → ℝ} (hg : negligible g): 
(∀ n, abs (f n) ≤ abs (g n)) → negligible f := 
begin
  intro h,
  intros c hc,
  have hh := hg c hc,
  cases hh with n₀ hn₀, 
  use n₀,
  intros n hn,
  have goal : abs (f n) < 1 / (n : ℝ) ^ c := 
  calc 
    abs (f n) ≤ abs (g n) : h n
          ... < 1 / (n : ℝ)^c: hn₀ n hn,
  exact goal,
end

lemma nat_mul_negl_negl {f : ℕ → ℝ} (m : ℕ): 
negligible f → negligible (λn, m * (f n)) := 
begin
  intros hf,
  induction m with k hk,
  { -- Base case
    norm_num,
    exact zero_negl,
  },
  { -- Inductive step
    norm_num,
    have d : (λn, ((k : ℝ) + 1) * (f n)) = (λn, (k : ℝ) * (f n)) + (λn, f n) := 
      by repeat {ring_nf},
    rw d, 
    apply negl_add_negl_negl,
    exact hk,
    exact hf,
  },
end

lemma const_mul_negl_negl {f : ℕ → ℝ} (m : ℝ) : 
negligible f → negligible (λn, m * (f n)) := 
begin
  intro hf,
  -- Use Archimedian property to get arch : ℕ with abs m < arch
  have arch := exists_nat_gt (abs m),
  cases arch with k hk,
  apply bounded_negl_negl,

  { -- Demonstrate a negligible function kf  
    have kf_negl := nat_mul_negl_negl k hf,
    exact kf_negl,
  },

  { -- Show kf bounds mf from above
    intro n,
    have h : abs m ≤ abs (k : ℝ) := 
    calc 
      abs m ≤ (k : ℝ) : le_of_lt hk
        ... = abs (k : ℝ) : (nat.abs_cast k).symm,

    have goal : abs (m * f n) ≤ abs ((k : ℝ) * f n) := 
    calc 
      abs (m * f n) = abs m * abs (f n) : by rw abs_mul
                ... ≤ abs (k : ℝ) * abs (f n) : mul_mono_nonneg (abs_nonneg (f n)) h
                ... = abs ((k : ℝ) * f n) : by rw <- abs_mul,
      
    exact goal,
  },  
end

theorem neg_exp_negl : negligible ((λn, (1 : ℝ) / 2^n) : ℕ → ℝ) := by sorry

-- Need to prove lim n^c/2^n = 0 by induction on c using L'Hopital's rule to apply inductive 
-- hypothesis
/-
begin
  let m := 2,
  have hm : 0 < 2 := zero_lt_two,
  have c2_negl := c2_mul_neg_exp_is_negl 2 hm,
  have r : (λ (n : ℕ), 16 * (1 / (2 ^ n * 16)): ℕ → ℝ) = ((λn, (1:ℝ)/2^n): ℕ → ℝ) := 
  begin
    funext,
    have h : (1:ℝ) / 2^n / 16 = (1:ℝ) / (2^n * 16) := div_div_eq_div_mul 1 (2^n) 16,
    rw <- h,
    ring_nf,  
  end,
  
  have goal := const_mul_negl_is_negl 16 c2_negl,
  norm_num at goal,
  rw <-r,
  exact goal,
end -/
