/-
 -----------------------------------------------------------
  Correctness and semantic security of ElGamal public-key 
  encryption scheme
 -----------------------------------------------------------
-/

import ddh
import security
import tactics 
import to_mathlib
import uniform

section elgamal

noncomputable theory 

parameters (G : Type) [fintype G] [comm_group G] [decidable_eq G] 
           (g : G) (g_gen_G : ∀ (x : G), x ∈ subgroup.gpowers g)
           (q : ℕ) [fact (0 < q)] (G_card_q : fintype.card G = q) 
           (A_state : Type)

include g_gen_G G_card_q

parameters (A1 : G → pmf (G × G × A_state))
           (A2 : G → G → A_state → pmf (zmod 2))
           
def A2' : G × G → A_state → pmf (zmod 2) := λ (gg : G × G), A2 gg.1 gg.2

-- generates a public key `g^x.val`, and private key `x`
def keygen : pmf (G × (zmod q)) := 
do 
  x ← uniform_zmod q,
  pure (g^x.val, x)

-- encrypt takes a pair (public key, message)
def encrypt (pk m: G) : pmf (G × G) := 
do
  y ← uniform_zmod q,
  pure (g^y.val, pk^y.val * m)

-- `x` is the secret key, `c.1` is g^y, the first part of the 
-- cipher text returned from encrypt, and `c.2` is the 
-- second value returned from encrypt
def decrypt (x : zmod q)(c : G × G) : G := 
	(c.2 / (c.1^x.val)) 



/- 
  -----------------------------------------------------------
  Proof of correctness of ElGamal
  -----------------------------------------------------------
-/

lemma decrypt_eq_m (m : G) (x y: zmod q) : decrypt x ((g^y.val), ((g^x.val)^y.val * m)) = m := 
begin
  simp [decrypt],
  rw (pow_mul g x.val y.val).symm,
  rw (pow_mul g y.val x.val).symm,
  rw mul_comm y.val x.val,
  repeat {rw group.div_eq_mul_inv},
  conv_lhs {rw [mul_assoc, mul_comm m _, <- mul_assoc]},
  rw mul_inv_self _,
  exact one_mul m,
end

theorem elgamal_correctness : pke_correctness keygen encrypt decrypt :=
begin
  simp [pke_correctness],
  intro m,
  simp [enc_dec, keygen, encrypt, bind],
  bind_skip_const with x,
  simp [pure],
  bind_skip_const with y,
  simp_rw decrypt_eq_m,
  simp,
end



/- 
  -----------------------------------------------------------
  Proof of semantic security of ElGamal
  -----------------------------------------------------------
-/

def D (gx gy gz : G) : pmf (zmod 2) := 
do 
  m ← A1 gx,
  b ← uniform_2,
  mb ← pure (if b = 0 then m.1 else m.2.1),
  b' ← A2 gy (gz * mb) m.2.2,
  pure (1 + b + b')

/- 
  The probability of the attacker (i.e. the composition of A1 and A2) 
  winning the semantic security game (i.e. guessing the correct bit), 
  w.r.t. ElGamal is equal to the probability of D winning the game DDH0. 
-/
theorem SSG_DDH0 : SSG keygen encrypt A1 A2' =  DDH0 G g g_gen_G q G_card_q D :=
begin
  simp only [SSG, DDH0, bind, keygen, encrypt, D],
  simp_rw pmf.bind_bind (uniform_zmod q),
  bind_skip with x,
  simp [pure],
  simp_rw pmf.bind_comm (uniform_zmod q),
  bind_skip with m,
  bind_skip with b,
  bind_skip with y,
  simp only [A2'],
  rw pow_mul g x.val y.val,
end

def Game1 : pmf (zmod 2) :=
do 
  x ← uniform_zmod q,
  y ← uniform_zmod q,
  m ← A1 (g^x.val),
  b ← uniform_2,
  ζ ← (do z ← uniform_zmod q, mb ← pure (if b = 0 then m.1 else m.2.1), pure (g^z.val * mb)),
  b' ← A2 (g^y.val) ζ m.2.2,
  pure (1 + b + b')

def Game2 : pmf (zmod 2) :=
do
  x ← uniform_zmod q,
  y ← uniform_zmod q,
  m ← A1 (g^x.val),
  b ← uniform_2,
  ζ ← (do z ← uniform_zmod q, pure (g^z.val)),
  b' ← A2 (g^y.val) ζ m.2.2,
  pure (1 + b + b')

/- 
  The probability of the attacker (i.e. the composition of A1 and A2) 
  winning Game1 (i.e. guessing the correct bit) is equal to the 
  probability of D winning the game DDH1. 
-/
theorem Game1_DDH1 : Game1 = DDH1 G g g_gen_G q G_card_q D := 
begin
  simp only [DDH1, Game1, bind, D],
  bind_skip with x,
  bind_skip with y,
  simp_rw pmf.bind_bind (A1 _),
  conv_rhs {rw pmf.bind_comm (uniform_zmod q)},
  bind_skip with m,
  simp_rw pmf.bind_bind (uniform_zmod q),
  conv_lhs {rw pmf.bind_comm (uniform_2)},
  bind_skip with z,
  conv_rhs {rw pmf.bind_bind (uniform_2)},
  bind_skip with b,
  simp_rw pmf.bind_bind,
  bind_skip with mb,
  simp [pure],
end

lemma exp_bij : 
  function.bijective (λ (z : zmod q), g ^ z.val) := 
begin
  apply (fintype.bijective_iff_surjective_and_card _).mpr,
  split,

  { -- (λ (z : zmod q), g ^ z.val) surjective
    intro gz, 
    have hz := subgroup.mem_gpowers_iff.mp (g_gen_G gz),
    cases hz with z hz,
    cases z,

    { -- Case : z = z' for (z : ℕ)
      let zq := z % q,
      use zq,
      have h1 : (λ (z : zmod q), g ^ z.val) ↑zq = g ^ (zq : zmod q).val := rfl,
      rw h1,
      rw zmod.val_cast_of_lt,
      {
        have goal : gz = g ^ zq := 
        calc
           gz = g ^ int.of_nat z : hz.symm
          ... = g ^ z  : by simp
          ... = g ^ (z % q + q * (z / q)) : by rw nat.mod_add_div z q
          ... = g ^ (z % q) * g ^ (q * (z / q)) : by rw pow_add
          ... = g ^ (z % q) * (g ^ q) ^ (z / q) : by rw pow_mul
          ... = g ^ (z % q) * (g ^ fintype.card G) ^ (z / q) : by rw <- G_card_q
          ... = g ^ (z % q) : by simp [pow_card_eq_one]
          ... = g ^ zq : rfl,
        exact goal.symm, 
      },
      exact nat.mod_lt z _inst_4.out,
    },

    { -- Case : z = - (1 + z') for (z' : ℕ)
      let zq := (q - (z + 1) % q ) % q,
      use zq,
      have h1 : (λ (z : zmod q), g ^ z.val) ↑zq = g ^ (zq : zmod q).val := rfl,
      rw h1,
      rw zmod.val_cast_of_lt,
      {
        have h1 : (z + 1) % q ≤ fintype.card G := 
        begin
          rw G_card_q,
          apply le_of_lt,
          exact nat.mod_lt _ _inst_4.out,
        end,

        have goal : gz = g ^ zq := 
        calc
           gz = g ^ int.neg_succ_of_nat z : hz.symm 
          ... = (g ^ z.succ)⁻¹  : by rw gpow_neg_succ_of_nat
          ... = (g ^ (z + 1))⁻¹ : rfl
          ... = (g ^ ((z + 1) % fintype.card G))⁻¹ : by rw pow_eq_mod_card G g (z + 1)
          ... = (g ^ ((z + 1) % q))⁻¹ : by rw G_card_q
          ... = g ^ (fintype.card G - (z + 1) % q) : inv_pow_eq_card_sub_pow G g _ h1
          ... = g ^ (q - ((z + 1) % q)) : by rw G_card_q
          ... = g ^ ((q - (z + 1) % q) % q
                  + q * ((q - (z + 1) % q) / q)) : by rw nat.mod_add_div
          ... = g ^ ((q - (z + 1) % q) % q) 
                  * g ^ (q * ((q - (z + 1) % q) / q)) : by rw pow_add
          ... = g ^ ((q - (z + 1) % q) % q) 
                  * (g ^ q) ^ ((q - (z + 1) % q) / q) : by rw pow_mul
          ... = g ^ ((q - (z + 1) % q) % q) 
                  * (g ^ fintype.card G) ^ ((q - (z + 1) % q) / q) : by rw <- G_card_q
          ... = g ^ ((q - (z + 1) % q) % q) : by simp [pow_card_eq_one]
          ... = g ^ zq : rfl,
        exact goal.symm, 
      },

      exact nat.mod_lt _ _inst_4.out,  
    },
  },

  { -- fintype.card (zmod q) = fintype.card G
    rw G_card_q,
    exact zmod.card q,
  },
end

lemma exp_mb_bij (mb : G) : function.bijective (λ (z : zmod q), g ^ z.val * mb) := 
begin
  have h : (λ (z : zmod q), g ^ z.val * mb) = 
    ((λ (m : G), (m * mb)) ∘ (λ (z : zmod q), g ^ z.val)) := by simp,
  rw h,
  apply function.bijective.comp,

  { -- (λ (m : G), (m * mb)) bijective
    refine fintype.injective_iff_bijective.mp _,
    intros x a hxa,
    simp at hxa,
    exact hxa,
  },

  { -- (λ (z : zmod q), g ^ z.val) bijective
    exact exp_bij,
  }
end

lemma G1_G2_lemma1 (x : G) (exp : zmod q → G) (exp_bij : function.bijective exp) : 
  ∑' (z : zmod q), ite (x = exp z) (1 : nnreal) 0 = 1 := 
begin
  have inv :=  function.bijective_iff_has_inverse.mp exp_bij,
  cases inv with exp_inv,
  have bij_eq : ∀ (z : zmod q), (x = exp z) = (z = exp_inv x) := 
  begin
    intro z,
    simp,
    split,

    { -- (x = exp z) → (z = exp_inv x)
      intro h,
      have h1 : exp_inv x = exp_inv (exp z) := congr_arg exp_inv h,
      rw inv_h.left z at h1,
      exact h1.symm,
    },

    { -- (z = exp_inv x) → (x = exp z) 
      intro h,
      have h2 : exp z = exp (exp_inv x) := congr_arg exp h,
      rw inv_h.right x at h2,
      exact h2.symm,
    },
  end,
  simp_rw bij_eq,
  simp,
end

lemma G1_G2_lemma2 (mb : G) : 
  (uniform_zmod q).bind (λ (z : zmod q), pure (g^z.val * mb)) =
  (uniform_zmod q).bind (λ (z : zmod q), pure (g^z.val))  := 
begin
  simp [pmf.bind],
  simp_rw uniform_zmod_prob,
  ext,
  simp only [pure, pmf.pure, coe_fn, has_coe_to_fun.coe, nnreal.tsum_mul_left],
  norm_cast,
  simp,
  apply or.intro_left,
  repeat {rw G1_G2_lemma1 x},
  exact exp_bij,
  exact exp_mb_bij mb,
end
 
lemma G1_G2_lemma3 (m : pmf G) : 
  m.bind (λ (mb : G), (uniform_zmod q).bind (λ (z : zmod q), pure (g^z.val * mb))) =
  (uniform_zmod q).bind (λ (z : zmod q), pure (g^z.val)) := 
begin
  simp_rw G1_G2_lemma2 _,
  bind_skip_const with m,
  congr,
end

/- 
  The probability of the attacker (i.e. the composition of A1 and A2) 
  winning Game1 (i.e. guessing the correct bit) is equal to the 
  probability of the attacker winning Game2.
-/
theorem Game1_Game2 : Game1 = Game2 := 
begin
  simp only [Game1, Game2],
  bind_skip with x,
  bind_skip with y, 
  bind_skip with m,
  bind_skip with b,
  simp [bind, -pmf.bind_pure, -pmf.bind_bind],
  simp_rw pmf.bind_comm (uniform_zmod q),
  rw G1_G2_lemma3,
end

lemma G2_uniform_lemma (b' : zmod 2) : 
uniform_2.bind (λ (b : zmod 2), pure (1 + b + b')) = uniform_2 :=
begin
  fin_cases b' with [0,1],

  { -- b = 0
    ring_nf,
    ext,
    simp [uniform_2],
    rw uniform_zmod_prob a,
    simp_rw uniform_zmod_prob,
    simp [nnreal.tsum_mul_left],
    have zmod_eq_comm : ∀ (x : zmod 2), (a = 1 + x) = (x = 1 + a) := 
    begin
      intro x,
      fin_cases a with [0,1],

      { -- a = 0
        fin_cases x with [0,1],
        simp,
        ring_nf,
      }, 

      { -- a = 1
        fin_cases x with [0,1],
        simp [if_pos],
        ring_nf,
      },
    end,
    have h : ∑' (x : zmod 2), (pure (1 + x) : pmf (zmod 2)) a = 1 := 
    begin
      simp [pure, pmf.pure, coe_fn, has_coe_to_fun.coe],
      simp_rw zmod_eq_comm,
      simp,
    end,
    rw h,
    simp,
  },

  { -- b = 1
    ring_nf,
    have h : 
      uniform_2.bind (λ (b : zmod 2), pure (b + 0)) = uniform_2 := by simp [pure],
    exact h,
  },
end

/- 
  The probability of the attacker (i.e. the composition of A1 and A2) 
  winning Game2 (i.e. guessing the correct bit) is equal to a coin flip.
-/
theorem Game2_uniform : Game2 = uniform_2 :=
begin
  simp [Game2, bind],
  bind_skip_const with x,
  bind_skip_const with m,
  bind_skip_const with y,
  rw pmf.bind_comm uniform_2,
  simp_rw pmf.bind_comm uniform_2,
  bind_skip_const with z,
  bind_skip_const with ζ,
  bind_skip_const with b',
  exact G2_uniform_lemma b',
end

parameters (ε : nnreal) 

/- 
  The advantage of the attacker (i.e. the composition of A1 and A2) in
  the semantic security game `ε` is exactly equal to the advantage of D in 
  the Diffie-Hellman game. Therefore, assumining the decisional Diffie-Hellman
  assumption holds for the group `G`, we conclude `ε` is negligble, and 
  therefore ElGamal is, by definition, semantically secure.
-/
theorem elgamal_semantic_security (DDH_G : DDH G g g_gen_G q G_card_q D ε) : 
  pke_semantic_security keygen encrypt A1 A2' ε := 
begin
  simp only [pke_semantic_security],
  rw SSG_DDH0,
  have h : (((uniform_2) 1) : ℝ) = 1/2 := 
  begin
    simp only [uniform_2],
    rw uniform_zmod_prob 1,
    norm_cast,
  end,
  rw <- h,
  rw <- Game2_uniform,
  rw <- Game1_Game2,
  rw Game1_DDH1,
  exact DDH_G,
end

end elgamal
