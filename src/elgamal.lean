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
           (g : G) (hGg : ∀ (x : G), x ∈ subgroup.gpowers g)
           (q : ℕ) [fact (0 < q)] (hGq : fintype.card G = q) 
           (A_state : Type)

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

-- `x` is the secret key, `gy` is g^y, the first part of the 
-- cipher text returned from encrypt, and `c` is the 
-- second value returned from encrypt
def decrypt (x : zmod q) (gy c : G) : G := 
  (c / (gy^x.val))



/- 
  -----------------------------------------------------------
  Proof of correctness of ElGamal
  -----------------------------------------------------------
-/

lemma decrypt_eq_m (m : G) (x y: zmod q) : decrypt x (g^y.val) ((g^x.val)^y.val * m) = m := 
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

def enc_dec (m : G) : pmf (zmod 2) := 
do 
  k ← keygen,
  c ← encrypt k.1 m,
  pure (if decrypt k.2 c.1 c.2 = m then 1 else 0)

theorem elgamal_correct : ∀ (m : G), enc_dec m = pure 1 := 
begin
  intro m,
  simp [enc_dec, keygen, encrypt, bind],
  apply bind_skip_const,
  intro x,
  simp [pure],
  apply bind_skip_const,
  intro y,
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
theorem SSG_DDH0 : SSG keygen encrypt A1 A2' = DDH0 G g q D :=
begin
  simp only [SSG, DDH0, bind, keygen, encrypt, D],
  simp_rw pmf.bind_bind (uniform_zmod q),
  apply bind_skip,
  intro x,
  simp [pure],
  simp_rw pmf.bind_comm (uniform_zmod q),
  apply bind_skip,
  intro m,
  apply bind_skip,
  intro b,
  apply bind_skip,
  intro y,
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
theorem Game1_DDH1 : Game1 = DDH1 G g q D := 
begin
  simp only [DDH1, Game1, bind, D],
  apply bind_skip,
  intro x,
  apply bind_skip, 
  intro y,
  simp_rw pmf.bind_bind (A1 _),
  conv_rhs {rw pmf.bind_comm (uniform_zmod q)},
  apply bind_skip,
  intro m,
  simp_rw pmf.bind_bind (uniform_zmod q),
  conv_lhs {rw pmf.bind_comm (uniform_2)},
  apply bind_skip,
  intro z,
  conv_rhs {rw pmf.bind_bind (uniform_2)},
  apply bind_skip,
  intro b,
  simp_rw pmf.bind_bind,
  apply bind_skip,
  intro mb,
  simp [pure],
  congr,
end

-- need function.bijective exp where exp is (λ (z : zmod q), g^z.val)
-- and (λ (z : zmod q), g^z.val * mb) for fixed mb
lemma G1_G2_lemma1(x : G) (exp : zmod q → G) : 
  ∑' (z : zmod q), ite (x = exp z) (1 : nnreal) 0 = 1 := 
begin
  sorry,
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
end

lemma G1_G2_lemma3 (m : pmf G) : 
  m.bind (λ (mb : G), (uniform_zmod q).bind (λ (z : zmod q), pure (g^z.val * mb))) =
  (uniform_zmod q).bind (λ (z : zmod q), pure (g^z.val)) := 
begin
  simp_rw G1_G2_lemma2,
  apply bind_skip_const,
  intro m,
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
  apply bind_skip,
  intro x,
  apply bind_skip,
  intro y,
  apply bind_skip,
  intro m,
  apply bind_skip,
  intro b,
  simp [bind, -pmf.bind_pure, -pmf.bind_bind],
  simp_rw pmf.bind_comm (uniform_zmod q),
  rw G1_G2_lemma3, 
end

lemma j (a x : zmod 2) : ite (a = 1 + x) (1 : nnreal) 0 = ite (a + 1 = x) 1 0 := 
begin
  fin_cases a with [0,1],

  { -- a = 0
    fin_cases x with [0,1],
    simp [if_pos],
    ring_nf,
  }, 

  { -- a = 1
    fin_cases x with [0,1],
    simp [if_pos],
    repeat {ring_nf},
  }, 
end

lemma Game2_lemma1 (b' : zmod 2) : 
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
    have h : ∑' (x : zmod 2), (pure (1 + x) : pmf (zmod 2)) a = 1 := 
    begin
      simp [pure, pmf.pure, coe_fn, has_coe_to_fun.coe],
      --simp_rw j a _,
      --fin_cases a with [0,1],
      sorry,
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
  apply bind_skip_const,
  intro x,
  apply bind_skip_const,
  intro m,
  apply bind_skip_const,
  intro y,
  rw pmf.bind_comm uniform_2,
  simp_rw pmf.bind_comm uniform_2,
  apply bind_skip_const,
  intro z,
  apply bind_skip_const,
  intro ζ,
  apply bind_skip_const, 
  intro b',
  exact Game2_lemma1 b',
end

parameters (ε : nnreal) 
          -- TO-DO how to make this like a parameter? 
           --(DDH_G : DDH G g q D ε)

/- 
  The advantage of the attacker (i.e. the composition of A1 and A2) in
  the semantic security game `ε` is exactly equal to the advantage of D in 
  the Diffie-Hellman game. Therefore, assumining the decisional Diffie-Hellman
  assumption holds for the group `G`, we conclude `ε` is negligble, and 
  therefore ElGamal is, by definition, semantically secure.
-/
theorem elgamal_secure (DDH_G : DDH G g q D ε) : 
  is_semantically_secure keygen encrypt A1 A2' ε := 
begin
  simp only [is_semantically_secure],
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