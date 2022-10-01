/-
 -----------------------------------------------------------
  Correctness of ElGamal public-key encryption scheme
 -----------------------------------------------------------
-/

import pke
import tactics 
import uniform

section elgamal

noncomputable theory 

parameters (G : Type) [fintype G] [comm_group G] [decidable_eq G] 
           (g : G) (g_gen_G : ∀ (x : G), x ∈ subgroup.zpowers g)
           (q : ℕ) [ne_zero q] [group (zmod q)] (G_card_q : fintype.card G = q) 
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
def encrypt (pk m : G) : pmf (G × G) := 
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
  simp only [eq_self_iff_true, if_true],
end


end elgamal
