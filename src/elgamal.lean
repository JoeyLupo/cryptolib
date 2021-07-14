/-
 -----------------------------------------------------------
  Correctness and semantic security of ElGamal public-key 
  encryption scheme
 -----------------------------------------------------------
-/

import ddh
import security

noncomputable theory

section elgamal

parameters (G : Type) [fintype G] [comm_group G] [decidable_eq G] 
           (g : G) (hGg : ∀ (x : G), x ∈ subgroup.gpowers g)
           (q : ℕ) [fact (0 < q)] (hGq : fintype.card G = q) 

def M := G
instance : comm_group M := _inst_2
def C := G × G 

parameters (A1 : G → pmf (M × M))
           (A2 : G × C → pmf (zmod 2))

-- g^x is the public key, and x is the secret key
def keygen : pmf (G × (zmod q)) := 
do 
  x ← uniform_zmod q,
  return (g^x.val, x)

-- encrypt takes a pair (pk, m)
def encrypt (m : G × M) : pmf C := 
do
  y ← uniform_zmod q,
  return (g^y.val, (m.1)^y.val * m.2)

-- TO-DO want zmod q × C, but want nicer way to 
-- get at input than c.1.1
def decrypt (x : zmod q) (c : C) : G := 
  (c.2 / (c.1^x.val))



/- 
  -----------------------------------------------------------
  Proof of correctness of ElGamal
  -----------------------------------------------------------
-/

@[simp] lemma and_then_eq_bind {α β : Type} {m : Type → Type} [monad m] (a : m α) (b : m β) :
  a >> b = a >>= (λ _, b) := rfl

@[simp] lemma return_eq_pure {α : Type*} (a : α) : (@return pmf _ _ a) = pure a := rfl

lemma pure_eq_pure {α : Type*} (a : α) : (@pure pmf _ _ a) = pmf.pure a := rfl

@[simp] lemma pure_apply_self {α : Type*} (a : α) : (@pure pmf _ _ a) a = 1 :=
by simp [pure_eq_pure, pmf.pure_apply]

lemma pure_apply' {α : Type*} [decidable_eq α] (a b : α) :
  (@pure pmf _ _ a) b = if b = a then 1 else 0 :=
by { simp only [pure_eq_pure, pmf.pure_apply], split_ifs; refl }

lemma bind_eq_bind {α β : Type*} (v : pmf α) (f : α → pmf β) :
  v >>= f = v.bind f := rfl

lemma t1 (m : M) (x y: zmod q) : decrypt x (g^y.val, (g^x.val)^y.val * m) = m := 
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

lemma t2 (m : M) (x y: zmod q) : 
  return (if decrypt x (g^y.val, (g^x.val)^y.val * m) = m then (1 : zmod 2) else 0) 
  = (return 1 : pmf (zmod 2)) := 
begin
  rw t1,
  simp,
end

def t3b (m : M) (x : zmod q): (zmod q) → pmf (zmod 2) := 
  (λ (y : zmod q), (return 
  (if decrypt x (g ^ y.val, (g ^ x.val) ^ y.val * m) = m then (1 : zmod 2) else 0)))

lemma t3a (m : M) (x : zmod q) : t3b m x = (λ (y : zmod q), (return 1) ):= 
begin
  simp [t3b],
  ext,
  rw t1,
  simp,
end

lemma t3 (m : M) (x : zmod q) : 
  (do 
    y ← uniform_zmod q, 
    return (if decrypt x (g^y.val, (g^x.val)^y.val * m) = m then (1 : zmod 2) else 0)
  ) = return 1 := 
begin
  rw <- t3b,
  rw t3a,
  simp [bind],
  ext,
  simp,
  rw nnreal.tsum_mul_right,
  simp,
end

variables (H : Type) (f : G → G → H)
          (f1 : C → pmf H)
          (f2 : zmod q → pmf (zmod 2))
          (f3 : G × (zmod q) → pmf (zmod 2))

lemma enc_bind (m : M) (x : zmod q) : (encrypt (g^x.val, m)).bind f1 = 
  (do 
    y ← uniform_zmod q, 
    f1 (g^y.val, (g^x.val)^y.val * m)
  ) := 
begin
  simp [encrypt],
  simp [bind],
  simp [pure],
end

lemma keygen_bind : (keygen.bind f3) = 
  (do 
    x ← uniform_zmod q, 
    f3 (g^x.val, x)
  ) := 
begin
  simp [keygen],
  simp [bind],
  simp [pure],
end

lemma forall_imp_uniform_bind : 
  (∀ (a : zmod q), f2 a = return (1 : zmod 2)) → (uniform_zmod q).bind f2 = return 1 := 
begin
  intro h,
  simp [pmf.bind, pure, pmf.pure],
  simp [coe_fn],
  simp [has_coe_to_fun.coe],
  ext,
  simp,
  simp_rw h, 
  simp [pure, pmf.pure],
  split_ifs,
  exact pmf.tsum_coe (uniform_zmod q),
  exact tsum_zero,
end

lemma t4 (m : M) (x : zmod q) : 
  (do 
    (β, ζ) ← encrypt(g^x.val, m), 
    return (if decrypt x (β, ζ) = m then (1 : zmod 2) else 0)
  ) = return 1 := 
begin
  simp [bind],
  rw enc_bind,
  simp [bind],
  ext,
  simp,
  simp [pure],
  split_ifs,
  simp [t1],
  rw h,
  simp,
  simp [t1],
  simp_rw (if_neg h),
  exact tsum_zero,
end

lemma t5 (m : M) : 
  (do 
    x ← uniform_zmod q,
    (β, ζ) ← encrypt(g^x.val, m), 
    return (if decrypt x (β, ζ) = m then (1 : zmod 2) else 0)
  ) = return 1 := 
begin
  simp [bind],
  apply forall_imp_uniform_bind,
  exact t4 m,
end

def enc_dec (m : M) : pmf (zmod 2) := 
do
  (α, x) ← keygen,
  (β, ζ) ← encrypt(α, m),
  return (if decrypt x (β, ζ) = m then 1 else 0)

theorem elgamal_correct : ∀ (m : M), enc_dec m = return 1 := 
begin
  intro m,
  simp [enc_dec],
  simp [bind],
  simp [keygen_bind],
  delta enc_dec._match_2,
  delta enc_dec._match_1,
  exact t5 m,
end



/- 
  -----------------------------------------------------------
  Proof of semantic security of ElGamal
  -----------------------------------------------------------
-/

parameters (ε : nnreal) 
           (DDH_G : DDH G g q A2 ε)

theorem elgamal_secure :  is_semantically_secure keygen encrypt A1 A2 ε := 
begin
  sorry,  
end

end elgamal