/-
 -----------------------------------------------------------
  Correctness of RSA public-key encryption scheme

  RSA encryption undoes decryption as originally 
  described in the [RSA paper](https://people.csail.mit.edu/rivest/Rsapaper.pdf).

  Original file: https://github.com/aronerben/lean-rsa/blob/main/src/rsa.lean

 -----------------------------------------------------------
-/

import data.nat.basic
import data.nat.modeq
import data.nat.prime
import data.nat.totient
import field_theory.finite.basic

variables (a b c d n : ℕ)

-- Helpers for proof
lemma mod_pow_mod : ((a % n) ^ b) % n = (a ^ b) % n :=
begin
  -- Use either change here or write MOD form directly as goal
  change (a % n) ^ b ≡ (a ^ b) [MOD n],
  apply nat.modeq.pow,
  exact nat.mod_modeq _ _,
end

lemma mul_mod_right_distrib : (a * b) % n = ((a % n) * (b % n)) % n :=
begin
  change (a * b) ≡ a % n * (b % n) [MOD n],
  apply nat.modeq.mul,
  repeat {apply nat.modeq.symm, exact nat.mod_modeq _ _},
end

variables (msg pub_e p q priv : ℕ)

-- Encryption
def enc : ℕ := (msg ^ pub_e) % (p * q)

-- Decryption
def dec (enc : ℕ) : ℕ := (enc ^ priv) % (p * q)

lemma mul_coprime_or_coprime_and
  (prime_p : p.prime)
  (prime_q : q.prime)
  (diff_pq : p ≠ q)
  : (p.coprime msg ∧ q.coprime msg) ∨ (¬p.coprime msg ∨ ¬q.coprime msg) :=
begin
  by_cases h : (p * q).coprime msg,
  { left,
    exact ⟨nat.coprime.coprime_mul_right h, nat.coprime.coprime_mul_left h⟩,
  },
  {
    right,
    rw nat.prime.not_coprime_iff_dvd at h,
    cases h with k ncp,
    cases ncp with prime_k ncp,
    cases ncp with k_dvd_pq k_dvd_msg,
    rw nat.prime.dvd_mul prime_k at k_dvd_pq,
    cases k_dvd_pq with k_dvd_p k_dvd_q,
    -- TODO use meta tactics to combine these two similar parts
    { rw nat.dvd_prime prime_p at k_dvd_p,
      cases k_dvd_p with k_one k_p,
      { have k_ne_one : k ≠ 1 := nat.prime.ne_one prime_k,
        exact absurd k_one k_ne_one,
      },
      { rw k_p at k_dvd_msg,
        left,
        rw ←nat.prime.dvd_iff_not_coprime prime_p,
        assumption,
      },
    },
    { rw nat.dvd_prime prime_q at k_dvd_q,
      cases k_dvd_q with k_one k_q,
      { have k_ne_one : k ≠ 1 := nat.prime.ne_one prime_k,
        exact absurd k_one k_ne_one,
      },
      { rw k_q at k_dvd_msg,
        right,
        rw ←nat.prime.dvd_iff_not_coprime prime_q,
        assumption,
      },
    },
  },
end

theorem dec_undoes_enc
-- These are the picking requirements
  (prime_p : p.prime)
  (prime_q : q.prime)
  (diff_pq : p ≠ q)
  (one_lt_pub_e : 1 < pub_e)
  (msg_lt_pq : msg < (p * q))
  (pub_e_lt_totient : pub_e < (p * q).totient)
  (pub_e_coprime_totient : pub_e * priv ≡ 1 [MOD (p * q).totient])
  (h : (p * q).coprime msg ∨ ¬(p * q).coprime msg)
  : msg = dec p q priv (enc msg pub_e p q) :=
begin
  have msg_coprime_or_not := mul_coprime_or_coprime_and msg _ _ prime_p prime_q diff_pq,
  rw [enc, dec, mod_pow_mod, ←pow_mul],
  have msg_zero_or_gt : 0 = msg ∨ 0 < msg
    := nat.eq_or_lt_of_le (nat.zero_le msg),
  rw nat.modeq.comm at pub_e_coprime_totient,
  have one_le_mul_pub_e_priv : 1 ≤ pub_e * priv
    := begin
       apply nat.modeq.le_of_lt_add pub_e_coprime_totient _,
       apply nat.lt_add_left,
       exact nat.lt_trans one_lt_pub_e pub_e_lt_totient,
    end,
  cases msg_zero_or_gt with eq_zero gt_zero,
  { rw [←eq_zero, zero_pow one_le_mul_pub_e_priv],
    simp only [nat.zero_mod]},
  { conv
    begin
      to_lhs,
      rw ←nat.mod_eq_of_lt msg_lt_pq,
    end,
    have p_coprime_q : p.coprime q
      := (nat.coprime_primes prime_p prime_q).mpr diff_pq,
    rw [←nat.modeq, ←nat.modeq_and_modeq_iff_modeq_mul p_coprime_q],
    split,
    all_goals { rw nat.modeq_iff_dvd' one_le_mul_pub_e_priv at pub_e_coprime_totient,
      cases pub_e_coprime_totient with k h₁,
      have h₂ : (pub_e * priv - 1).succ = ((p * q).totient * k).succ
        := congr_arg nat.succ h₁,
      rw [nat.sub_one,
         nat.succ_pred_eq_of_pos (nat.lt_of_succ_le one_le_mul_pub_e_priv)]
         at h₂,
      rw h₂,
      rw [pow_succ,
        pow_mul,
        nat.modeq, mul_mod_right_distrib,
        ←mod_pow_mod],
    },
    show msg % q = msg % q * ((msg ^ (p * q).totient % q) ^ k % q) % q,
    rw mul_comm p,
    show msg % p = msg % p * ((msg ^ (p * q).totient % p) ^ k % p) % p,
    all_goals {
      cases msg_coprime_or_not with coprime ncoprime,
      { rw [nat.totient_mul p_coprime_q,
           pow_mul,
           ←mod_pow_mod _ q.totient]
        <|> rw [nat.totient_mul (nat.coprime.symm p_coprime_q),
               pow_mul,
               ←mod_pow_mod _ p.totient],
        have h₃ := nat.modeq.pow_totient,
        rw nat.modeq at h₃,
        rw h₃ (nat.coprime.symm coprime.1)
        <|> rw h₃ (nat.coprime.symm coprime.2),
        repeat {rw nat.mod_eq_of_lt (nat.prime.one_lt prime_p)
                <|> rw nat.mod_eq_of_lt (nat.prime.one_lt prime_q)
                <|> rw one_pow},
        simp only [mul_one, nat.mod_mod],
      },
    },
    -- TODO use meta tactics to combine these two similar parts
    { cases ncoprime with np nq,
      { rw [nat.totient_mul p_coprime_q,
           pow_mul,
           ←mod_pow_mod _ q.totient],
        rw ←nat.prime.dvd_iff_not_coprime prime_p at np,
        rw [←nat.modeq_zero_iff_dvd, nat.modeq] at np,
        rw [mul_mod_right_distrib, np],
        simp only [nat.zero_mod, zero_mul],
      },
      { have msg_coprime_p : msg.coprime p := begin
          rw [nat.coprime_comm, nat.prime.coprime_iff_not_dvd prime_p],
          rw ←nat.prime.dvd_iff_not_coprime prime_q at nq,
          exact begin
            intro p_dvd_msg,
            have pq_dvd_msg
              := nat.prime.dvd_mul_of_dvd_ne
                 diff_pq prime_p prime_q p_dvd_msg nq,
            have pq_not_dvd_msg
              := nat.not_dvd_of_pos_of_lt gt_zero msg_lt_pq,
            exact absurd pq_dvd_msg pq_not_dvd_msg,
          end,
        end,
        rw [nat.totient_mul p_coprime_q,
          pow_mul,
          ←mod_pow_mod _ q.totient],
        have h₃ := nat.modeq.pow_totient,
        rw nat.modeq at h₃,
        rw h₃ msg_coprime_p,
        repeat {rw nat.mod_eq_of_lt (nat.prime.one_lt prime_p)
          <|> rw one_pow},
        simp only [mul_one, nat.mod_mod],
      },
    },
    { cases ncoprime with np nq,
      { have msg_coprime_q : msg.coprime q := begin
          rw [nat.coprime_comm, nat.prime.coprime_iff_not_dvd prime_q],
          rw ←nat.prime.dvd_iff_not_coprime prime_p at np,
          exact begin
            intro q_dvd_msg,
            have pq_dvd_msg
              := nat.prime.dvd_mul_of_dvd_ne
                 diff_pq prime_p prime_q np q_dvd_msg,
            have pq_not_dvd_msg
              := nat.not_dvd_of_pos_of_lt gt_zero msg_lt_pq,
            exact absurd pq_dvd_msg pq_not_dvd_msg,
          end,
        end,
        rw [nat.totient_mul (nat.coprime.symm p_coprime_q),
          pow_mul,
          ←mod_pow_mod _ p.totient],
        have h₃ := nat.modeq.pow_totient,
        rw nat.modeq at h₃,
        rw h₃ msg_coprime_q,
        repeat {rw nat.mod_eq_of_lt (nat.prime.one_lt prime_q)
          <|> rw one_pow},
        simp only [mul_one, nat.mod_mod],
      },
      { rw [nat.totient_mul (nat.coprime.symm p_coprime_q),
           pow_mul,
           ←mod_pow_mod _ p.totient],
        rw ←nat.prime.dvd_iff_not_coprime prime_q at nq,
        rw [←nat.modeq_zero_iff_dvd, nat.modeq] at nq,
        rw [mul_mod_right_distrib, nq],
        simp only [nat.zero_mod, zero_mul],
      },
    },
  },
end