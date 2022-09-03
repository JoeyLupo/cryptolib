/-
Modes of operation
https://www.youtube.com/watch?v=Rk0NIQfEXBA
-/

import data.bitvec.basic

-- 128 and 256 bits are common block sizes,
-- but we leave this random.
variable n : ℕ


-- Electronic Cook Book mode
namespace ecb

-- Secret shared key
variable k : bitvec n

-- A random message
variable message : bitvec n

-- encryption is just xor of the message with the key
def encrypt : bitvec n := message.xor k 

-- 2 random messages
variable m1 : bitvec n
variable m2 : bitvec n

-- The problem with ecb mode is that given the same
-- message the ciphertext produced is the same
lemma same_message_produces_same_cipher 
  -- we assume messages are the same
  (h : m1 = m2) :
  -- then ciphertext produced is the same
  encrypt n m1 k = encrypt n m2 k :=
begin
  -- by hiphotesis
  rw h,
end 


end ecb


-- Before more modes, a few xor properties

-- Assuming (because i was not able to prove yet) that
-- two xors of the same value with a different value will produce
-- a different cipher.
axiom xor_result_is_different (a b c : bitvec n) (h: a ≠ b) : 
  c.xor a ≠ c.xor b

-- We can now prove that if we have randomness
-- then we have different ciphertext after nested xors.
lemma randomness_produces_different (a b c d : bitvec n): 
  a ≠ b → (d.xor c).xor a ≠ (d.xor c).xor b :=
begin
  apply xor_result_is_different,
end

-- Prove the above but both ways, given all data is the same except randomness:
-- * Different randomness used → Different cipher
-- * Diferent cipher → Different randomness used
lemma different_iff_different_randomness (a b c d : bitvec n):
  (d.xor c).xor a ≠ (d.xor c).xor b ↔ a ≠ b  :=
begin
  split,
  exact mt (congr_arg (λ (a : bitvec n), (bitvec.xor d c).xor a)),
  exact randomness_produces_different n a b c d,  
end


-- cipher block chaining mode
namespace cbc

-- A random message
variable m : bitvec n
-- A random shared secret key
variable k : bitvec n

-- An initial random vector, not a secret.
variable r1 : bitvec n

-- In a chain of blocks, this is the result of encrypting
-- the previous block.
-- For example, if we are encrypting the second block then: 
-- r2 = encrypt m r1 k
-- but we leave this random as we only need that r1 ≠ r2
variable r2 : bitvec n

-- Encryption is xor of the message with the random vector
-- and then the output xored with the key
def encrypt : bitvec n := (m.xor r1).xor k

-- Encrypting the same message in cbc mode will produce
-- different ciphertext thanks to the randomness added.
lemma same_message_produces_different_cipher (h1 : r1 ≠ r2) :
 encrypt n m r1 k ≠ encrypt n m r2 k :=
begin
  unfold encrypt,
  rw different_iff_different_randomness,
  exact h1,
end  

  
end cbc


-- Counter mode: Very similar to prove to CBC mode
namespace ctr

-- A random message
variable m : bitvec n
-- A random shared secret key
variable k : bitvec n

-- An initial nonce, not a secret.
variable nonce1 : bitvec n

-- In a chain of blocks, this is nonce1 + block number
-- For example, if we are encrypting the second block and nonce1 = 0, then: 
-- nonce2 = 0 + 2 = 2
-- but we leave this random as we only need that r1 < r2
variable nonce2 : bitvec n

-- Encryption is xor of the nonce with the key
-- and then the output xored with the message
def encrypt : bitvec n := (nonce1.xor k).xor m

-- Encrypting the same message in ctr mode will produce
-- different ciphertext thanks to the nonce.
lemma same_message_produces_different_cipher
  -- we assume nonce2 > nonce2 but we just need nonce1 ≠ nonce2
  (h1: nonce1 < nonce2) :
  encrypt n nonce1 k m ≠ encrypt n nonce2 k m :=
begin
  unfold encrypt,
  rw different_iff_different_randomness,
  exact ne_of_lt h1,
end



end ctr