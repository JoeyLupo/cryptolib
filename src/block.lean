/-
 -----------------------------------------------------------
  Formalization and correctness of block ciphers
 -----------------------------------------------------------
-/

import data.matrix.basic
import data.zmod.basic
import linear_algebra.matrix.nonsingular_inverse

open_locale matrix

namespace hill

-- Hill cipher: A generalization of the affine cipher
--
-- If block = 2 then this is a digraphic cipher.
-- If block > 2 then this is a poligraphic cipher.
-- If block = 1 then this is a reduction to the affine cipher.

-- All operations will be mod 26.
def m : ℕ := 26

-- The size of the block
variables block : ℕ

-- The key matrix
variable A : matrix (fin block) (fin block) (zmod m)

-- The plaintext vector
variable P : matrix (fin block) (fin 1) (zmod m)

-- The ciphertext vector
variable C : matrix (fin block) (fin 1) (zmod m)

-- Encryption
def encrypt :
  matrix (fin block) (fin 1) (zmod m) := A ⬝ P

-- Decryption
noncomputable def decrypt : 
  matrix (fin block) (fin 1) (zmod m) := A⁻¹ ⬝ P

-- Proof of correctness
lemma dec_undoes_enc (h : A.det = 1): 
  P = decrypt block A (encrypt block A P) :=
begin
  unfold encrypt,
  unfold decrypt,
  rw ← matrix.mul_assoc,
  rw matrix.nonsing_inv_mul,
  finish,
  finish,
end

end hill
