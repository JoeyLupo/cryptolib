/-
 --------------------------------------------------------------
  Formalization of the discrete logarithm problem in zmod
 --------------------------------------------------------------
-/
import data.zmod.basic


namespace dlp

/--
  Calculate the discrete logarithm by brute forcing.
-/

def nat_power (base : ℕ) : ℕ → ℕ
| 0 := 1
| (nat.succ n) := base * nat_power n

meta def nat_dlp_brute_force (g : ℕ) (h : ℕ) : ℕ → ℕ
| n := if nat_power g n = h then n else nat_dlp_brute_force (n + 1)

/- Examples -/
-- 2 ^ 3 = 8
#eval nat_power 2 3
-- 2 ^ x = 8, then x = 3
#eval nat_dlp_brute_force 2 8 1
-- 2 ^ x = 1024, then x = 10
#eval nat_dlp_brute_force 2 1024 1

-- timeout
-- #eval nat_dlp_brute_force 2 1023 1


def p : ℕ := 941

def zmod_power (base : ℕ) : ℕ → zmod p 
| 0 := 1
| (nat.succ n) := base * zmod_power n

meta def zmod_dlp_brute_force (g : ℕ) (h : zmod p) : ℕ → zmod p
| n := if zmod_power g n = h then n else zmod_dlp_brute_force (n + 1)

/- Examples from An introduction to mathemeatical cryptography
   by Hoffstein - Pipher - Silverman Table 2.1: 
   Powers and discrete logarithms for g = 627 mod p = 941
-/

#eval zmod_power 627 1
#eval zmod_power 627 2
#eval zmod_power 627 3
#eval zmod_power 627 4
#eval zmod_power 627 5
#eval zmod_power 627 6
#eval zmod_power 627 7
#eval zmod_power 627 8
#eval zmod_power 627 9
#eval zmod_power 627 10

#eval zmod_dlp_brute_force 627 627 1
#eval zmod_dlp_brute_force 627 732 1
#eval zmod_dlp_brute_force 627 697 1
#eval zmod_dlp_brute_force 627 395 1
#eval zmod_dlp_brute_force 627 182 1
#eval zmod_dlp_brute_force 627 253 1
#eval zmod_dlp_brute_force 627 543 1
#eval zmod_dlp_brute_force 627 760 1
#eval zmod_dlp_brute_force 627 374 1
#eval zmod_dlp_brute_force 627 189 1


end dlp
