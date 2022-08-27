import data.bitvec.basic
import data.bitvec.core
import data.list.basic
import control.random

section lfsr


-- Example: https://www.youtube.com/watch?v=Ks1pw1X22y4

-- The video shows how to random generate numbers. 
-- This is not cryptographically secure but just a decent random number generator technique.
-- TODO: This is currently a naive implementation, not proving anything.

-- We will be working with bitvectors of length 4
def n : ℕ := 4

-- A seed number that will generate a random initial state.
def seed_for_generator : ℕ := 44343344

-- An initial state, can be anything except "b0000".
def initial_state : bitvec n := (rand_nat (mk_std_gen seed_for_generator) 1 16).1

-- Taps located at bit 4 and 3.
-- Feed polynomial is then x^4 + x^3 + 1: 1100 (https://en.wikipedia.org/wiki/Linear-feedback_shift_register#Example_polynomials_for_maximal_LFSRs)
-- However, we represent this in reverse order.
def taps : bitvec n := bit1 (bit1 (bit0 0))

-- Taps polynomial should be irreducible and primitive in order to produce 
-- maximum length sequences: https://www.ece.unb.ca/tervo/ece4253/polyprime.shtml
--
-- The taps are hard coded into the program, this means we can't just use
-- any tap setting currently but just 0011.

-- Get the bit at position as a boolean
def bit_at_position (input : bitvec n) (pos : fin n) : bool := input.nth pos

-- Convert the last bit to a bitvec of length 1
def last_as_bitvec (input : bitvec n) : bitvec 1 := 
  if bit_at_position input (fin.of_nat (n-1)) then bitvec.one 1
  else bitvec.zero 1

-- Convert the last bit -1 to a bitvec of length 1
def last_minus_one_as_bitvec (input : bitvec n) : bitvec 1 := 
  if bit_at_position input (fin.of_nat (n-2)) then bitvec.one 1
  else bitvec.zero 1

-- xor the 2 bits
def xored (input : bitvec n) : bitvec 1 := bitvec.xor (last_as_bitvec input) (last_minus_one_as_bitvec input)

-- Do one round of computation
def generate_one (input : bitvec n) : bitvec n := bitvec.fill_shr input 1 (xored input).head

-- Do n rounds of computations
def generate_n : ℕ → bitvec n → bitvec n
| 0 m := generate_one m
| (n+1) m := generate_n n (generate_one m)

-- The maximum period.
def maximum_period : ℕ := (2^n) - 1

-- When counting iterations we start at 0 so we expect to get the initial state
-- back again at maximum_period - 1
def maximum_period_counter : ℕ := maximum_period - 1

-- Test that after maximum_period iterations, we are back at the initial state
#eval initial_state
#eval generate_n maximum_period_counter initial_state

-- Test all outputs are different - naive way.
def r1 : bitvec n := generate_one initial_state
def r2 : bitvec n := generate_one r1
def r3 : bitvec n := generate_one r2
def r4 : bitvec n := generate_one r3
def r5 : bitvec n := generate_one r4
def r6 : bitvec n := generate_one r5
def r7 : bitvec n := generate_one r6
def r8 : bitvec n := generate_one r7
def r9 : bitvec n := generate_one r8
def r10 : bitvec n := generate_one r9
def r11 : bitvec n := generate_one r10
def r12 : bitvec n := generate_one r11
def r13 : bitvec n := generate_one r12
def r14 : bitvec n := generate_one r13
def r15 : bitvec n := generate_one r14

-- We know that we get back to initial state after maximum_period
#eval if (initial_state = r15) then tt else ff

-- Insert all the results into a list.
def results_list : list (bitvec n) := [
  initial_state,
  r1,
  r2,
  r3,
  r4,
  r5,
  r6,
  r7,
  r8,
  r9,
  r10,
  r11,
  r12,
  r13,
  r14,
  r15
]

-- At least one we have one duplicate here as initial_state = r15
#eval results_list.length

-- Dedup the list
#eval results_list.dedup.length

-- List length is now = maximum_period
#eval if results_list.dedup.length = maximum_period then tt else ff


end lfsr
