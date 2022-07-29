/-
Galois Fields arithmetic
-/
import data.bitvec.basic
import data.vector.basic

/- All operations are done in GF(2^3) -/
def n : ℕ := 3

/- Values in GF(2^3) represent the decimal range [0..7] -/
def zero : bitvec n := 0
def one : bitvec n := 1
def two : bitvec n := 2
def three : bitvec n := 3
def four : bitvec n := 4
def five : bitvec n := 5
def six : bitvec n := 6
def seven : bitvec n := 7

/- Addition in GF(2^n) is just the bitwise XOR -/

/- 
Examples:
Addition table taken from http://www.ee.unb.ca/cgi-bin/tervo/galois3.pl?p=2&C=1&D=1&A=1

#eval (six.xor three).to_nat
#eval (two.xor six).to_nat
#eval (four.xor seven).to_nat
#eval (two.xor three).to_nat
-/

/- 
Multiplication in GF(2^n) using direct bitwise operations
https://engineering.purdue.edu/kak/compsec/NewLectures/Lecture7.pdf
Sections 7.9 and 7.10
-/

/-
The primitive polynomial for GF(2^3) is x^3 + x + 1
This is 1011 but in 7.10 algo the right bit is removed
So our modulo will be 011 
-/
def primitive_mod : bitvec n := bit1 (bit1 0)

-- A function to get the most significant bit from a bit string
def get_msb (input : bitvec n): bool := input.head

-- A function that multiplies the input by x 
def multiply_by_x (input : bitvec n ) : bitvec n := 
match get_msb input with
  | tt := bitvec.xor (bitvec.shl input 1) primitive_mod
  | ff := bitvec.shl input 1
end

-- Get the bit on each possible position
-- (Easy for 2^3 but this does not scale well)
def pos1 (input: bitvec n): bool := vector.head input
def pos2 (input: bitvec n): bool := vector.head (vector.tail input)
def pos3 (input: bitvec n): bool := vector.head (vector.tail (vector.tail input))

-- Depending on the value of the bit in position do 
-- multiply_by_x logic the number of times needed
def mul1 (input1: bitvec n) (input2: bitvec n) : bitvec n :=
if pos1 input2 then multiply_by_x (multiply_by_x input1) else zero

def mul2 (input1: bitvec n) (input2: bitvec n) : bitvec n :=
if pos2 input2 then multiply_by_x input1 else zero

def mul3 (input1: bitvec n) (input2: bitvec n) : bitvec n :=
if pos3 input2 then input1 else zero

-- Multiply and sum all the values for a final result
def mul (input1: bitvec n) (input2: bitvec n) : bitvec n :=
((mul1 input1 input2).xor (mul2 input1 input2)).xor (mul3 input1 input2)

/-
Examples:
Multiplication table taken from http://www.ee.unb.ca/cgi-bin/tervo/galois3.pl?p=2&C=1&D=1&A=1

-- 5 X 4 = 2
#eval (mul five four).to_nat

-- 6 X 4 = 5
#eval (mul six four).to_nat

-- 6 X 3 = 1
#eval (mul six three).to_nat

-- 4 X 4 = 6
#eval (mul four four).to_nat

-- 5 X 6 = 3
#eval (mul five six).to_nat

-- 2 X 1 = 2
#eval (mul two one).to_nat

-- 7 X 7 = 3
#eval (mul seven seven).to_nat

-- 4 X 1 = 4
#eval (mul four one).to_nat

-- 2 X 5 = 1
#eval (mul two five).to_nat
-/

-- TODO: inverses
