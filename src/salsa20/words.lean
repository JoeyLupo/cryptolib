/-
  Section 2 : Words
  http://cr.yp.to/snuffle/spec.pdf

  This file formalize the ARX building blocks of salsa20:
  https://en.wikipedia.org/wiki/Block_cipher#ARX_(add%E2%80%93rotate%E2%80%93XOR)

  Utility functions to be used in higher levels of salsa20 are also here.

  Numeric examples are taken form the spec.
-/
import data.bitvec.basic
import data.list.basic
import data.zmod.basic
import tactics

-- A byte is a bitvec of 8 bits
def byte_len : ℕ := 8
-- A word is a bitvec of 32 bits
def word_len : ℕ := 32 

-- sum of 2 words

-- sums are done modulo 2^32
def mod : ℕ := (2^word_len)

-- convert a 32 bitvector to a zmod
def bitvec_as_mod (v : bitvec word_len) : zmod mod := v.to_nat

-- convert two bitvec to the sum of them modulo 2^32
def sum_as_mod (u v : bitvec word_len) : zmod mod := 
  bitvec_as_mod u + bitvec_as_mod v

-- convert a mod 2^32 to a nat
def mod_as_nat (sum : zmod mod) : ℕ := sum.val

-- convert a nat to a bitvec
def nat_as_bitvec (n : ℕ) : bitvec word_len := bitvec.of_nat word_len n

-- example from the spec: 0xc0a8787e + 0x9fd1161d = 0x60798e9b
def u : bitvec word_len := 0xc0a8787e
def v : bitvec word_len := 0x9fd1161d

#eval (nat_as_bitvec (mod_as_nat (sum_as_mod u v))).to_nat
#eval 0x60798e9b

-- xor = just bitwise xor

def xor' (v1 v2 : bitvec word_len): bitvec word_len :=
  v1.xor v2

-- example from the spec: 0xc0a8787e XOR 0x9fd1161d = 0x5f796e63
def x1 : bitvec 32 := 0xc0a8787e
def x2 : bitvec 32 := 0x9fd1161d

#eval (xor' x1 x2).to_nat
#eval 0x5f796e63


-- rotation

-- given an input and a position, get the bit at pos as a bitvec of lenght 1
def bit_n (input: bitvec word_len) (n : fin 32): bitvec 1 := 
  if input.nth n then bitvec.one 1 else bitvec.zero 1 

-- given a vector and a shift number n, shift the vector to the left by n
def shift_left (v : bitvec word_len) (shift : ℕ): bitvec 32 := 
  bitvec.shl v shift

-- reduce a given bitvector to a given size
def reduce_bitvector (input : bitvec word_len) (reduce_to : ℕ) : bitvec (min reduce_to word_len)  := 
  (vector.take reduce_to input)

-- a pretty bad way to push 5 bits to a reduced bitvector
-- TODO: use induction or something to make something better
def push5 (orig : bitvec 32) (reduced : bitvec (word_len - 5)) : bitvec 32 :=
do
  let a1 := reduced.append (bit_n orig 0),
  let a2 := a1.append (bit_n orig 1),
  let a3 := a2.append (bit_n orig 2),
  let a4 := a3.append (bit_n orig 3),
  let a5 := a4.append (bit_n orig 4),
  a5

-- example from the spec : 0xc0a8787e <<< 5 = 0x150f0fd8
def v' : bitvec 32 := 0xc0a8787e
def shift : ℕ := 5

#eval (push5 v' (reduce_bitvector (shift_left v' 5) 27)).to_nat
#eval 0x150f0fd8

def rotate5 (input: bitvec 32) := (push5 input (reduce_bitvector (shift_left input 5) 27))
#eval (rotate5 v').to_nat


-- the quarterround function will require push7, push9, push13 and push18

def push7 (orig : bitvec 32) (reduced : bitvec (word_len - 7)) : bitvec 32 :=
do
  let a1 := reduced.append (bit_n orig 0),
  let a2 := a1.append (bit_n orig 1),
  let a3 := a2.append (bit_n orig 2),
  let a4 := a3.append (bit_n orig 3),
  let a5 := a4.append (bit_n orig 4),
  let a6 := a5.append (bit_n orig 5),
  let a7 := a6.append (bit_n orig 6),
  a7

def rotate7 (input: bitvec 32) := (push7 input (reduce_bitvector (shift_left input 7) 25))

def push9 (orig : bitvec 32) (reduced : bitvec (word_len - 9)) : bitvec 32 :=
do
  let a1 := reduced.append (bit_n orig 0),
  let a2 := a1.append (bit_n orig 1),
  let a3 := a2.append (bit_n orig 2),
  let a4 := a3.append (bit_n orig 3),
  let a5 := a4.append (bit_n orig 4),
  let a6 := a5.append (bit_n orig 5),
  let a7 := a6.append (bit_n orig 6),
  let a8 := a7.append (bit_n orig 7),
  let a9 := a8.append (bit_n orig 8),
  a9

def rotate9 (input: bitvec 32) := (push9 input (reduce_bitvector (shift_left input 9) 23))

def push13 (orig : bitvec 32) (reduced : bitvec (word_len - 13)) : bitvec 32 :=
do
  let a1 := reduced.append (bit_n orig 0),
  let a2 := a1.append (bit_n orig 1),
  let a3 := a2.append (bit_n orig 2),
  let a4 := a3.append (bit_n orig 3),
  let a5 := a4.append (bit_n orig 4),
  let a6 := a5.append (bit_n orig 5),
  let a7 := a6.append (bit_n orig 6),
  let a8 := a7.append (bit_n orig 7),
  let a9 := a8.append (bit_n orig 8),
  let a10 := a9.append (bit_n orig 9),
  let a11 := a10.append (bit_n orig 10),
  let a12 := a11.append (bit_n orig 11),
  let a13 := a12.append (bit_n orig 12),
  a13

def rotate13 (input: bitvec 32) := (push13 input (reduce_bitvector (shift_left input 13) 19))

def push18 (orig : bitvec 32) (reduced : bitvec (word_len - 18)) : bitvec 32 :=
do
  let a1 := reduced.append (bit_n orig 0),
  let a2 := a1.append (bit_n orig 1),
  let a3 := a2.append (bit_n orig 2),
  let a4 := a3.append (bit_n orig 3),
  let a5 := a4.append (bit_n orig 4),
  let a6 := a5.append (bit_n orig 5),
  let a7 := a6.append (bit_n orig 6),
  let a8 := a7.append (bit_n orig 7),
  let a9 := a8.append (bit_n orig 8),
  let a10 := a9.append (bit_n orig 9),
  let a11 := a10.append (bit_n orig 10),
  let a12 := a11.append (bit_n orig 11),
  let a13 := a12.append (bit_n orig 12),
  let a14 := a13.append (bit_n orig 13),
  let a15 := a14.append (bit_n orig 14),
  let a16 := a15.append (bit_n orig 15),
  let a17 := a16.append (bit_n orig 16),
  let a18 := a17.append (bit_n orig 17),
  a18

def rotate18 (input: bitvec 32) := (push18 input (reduce_bitvector (shift_left input 18) 14))
