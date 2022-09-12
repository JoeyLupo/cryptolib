/-

  Section 3 : The quarterround function
  http://cr.yp.to/snuffle/spec.pdf

-/
import salsa20.words

-- z1
def z1 (y0 y1 y2 y3 : bitvec word_len) : bitvec word_len := 
  bitvec.xor y1 (rotate7 (nat_as_bitvec (mod_as_nat (sum_as_mod y0 y3))))

-- z2
def z2 (y0 y1 y2 y3 : bitvec word_len) : bitvec 32 := 
  bitvec.xor y2 (rotate9 (nat_as_bitvec (mod_as_nat (sum_as_mod (z1 y0 y1 y2 y3) y0))))

-- z3
def z3 (y0 y1 y2 y3 : bitvec word_len) :  bitvec 32 := 
  bitvec.xor y3 (rotate13 (nat_as_bitvec (mod_as_nat (sum_as_mod (z2 y0 y1 y2 y3) (z1 y0 y1 y2 y3)))))

-- z0
def z0 (y0 y1 y2 y3 : bitvec word_len) : bitvec 32 := 
  bitvec.xor y0 (rotate18 (nat_as_bitvec (mod_as_nat (sum_as_mod (z3 y0 y1 y2 y3) (z2 y0 y1 y2 y3)))))

def quarterround (y0 y1 y2 y3 : bitvec word_len) : list (bitvec 32) :=
  do
    let z1_res := z1 y0 y1 y2 y3,
    let z2_res := z2 y0 y1 y2 y3,
    let z3_res := z3 y0 y1 y2 y3,
    let z0_res := z0 y0 y1 y2 y3,
    [z0_res, z1_res, z2_res, z3_res]

-- Examples from the spec

-- example 1
namespace example1

def y0 : bitvec word_len := 0x00000000
def y1 : bitvec word_len := 0x00000000
def y2 : bitvec word_len := 0x00000000
def y3 : bitvec word_len := 0x00000000

example : (z1 y0 y1 y2 y3).to_nat = 0x00000000 := by refl
example : (z2 y0 y1 y2 y3).to_nat = 0x00000000 := by refl
example : (z3 y0 y1 y2 y3).to_nat = 0x00000000 := by refl
example : (z0 y0 y1 y2 y3).to_nat = 0x00000000 := by refl

end example1

-- example 2
namespace example2

def y0 : bitvec word_len := 0x00000001
def y1 : bitvec word_len := 0x00000000
def y2 : bitvec word_len := 0x00000000
def y3 : bitvec word_len := 0x00000000

-- timeout, why ?
--example : (z1 y0 y1 y2 y3).to_nat = 0x00000080 := by refl
--example : (z2 y0 y1 y2 y3).to_nat = 0x00010200 := by refl
--example : (z3 y0 y1 y2 y3).to_nat = 0x20500000 := by refl
--example : (z0 y0 y1 y2 y3).to_nat = 0x08008145 := by refl

#eval (z1 y0 y1 y2 y3).to_nat
#eval 0x00000080
#eval ((quarterround y0 y1 y2 y3).tail).head.to_nat

#eval (z2 y0 y1 y2 y3).to_nat
#eval 0x00010200
#eval ((quarterround y0 y1 y2 y3).tail.tail).head.to_nat

#eval (z3 y0 y1 y2 y3).to_nat
#eval 0x20500000
#eval ((quarterround y0 y1 y2 y3).tail.tail.tail).head.to_nat

#eval (z0 y0 y1 y2 y3).to_nat
#eval 0x08008145
#eval ((quarterround y0 y1 y2 y3).head).to_nat

end example2

-- example 3
namespace example3

def y0 : bitvec word_len := 0x00000000
def y1 : bitvec word_len := 0x00000001
def y2 : bitvec word_len := 0x00000000
def y3 : bitvec word_len := 0x00000000

#eval (z1 y0 y1 y2 y3).to_nat
#eval 0x00000001
#eval ((quarterround y0 y1 y2 y3).tail).head.to_nat

#eval (z2 y0 y1 y2 y3).to_nat
#eval 0x00000200
#eval ((quarterround y0 y1 y2 y3).tail.tail).head.to_nat

#eval (z3 y0 y1 y2 y3).to_nat
#eval 0x00402000
#eval ((quarterround y0 y1 y2 y3).tail.tail.tail).head.to_nat

#eval (z0 y0 y1 y2 y3).to_nat
#eval 0x88000100
#eval ((quarterround y0 y1 y2 y3).head).to_nat

end example3

-- example 4
namespace example4

def y0 : bitvec word_len := 0x00000000
def y1 : bitvec word_len := 0x00000000
def y2 : bitvec word_len := 0x00000001
def y3 : bitvec word_len := 0x00000000

#eval (z1 y0 y1 y2 y3).to_nat
#eval 0x00000000
#eval ((quarterround y0 y1 y2 y3).tail).head.to_nat

#eval (z2 y0 y1 y2 y3).to_nat
#eval 0x00000001
#eval ((quarterround y0 y1 y2 y3).tail.tail).head.to_nat

#eval (z3 y0 y1 y2 y3).to_nat
#eval 0x00002000
#eval ((quarterround y0 y1 y2 y3).tail.tail.tail).head.to_nat

#eval (z0 y0 y1 y2 y3).to_nat
#eval 0x80040000
#eval ((quarterround y0 y1 y2 y3).head).to_nat

end example4

-- example 5
namespace example5

def y0 : bitvec word_len := 0x00000000
def y1 : bitvec word_len := 0x00000000
def y2 : bitvec word_len := 0x00000000
def y3 : bitvec word_len := 0x00000001

#eval (z1 y0 y1 y2 y3).to_nat
#eval 0x00000080
#eval ((quarterround y0 y1 y2 y3).tail).head.to_nat

#eval (z2 y0 y1 y2 y3).to_nat
#eval 0x00010000
#eval ((quarterround y0 y1 y2 y3).tail.tail).head.to_nat

#eval (z3 y0 y1 y2 y3).to_nat
#eval 0x20100001
#eval ((quarterround y0 y1 y2 y3).tail.tail.tail).head.to_nat

#eval (z0 y0 y1 y2 y3).to_nat
#eval 0x00048044
#eval ((quarterround y0 y1 y2 y3).head).to_nat

end example5

-- example 6
namespace example6

def y0 : bitvec word_len := 0xe7e8c006
def y1 : bitvec word_len := 0xc4f9417d
def y2 : bitvec word_len := 0x6479b4b2
def y3 : bitvec word_len := 0x68c67137

#eval (z1 y0 y1 y2 y3).to_nat
#eval 0x9361dfd5
#eval ((quarterround y0 y1 y2 y3).tail).head.to_nat

#eval (z2 y0 y1 y2 y3).to_nat
#eval 0xf1460244
#eval ((quarterround y0 y1 y2 y3).tail.tail).head.to_nat

#eval (z3 y0 y1 y2 y3).to_nat
#eval 0x948541a3
#eval ((quarterround y0 y1 y2 y3).tail.tail.tail).head.to_nat

#eval (z0 y0 y1 y2 y3).to_nat
#eval 0xe876d72b
#eval ((quarterround y0 y1 y2 y3).head).to_nat

end example6

-- example 7
namespace example7

def y0 : bitvec word_len := 0xd3917c5b
def y1 : bitvec word_len := 0x55f1c407
def y2 : bitvec word_len := 0x52a58a7a
def y3 : bitvec word_len := 0x8f887a3b

#eval (z1 y0 y1 y2 y3).to_nat
#eval 0xd90a8f36
#eval ((quarterround y0 y1 y2 y3).tail).head.to_nat

#eval (z2 y0 y1 y2 y3).to_nat
#eval 0x6ab2a923
#eval ((quarterround y0 y1 y2 y3).tail.tail).head.to_nat

#eval (z3 y0 y1 y2 y3).to_nat
#eval 0x2883524c
#eval ((quarterround y0 y1 y2 y3).tail.tail.tail).head.to_nat

#eval (z0 y0 y1 y2 y3).to_nat
#eval 0x3e2f308c
#eval ((quarterround y0 y1 y2 y3).head).to_nat

end example7
