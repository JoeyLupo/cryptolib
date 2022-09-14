/-
  Section 5 : The columnrow function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.quarterround

def columnround1 (x0 x4 x8 x12 : bitvec word_len) : list (bitvec word_len) := 
  quarterround x0 x4 x8 x12

def columnround2 (x5 x9 x13 x1 : bitvec word_len) : list (bitvec word_len) := 
  quarterround x5 x9 x13 x1

def columnround3 (x10 x14 x2 x6 : bitvec word_len) : list (bitvec word_len) := 
  quarterround x10 x14 x2 x6

def columnround4 (x15 x3 x7 x11 : bitvec word_len) : list (bitvec word_len) := 
  quarterround x15 x3 x7 x11

def columnround
  (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : 
  bitvec word_len) : list (bitvec word_len) :=
  do
    let list1 := columnround1 x0 x4 x8 x12,
    let list2 := columnround2 x5 x9 x13 x1,
    let list3 := columnround3 x10 x14 x2 x6,
    let list4 := columnround4 x15 x3 x7 x11,

    let y0 := list1.head,
    let y4 := (list1.nth 1).iget,
    let y8 := (list1.nth 2).iget,
    let y12 := (list1.nth 3).iget,

    let y5 := list2.head,
    let y9 := (list2.nth 1).iget,
    let y13 := (list2.nth 2).iget,
    let y1 := (list2.nth 3).iget,

    let y10 := list3.head,
    let y14 := (list3.nth 1).iget,
    let y2 := (list3.nth 2).iget,
    let y6 := (list3.nth 3).iget,

    let y15 := list4.head,
    let y3 := (list4.nth 1).iget,
    let y7 := (list4.nth 2).iget,
    let y11 := (list4.nth 3).iget,

    [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15]

-- example 1
namespace example5_1

def x0 : bitvec word_len := 0x00000001
def x1 : bitvec word_len := 0x00000000
def x2 : bitvec word_len := 0x00000000
def x3 : bitvec word_len := 0x00000000
def x4 : bitvec word_len := 0x00000001
def x5 : bitvec word_len := 0x00000000
def x6 : bitvec word_len := 0x00000000
def x7 : bitvec word_len := 0x00000000
def x8 : bitvec word_len := 0x00000001
def x9 : bitvec word_len := 0x00000000
def x10 : bitvec word_len := 0x00000000
def x11 : bitvec word_len := 0x00000000
def x12 : bitvec word_len := 0x00000001
def x13 : bitvec word_len := 0x00000000
def x14 : bitvec word_len := 0x00000000
def x15 : bitvec word_len := 0x00000000

-- y0
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 0).iget).to_nat
#eval 0x10090288

-- y1
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 1).iget).to_nat
#eval 0x00000000

-- y2
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 2).iget).to_nat
#eval 0x00000000

-- y3
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 3).iget).to_nat
#eval 0x00000000

-- y4
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 4).iget).to_nat
#eval 0x00000101

-- y5
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 5).iget).to_nat
#eval 0x00000000

-- y6
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 6).iget).to_nat
#eval 0x00000000

-- y7
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 7).iget).to_nat
#eval 0x00000000

-- y8
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 8).iget).to_nat
#eval 0x00020401

-- y9
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 9).iget).to_nat
#eval 0x00000000

-- y10
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 10).iget).to_nat
#eval 0x00000000

-- y11
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 11).iget).to_nat
#eval 0x00000000

-- y12
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 12).iget).to_nat
#eval 0x40a04001

-- y13
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 13).iget).to_nat
#eval 0x00000000

-- y14
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 14).iget).to_nat
#eval 0x00000000

-- y15
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 15).iget).to_nat
#eval 0x00000000

end example5_1

-- example 2
namespace example5_2

def x0 : bitvec word_len := 0x08521bd6
def x1 : bitvec word_len := 0x1fe88837
def x2 : bitvec word_len := 0xbb2aa576
def x3 : bitvec word_len := 0x3aa26365
def x4 : bitvec word_len := 0xc54c6a5b
def x5 : bitvec word_len := 0x2fc74c2f
def x6 : bitvec word_len := 0x6dd39cc3
def x7 : bitvec word_len := 0xda0a64f6
def x8 : bitvec word_len := 0x90a2f23d
def x9 : bitvec word_len := 0x067f95a6
def x10 : bitvec word_len := 0x06b35f61
def x11 : bitvec word_len := 0x41e4732e
def x12 : bitvec word_len := 0xe859c100
def x13 : bitvec word_len := 0xea4d84b7
def x14 : bitvec word_len := 0x0f619bff
def x15 : bitvec word_len := 0xbc6e965a

-- y0
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 0).iget).to_nat
#eval 0x8c9d190a

-- y1
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 1).iget).to_nat
#eval 0xce8e4c90

-- y2
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 2).iget).to_nat
#eval 0x1ef8e9d3

-- y3
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 3).iget).to_nat
#eval 0x1326a71a

-- y4
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 4).iget).to_nat
#eval 0x90a20123

-- y5
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 5).iget).to_nat
#eval 0xead3c4f3

-- y6
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 6).iget).to_nat
#eval 0x63a091a0

-- y7
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 7).iget).to_nat
#eval 0xf0708d69

-- y8
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 8).iget).to_nat
#eval 0x789b010c

-- y9
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 9).iget).to_nat
#eval 0xd195a681

-- y10
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 10).iget).to_nat
#eval 0xeb7d5504

-- y11
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 11).iget).to_nat
#eval 0xa774135c

-- y12
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 12).iget).to_nat
#eval 0x481c2027

-- y13
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 13).iget).to_nat
#eval 0x53a8e4b5

-- y14
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 14).iget).to_nat
#eval 0x4c1f89c5

-- y15
#eval (((columnround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 15).iget).to_nat
#eval 0x3f78c9c8

end example5_2

-- TODO: equivalent formula
-- TODO: matrix form
