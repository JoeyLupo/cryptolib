/-
  Section 4 : The rowround function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.quarterround

def rowround1 (y0 y1 y2 y3 : bitvec word_len) : list (bitvec word_len) := 
  quarterround y0 y1 y2 y3

def rowround2 (y5 y6 y7 y4 : bitvec word_len) : list (bitvec word_len) := 
  quarterround y5 y6 y7 y4

def rowround3 (y10 y11 y8 y9 : bitvec word_len) : list (bitvec word_len) := 
  quarterround y10 y11 y8 y9

def rowround4 (y15 y12 y13 y14 : bitvec word_len) : list (bitvec word_len) := 
  quarterround y15 y12 y13 y14

def rowround
  (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : 
  bitvec word_len) : list (bitvec word_len) :=
  do
    let list1 := rowround1 y0 y1 y2 y3,
    let list2 := rowround2 y5 y6 y7 y4,
    let list3 := rowround3 y10 y11 y8 y9,
    let list4 := rowround4 y15 y12 y13 y14,

    let z5 := list2.head,
    let z6 := list2.tail.head,
    let z7 := list2.tail.tail.head,
    let z4 := list2.tail.tail.tail.head,

    let list2_sorted := [z4, z5, z6, z7], 

    let z10 := list3.head,
    let z11 := list3.tail.head,
    let z8 := list3.tail.tail.head,
    let z9 := list3.tail.tail.tail.head,

    let list3_sorted := [z8, z9, z10, z11],

    let z15 := list4.head,
    let z12 := list4.tail.head,
    let z13 := list4.tail.tail.head,
    let z14 := list4.tail.tail.tail.head,

    let list4_sorted := [z12, z13, z14, z15],
    
    ((list1.append list2_sorted).append list3_sorted).append list4_sorted


-- example 1
namespace example4_1

def y0 : bitvec word_len := 0x00000001
def y1 : bitvec word_len := 0x00000000
def y2 : bitvec word_len := 0x00000000
def y3 : bitvec word_len := 0x00000000
def y4 : bitvec word_len := 0x00000001
def y5 : bitvec word_len := 0x00000000
def y6 : bitvec word_len := 0x00000000
def y7 : bitvec word_len := 0x00000000
def y8 : bitvec word_len := 0x00000001
def y9 : bitvec word_len := 0x00000000
def y10 : bitvec word_len := 0x00000000
def y11 : bitvec word_len := 0x00000000
def y12 : bitvec word_len := 0x00000001
def y13 : bitvec word_len := 0x00000000
def y14 : bitvec word_len := 0x00000000
def y15 : bitvec word_len := 0x00000000

-- z0
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).head).to_nat
#eval 0x08008145

-- z1
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.head).to_nat
#eval 0x00000080

-- z2
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.head).to_nat
#eval 0x00010200

-- z3
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.head).to_nat
#eval 0x20500000

-- z4
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.head).to_nat
#eval 0x20100001

-- z5
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.head).to_nat
#eval 0x00048044

-- z6
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x00000080

-- z7
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x00010000

-- z8
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x00000001

-- z9
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x00002000

-- z10
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x80040000

-- z11
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x00000000

-- z12
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x00000001

-- z13
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x00000200

-- z14
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x00402000

-- z15
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x88000100

end example4_1

-- example 2
namespace example4_2

def y0 : bitvec word_len := 0x08521bd6
def y1 : bitvec word_len := 0x1fe88837
def y2 : bitvec word_len := 0xbb2aa576
def y3 : bitvec word_len := 0x3aa26365
def y4 : bitvec word_len := 0xc54c6a5b
def y5 : bitvec word_len := 0x2fc74c2f
def y6 : bitvec word_len := 0x6dd39cc3
def y7 : bitvec word_len := 0xda0a64f6
def y8 : bitvec word_len := 0x90a2f23d
def y9 : bitvec word_len := 0x067f95a6
def y10 : bitvec word_len := 0x06b35f61
def y11 : bitvec word_len := 0x41e4732e
def y12 : bitvec word_len := 0xe859c100
def y13 : bitvec word_len := 0xea4d84b7
def y14 : bitvec word_len := 0x0f619bff
def y15 : bitvec word_len := 0xbc6e965a

-- z0
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).head).to_nat
#eval 0xa890d39d

-- z1
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.head).to_nat
#eval 0x65d71596

-- z2
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.head).to_nat
#eval 0xe9487daa

-- z3
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.head).to_nat
#eval 0xc8ca6a86

-- z4
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.head).to_nat
#eval 0x949d2192

-- z5
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.head).to_nat
#eval 0x764b7754

-- z6
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0xe408d9b9

-- z7
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x7a41b4d1

-- z8
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x3402e183

-- z9
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x3c3af432

-- z10
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x50669f96

-- z11
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0xd89ef0a8

-- z12
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x0040ede5

-- z13
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0xb545fbce

-- z14
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0xd257ed4f

-- z15
#eval ((rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.head).to_nat
#eval 0x1818882d

end example4_2
