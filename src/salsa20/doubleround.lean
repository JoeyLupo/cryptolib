/-
  Section 6 : The doubleround function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.rowround
import salsa20.columnround

def doubleround
  (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : 
    bitvec word_len) : list (bitvec word_len) :=

  do
    let cr := columnround 
      x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15,
    let y0 := (cr.nth 0).iget,
    let y1 := (cr.nth 1).iget,
    let y2 := (cr.nth 2).iget,
    let y3 := (cr.nth 3).iget,
    let y4 := (cr.nth 4).iget,
    let y5 := (cr.nth 5).iget,
    let y6 := (cr.nth 6).iget,
    let y7 := (cr.nth 7).iget,
    let y8 := (cr.nth 8).iget,
    let y9 := (cr.nth 9).iget,
    let y10 := (cr.nth 10).iget,
    let y11 := (cr.nth 11).iget,
    let y12 := (cr.nth 12).iget,
    let y13 := (cr.nth 13).iget,
    let y14 := (cr.nth 14).iget,
    let y15 := (cr.nth 15).iget,

    rowround y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15

-- example 1
namespace example6_1

def x0 : bitvec word_len := 0x00000001
def x1 : bitvec word_len := 0x00000000
def x2 : bitvec word_len := 0x00000000
def x3 : bitvec word_len := 0x00000000
def x4 : bitvec word_len := 0x00000000
def x5 : bitvec word_len := 0x00000000
def x6 : bitvec word_len := 0x00000000
def x7 : bitvec word_len := 0x00000000
def x8 : bitvec word_len := 0x00000000
def x9 : bitvec word_len := 0x00000000
def x10 : bitvec word_len := 0x00000000
def x11 : bitvec word_len := 0x00000000
def x12 : bitvec word_len := 0x00000000
def x13 : bitvec word_len := 0x00000000
def x14 : bitvec word_len := 0x00000000
def x15 : bitvec word_len := 0x00000000

-- double 0
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 0).iget).to_nat
#eval 0x8186a22d

-- double 1
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 1).iget).to_nat
#eval 0x0040a284

--  double 2
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 2).iget).to_nat
#eval 0x82479210

-- double 3
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 3).iget).to_nat
#eval 0x06929051

-- double 4
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 4).iget).to_nat
#eval 0x08000090

-- double 5
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 5).iget).to_nat
#eval 0x02402200

-- double 6
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 6).iget).to_nat
#eval 0x00004000

-- double 7
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 7).iget).to_nat
#eval 0x00800000

-- double 8
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 8).iget).to_nat
#eval 0x00010200

-- double 9
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 9).iget).to_nat
#eval 0x20400000

-- double 10
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 10).iget).to_nat
#eval 0x08008104

-- double 11
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 11).iget).to_nat
#eval 0x00000000

-- double 12
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 12).iget).to_nat
#eval 0x20500000

-- double 13
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 13).iget).to_nat
#eval 0xa0000040

-- double 14
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 14).iget).to_nat
#eval 0x0008180a

-- double 15
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 15).iget).to_nat
#eval 0x612a8020

end example6_1

-- example 2
namespace example6_2

def x0 : bitvec word_len := 0xde501066
def x1 : bitvec word_len := 0x6f9eb8f7
def x2 : bitvec word_len := 0xe4fbbd9b
def x3 : bitvec word_len := 0x454e3f57
def x4 : bitvec word_len := 0xb75540d3
def x5 : bitvec word_len := 0x43e93a4c
def x6 : bitvec word_len := 0x3a6f2aa0
def x7 : bitvec word_len := 0x726d6b36
def x8 : bitvec word_len := 0x9243f484
def x9 : bitvec word_len := 0x9145d1e8
def x10 : bitvec word_len := 0x4fa9d247
def x11 : bitvec word_len := 0xdc8dee11
def x12 : bitvec word_len := 0x054bf545
def x13 : bitvec word_len := 0x254dd653
def x14 : bitvec word_len := 0xd9421b6d
def x15 : bitvec word_len := 0x67b276c1

-- double 0
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 0).iget).to_nat
#eval 0xccaaf672

-- double 1
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 1).iget).to_nat
#eval 0x23d960f7

-- double 2
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 2).iget).to_nat
#eval 0x9153e63a

-- double 3
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 3).iget).to_nat
#eval 0xcd9a60d0

-- double 4
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 4).iget).to_nat
#eval 0x50440492

-- double 5
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 5).iget).to_nat
#eval 0xf07cad19

-- double 6
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 6).iget).to_nat
#eval 0xae344aa0

-- double 7
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 7).iget).to_nat
#eval 0xdf4cfdfc

-- double 8
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 8).iget).to_nat
#eval 0xca531c29

--  double 9
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 9).iget).to_nat
#eval 0x8e7943db

-- double 10
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 10).iget).to_nat
#eval 0xac1680cd

-- double 11
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 11).iget).to_nat
#eval 0xd503ca00

-- double 12
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 12).iget).to_nat
#eval 0xa74b2ad6

-- double 13
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 13).iget).to_nat
#eval 0xbc331c5c

-- double 14
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 14).iget).to_nat
#eval 0x1dda24c7

-- double 15
#eval (((doubleround x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).nth 15).iget).to_nat
#eval 0xee928277

end example6_2
