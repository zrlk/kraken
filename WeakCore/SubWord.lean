import WeakCore.HashMap

/-!
# Sub-word integers — fixed-width types and packed buffers

* `fix sg w` (`U8`…`U64`, `I8`…`I64`): a `w`-bit integer.  At run time, its
  two's-complement pattern below `2^w`; signedness matters only to `div`, `rem`,
  `shr`, comparisons and widening.  Everything wraps: no undefined results.
* `lanes sg w`: one 64-bit word of `64/w` lanes, little-endian.  A packed array
  is a buffer of them, `Buf μ (lanes sg w) n k`: `n` words, `n·64/w` lanes, so
  every buffer rule (width, `ini`, zero, `idx`, `region`) applies unchanged.
* `ldl`/`stl` read and write one lane of an **own** buffer.  `stl` is the one
  sub-word store; in the model it is the owner's word read-modify-write, and
  nobody else can see the word.  A shared buffer is written a word at a time
  (`idx`, `load`, `setLane`, `store`), under the region's usual rules.
-/

namespace SubWord
open CoreLang CoreTerm TermRun TermSmoke HashMap

def u8 : Ty := .fix false .w8
def i8 : Ty := .fix true .w8
def L8 : Ty := .lanes false .w8
def L16 : Ty := .lanes false .w16

/-! ## Bytes in an own buffer -/

/-- Two words, sixteen byte lanes.  Store four, read one back, and load word 1
whole (a group load): lanes 8, 9 and 15 are `0x11`, `0x22`, `300 mod 256`. -/
def bytesD : Decl := dcl "bytes" .int .int
  (lets [("n", .nameI (.lit 2)), ("b", .newBuf (v "n") L8),
         ("x1", .cvt false .w8 (.lit 0x11)), ("x2", .cvt false .w8 (.lit 0x22)),
         ("x3", .cvt false .w8 (.lit 300)),
         ("u0", .stl (v "b") (.lit 0) (v "x1")), ("u1", .stl (v "b") (.lit 9) (v "x2")),
         ("u2", .stl (v "b") (.lit 15) (v "x3")), ("u3", .stl (v "b") (.lit 8) (v "x1")),
         ("y", .ldl (v "b") (.lit 9)), ("yy", .fop .add (v "y") (v "x1")),
         ("w1", .loadAt (v "b") (.lit 1)), ("i1", .toInt (v "w1")),
         ("iy", .toInt (v "yy")), ("r", .add (v "i1") (v "iy"))] (.ret (v "r")))

/-- Sixteen-bit lanes: one word, four lanes. -/
def halvesD : Decl := dcl "halves" .int (.prod .int .int)
  (lets [("n", .nameI (.lit 1)), ("b", .newBuf (v "n") L16),
         ("x", .cvt false .w16 (.lit 0xabcd)), ("u", .stl (v "b") (.lit 3) (v "x")),
         ("y", .ldl (v "b") (.lit 3)), ("w0", .loadAt (v "b") (.lit 0)),
         ("iy", .toInt (v "y")), ("iw", .toInt (v "w0")), ("r", .pair (v "iy") (v "iw"))] (.ret (v "r")))

/-! ## Signed arithmetic -/

/-- `a = -56 : I8`.  Every result is shown through an unsigned `cvt` and `toInt`. -/
def signedD : Decl := dcl "signed" .int
  (.prod .int (.prod .int (.prod .int (.prod .int (.prod .int .int)))))
  (lets [("sa", .cvt true .w8 (.lit 200)), ("b", .cvt true .w8 (.lit 100)),
         ("k7", .cvt true .w8 (.lit 7)), ("k5", .cvt true .w8 (.lit 5)), ("k2", .cvt true .w8 (.lit 2)),
         ("z", .cvt true .w8 (.lit 0)),
         ("s32", .cvt true .w32 (v "sa")), ("u32", .cvt false .w32 (v "s32")), ("o1", .toInt (v "u32")),
         ("q", .fop .div (v "sa") (v "k7")), ("uq", .cvt false .w8 (v "q")), ("o2", .toInt (v "uq")),
         ("m", .fop .rem (v "sa") (v "k5")), ("um", .cvt false .w8 (v "m")), ("o3", .toInt (v "um")),
         ("o4", .fcmp .lt (v "sa") (v "z")),
         ("h", .fop .shr (v "sa") (v "k2")), ("uh", .cvt false .w8 (v "h")), ("o5", .toInt (v "uh")),
         ("c", .fop .add (v "sa") (v "b")), ("uc", .cvt false .w8 (v "c")), ("o6", .toInt (v "uc")),
         ("p5", .pair (v "o5") (v "o6")), ("p4", .pair (v "o4") (v "p5")), ("p3", .pair (v "o3") (v "p4")),
         ("p2", .pair (v "o2") (v "p3")), ("p1", .pair (v "o1") (v "p2"))] (.ret (v "p1")))

/-- `|a|` for `a : I8`, as an `Int`: the signed-to-index branch, derived from
`fcmp lt` and `ifeq` (no new expression form). -/
def absD : Decl := dcl "abs8" i8 .int
  (lets [("z", .cvt true .w8 (.lit 0)), ("n", .fcmp .lt (v "a") (v "z"))]
    (.ifeq (v "n") (.lit 1)
      (lets [("m", .fop1 .neg (v "a")), ("u", .cvt false .w8 (v "m")), ("r", .toInt (v "u"))] (.ret (v "r")))
      (lets [("u", .cvt false .w8 (v "a")), ("r", .toInt (v "u"))] (.ret (v "r")))))

/-- Word/lane addressing, the lane mod 8: `(1, 9)` is lane 1 of word 1, flat lane 9. -/
def wordLaneD : Decl := dcl "wordLane" .int (.prod .int (.prod .int .int))
  (lets [("n", .nameI (.lit 2)), ("b", .newBuf (v "n") L8), ("x", .cvt false .w8 (.lit 0x5a)),
         ("u", .stlw (v "b") (.lit 1) (.lit 9) (v "x")), ("y", .ldl (v "b") (.lit 9)),
         ("z", .ldlw (v "b") (.lit 1) (.lit 1)), ("w", .loadAt (v "b") (.lit 1)),
         ("q", .lane (v "w") (.lit 17)), ("iy", .toInt (v "y")), ("iz", .toInt (v "z")), ("iq", .toInt (v "q")),
         ("p2", .pair (v "iz") (v "iq")), ("p", .pair (v "iy") (v "p2"))] (.ret (v "p")))

def swLib : Prog := [bytesD, halvesD, signedD, absD, wordLaneD]

#guard accepts (checkProg swLib)

/-! ## On the machine -/

def run1 (f : String) (t : Ty) (x : Nat) : Option (List WeakMem.Val) :=
  (runSetup swLib f [] t [cst (.num x)]).map (·.res.map (·.val))

#guard run1 "bytes" .int 0 == some [.num (0x2c00000000002211 + 0x33)]
#guard run1 "halves" .int 0 == some [.num 0xabcd, .num 0xabcd000000000000]
#guard run1 "signed" .int 0 == some [.num (2 ^ 32 - 56), .num 248, .num 255, .num 1, .num 242, .num 44]
#guard run1 "abs8" i8 200 == some [.num 56]
#guard run1 "abs8" i8 56 == some [.num 56]
#guard run1 "abs8" i8 128 == some [.num 128]
#guard run1 "wordLane" .int 0 == some [.num 0x5a, .num 0x5a, .num 0x5a]

/-! ## Hazards -/

-- Mixed types: no implicit conversion.
#guard rejects (checkDecl [] (dcl "mix" .int .int
    (lets [("a1", .cvt false .w8 (.lit 1)), ("b", .cvt true .w8 (.lit 1)), ("c", .fop .add (v "a1") (v "b"))]
      (.ret .unit)))) "different fixed-width types"
-- A signed value is not an `Int` until it is made unsigned (or tested).
#guard rejects (checkDecl [] (dcl "si" .int .int
    (lets [("a1", .cvt true .w8 (.lit 1)), ("c", .toInt (v "a1"))] (.ret (v "c"))))) "toInt needs an unsigned fix"
-- Arithmetic is on fixed-width values, not on `Int`.
#guard rejects (checkDecl [] (dcl "fi" .int .int
    (lets [("c", .fop .add (v "a") (v "a"))] (.ret .unit)))) "fop needs fixed-width integers"

/-- Two words of byte lanes, then `extra`. -/
def withBytes (extra : List (String × Op)) : Decl := dcl "wb" .int .unit
  (lets ([("n", .nameI (.lit 2)), ("b", .newBuf (v "n") L8), ("x", .cvt false .w8 (.lit 1))] ++ extra)
    (.ret .unit))

#guard accepts (checkDecl [] (withBytes [("u", .stl (v "b") (.lit 15) (v "x"))]))
-- Lane 16 of a two-word buffer: out of bounds, statically.
#guard rejects (checkDecl [] (withBytes [("u", .stl (v "b") (.lit 16) (v "x"))]))
  "stl: the lane is not provably below the capacity"
#guard rejects (checkDecl [] (withBytes [("u", .ldl (v "b") (.lit 16))]))
  "ldl: the lane is not provably below the capacity"
-- A 16-bit value into a byte lane.
#guard rejects (checkDecl [] (withBytes [("y", .cvt false .w16 (.lit 1)), ("u", .stl (v "b") (.lit 0) (v "y"))]))
  "stl: the value is not the lane's type"
-- Within a word the lane number is taken mod `64/w` (a shift count): any `Int` will do.
#guard accepts (checkDecl [] (withBytes [("w", .loadAt (v "b") (.lit 0)), ("y", .lane (v "w") (.lit 9))]))
#guard rejects (checkDecl [] (withBytes [("w", .loadAt (v "b") (.lit 0)), ("y", .lane (v "w") (v "x"))]))
  "lane: the lane number must be an Int"
-- The word, though, is bounded statically.
#guard accepts (checkDecl [] (withBytes [("u", .stlw (v "b") (.lit 1) (.lit 7) (v "x"))]))
#guard rejects (checkDecl [] (withBytes [("u", .stlw (v "b") (.lit 2) (.lit 0) (v "x"))]))
  "stlw: the word is not provably below the capacity"
-- Lanes need a buffer of lanes.
#guard rejects (checkDecl [] (dcl "nl" .int .unit
    (lets [("n", .nameI (.lit 2)), ("b", .newBuf (v "n") .int), ("x", .cvt false .w8 (.lit 1)),
           ("u", .stl (v "b") (.lit 0) (v "x"))] (.ret .unit)))) "stl needs a buffer of lanes"

/-- The byte buffer opened as a region (fresh token `t0` in hand), then `extra`. -/
def inRegion (extra : List (String × Op)) : Decl := dcl "ir" .int .unit
  (lets [("n", .nameI (.lit 2)), ("b0", .newBuf (v "n") L8), ("x", .cvt false .w8 (.lit 1))]
    (.region (v "b0") "r" "b" "t0" (lets extra (.ret .unit))))

-- No sub-word store into a region, not even with its fresh token in hand …
#guard rejects (checkDecl [] (inRegion [("u", .stl (v "b") (.lit 3) (v "x"))]))
  "stl works on own buffers only"
-- … but a visible word read-modify-write under the token is fine.
#guard accepts (checkDecl [] (inRegion [("l", .idx (v "b") (.lit 0)), ("w", .load false (v "l")),
    ("w2", .setLane (v "w") (.lit 3) (v "x")), ("u", .store false (v "l") (v "w2") none)]))

/-! ## A frozen byte table: read with plain loads, no `cas` -/

/-- Build bytes `[1, 2, …]` in lanes 0..2, freeze, and read lane 2 back through
`idx`, `load` and `lane` under `Cap frz`. -/
def frozenBytesD : Decl := dcl "frozenBytes" .int .int
  (lets [("n", .nameI (.lit 1)), ("b0", .newBuf (v "n") L8),
         ("x1", .cvt false .w8 (.lit 1)), ("x2", .cvt false .w8 (.lit 2)), ("x3", .cvt false .w8 (.lit 3)),
         ("u1", .stl (v "b0") (.lit 0) (v "x1")), ("u2", .stl (v "b0") (.lit 1) (v "x2")),
         ("u3", .stl (v "b0") (.lit 2) (v "x3"))]
    (.region (v "b0") "r" "b" "t0"
      (lets [("c", .freeze (v "t0")), ("l", .idx (v "b") (.lit 0)),
             ("w", .load false (v "l")), ("y", .lane (v "w") (.lit 2)), ("r", .toInt (v "y"))]
        (.ret (v "r")))))

#guard accepts (checkDecl [] frozenBytesD)
#guard (runSetup [frozenBytesD] "frozenBytes" [] .int [cst (.num 0)]).map (·.res.map (·.val)) ==
  some [.num 3]
-- And after `freeze`, not even the word store goes through.
#guard rejects (checkDecl [] { frozenBytesD with
    body := lets [("n", .nameI (.lit 1)), ("b0", .newBuf (v "n") L8), ("x1", .cvt false .w8 (.lit 1))]
      (.region (v "b0") "r" "b" "t0"
        (lets [("c", .freeze (v "t0")), ("l", .idx (v "b") (.lit 0)),
               ("w", .load false (v "l")), ("w2", .setLane (v "w") (.lit 0) (v "x1")),
               ("u", .store false (v "l") (v "w2") none), ("r", .toInt (v "w"))] (.ret (v "r")))) })
  "store into a region without its token"

end SubWord
