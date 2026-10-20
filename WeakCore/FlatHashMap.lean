import WeakCore.HashMapOwn

/-!
# FlatHashMap — a SwissTable, own and by value

`absl::flat_hash_map` in the term language.  One generator, two targets:

* **portable** (`x = false`): 8-slot groups, one control word per group, matched
  with SWAR bit tricks (`bits`/`bit1` only);
* **x64** (`x = true`): 16-slot groups, two control words per group, matched
  with `vmatch` (`pcmpeqb`+`pmovmskb`) and `msb16` (`pmovmskb`).

Layout.  The table is two own buffers: control words (`LanesU8`, eight byte
lanes each: a packed byte array, read a group at a time with `loadAt` and
written a byte at a time with `stlw`) and slots
(`K × V`, inline, zero-initialised).  Control byte: `0x00` empty (so a fresh
zero-filled buffer is all empty), `0x01` deleted, `0x80 | h2` full.  The table
type packs two independent sizes, `m` (groups − 1) and `c` (slots − 1):

  `Tbl = ∃m. (Int(m) × Buf own LanesU8 CW CW) × ∃c. (Int(c) × Buf own (K×V) (c+1) (c+1))`

with `CW = m+1` (portable) or `2(m+1)` (x64).  `c + 1 = W(m+1)` is a runtime
invariant only: safety never depends on it, nor on the control bytes.  Every
slot index is `band sr cv` (`sr & c`, which the checker knows is `≤ c`); every
group index is `band pos mv`.  At runtime each `band` is one AND (the identity
on in-range values).

Hash and equality are `code` values (`callc`), as in HashMap.lean.  Keys are
`K : copy, zero`; values `V : zero, noWord` (affine is fine: `insert` hands back the
displaced value, `take` moves it out, `lookup` asks `V : copy`).  The map is
threaded by value (`MapT → MapT × result`), like HashMapOwn.

Probing is over aligned groups, triangular (`pos += 1, 2, 3, …` groups), so it
visits every group of a power-of-two table.  `growth_left` counts the empty
slots that may still be filled; `take` turns a slot back to empty (and gives
growth back) iff its group still has an empty slot — with aligned groups no
probe sequence can have passed such a group — else to deleted.  Growth doubles
the group count and reinserts every full slot.
-/

namespace FlatHashMap
open CoreLang CoreTerm TermRun TermSmoke HashMap

/-! ## Types -/

def κKz : Kind := { copy := true, zero := true }
def κVz : Kind := { zero := true, noWord := true }   -- `noWord`: slots are written by plain exchange
def κVzc : Kind := { zero := true, copy := true, noWord := true }

/-- Slots per group, and its log. -/
def W (x : Bool) : Nat := if x then 16 else 8
def lgW (x : Bool) : Nat := if x then 4 else 3

/-- A slot: key and value inline. -/
def ST : Ty := .prod K V
/-- Control words for `s` groups. -/
def ctrlS (x : Bool) (s : Idx) : Idx := if x then .add s s else s
def CB (x : Bool) (mI : Idx) : Ty :=
  buf .own (.lanes false .w8) (ctrlS x (.add mI (.lit 1))) (ctrlS x (.add mI (.lit 1)))
def SB (cI : Idx) : Ty := buf .own ST (.add cI (.lit 1)) (.add cI (.lit 1))
def tblBody (x : Bool) (mI cI : Idx) : Ty :=
  .prod (.prod (.intS mI) (.intS cI)) (.prod (CB x mI) (SB cI))
/-- The slots at their own size: `∃c. Int(c) × Buf own (K×V) (c+1) (c+1)`. -/
def Slots : Ty := .iex (.prod (.intS (.var 0)) (SB (.var 0)))
/-- `pack` takes one witness and a closed target, so the two sizes nest: the
slots are packed at `c` first (a closed type), then the table at `m`. -/
def Tbl (x : Bool) : Ty := .iex (.prod (.prod (.intS (.var 0)) (CB x (.var 0))) Slots)
/-- The table, `(growth_left, size)`, and the functions. -/
def MapT (x : Bool) : Ty := .prod (Tbl x) (.prod (.prod .int .int) Fns)
def EqT : Ty := .code (.prod K K) HashMap.bool
/-- A probe's answer: `inl sr` (the raw slot index holding the key) or `inr ()`. -/
def SR : Ty := .sum .int .unit

/-! ## Word-level building blocks -/

def L8 : Nat := 0x0101010101010101
def H8 : Nat := 0x8080808080808080
def Lo7 : Nat := 0x7F7F7F7F7F7F7F7F
def Cmix : Nat := 0x9E3779B97F4A7C15

def bo (o : BitOp) (a b : At) : Op := .bits o a b

/-- Nested `split`s: `a` into `x₁, x₂, …, xₙ` (right-nested pairs). -/
def splits (a : String) : List String → Expr → Expr
  | [], e => e
  | [_], e => e
  | [x, y], e => .split (v a) x y e
  | x :: y :: z :: r, e => .split (v a) x (a ++ "'") (splits (a ++ "'") (y :: z :: r) e)

/-- Load group `g` of control buffer `cb` under prefix `p`. -/
def load (x : Bool) (cb g p : String) : List (String × Op) :=
  if x then
    [(p ++ "g2", .add (v g) (v g)), (p ++ "loL", .loadAt (v cb) (v (p ++ "g2"))),
     (p ++ "g3", .add (v (p ++ "g2")) (.lit 1)), (p ++ "hiL", .loadAt (v cb) (v (p ++ "g3"))),
     (p ++ "lo", .toInt (v (p ++ "loL"))), (p ++ "hi", .toInt (v (p ++ "hiL")))]
  else [(p ++ "wL", .loadAt (v cb) (v g)), (p ++ "w", .toInt (v (p ++ "wL")))]

/-- Exact per-byte zero test: `0x80` in each byte of `y` that is `0`. -/
def zb (y : At) (out : String) : List (String × Op) :=
  [(out ++ "a", bo .and y (.lit Lo7)), (out ++ "b", bo .wadd (v (out ++ "a")) (.lit Lo7)),
   (out ++ "c", bo .or (v (out ++ "b")) y), (out ++ "d", bo .or (v (out ++ "c")) (.lit Lo7)),
   (out, .bit1 .not (v (out ++ "d")))]

/-- Lanes of the group whose control byte is `h2`: `p ++ "mk"`. -/
def matchOps (x : Bool) (p h2 : String) : List (String × Op) :=
  if x then [(p ++ "mk", .vmatch (v (p ++ "lo")) (v (p ++ "hi")) (v h2))]
  else [(p ++ "pt", bo .wmul (v h2) (.lit L8)), (p ++ "x", bo .xor (v (p ++ "w")) (v (p ++ "pt")))] ++
       zb (v (p ++ "x")) (p ++ "mk")
/-- Empty lanes: `p ++ "em"`. -/
def emptyOps (x : Bool) (p : String) : List (String × Op) :=
  if x then [(p ++ "em", .vmatch (v (p ++ "lo")) (v (p ++ "hi")) (.lit 0))]
  else zb (v (p ++ "w")) (p ++ "em")
/-- Empty or deleted lanes (top bit clear): `p ++ "fr"`. -/
def freeOps (x : Bool) (p : String) : List (String × Op) :=
  if x then [(p ++ "ms", bo .msb16 (v (p ++ "lo")) (v (p ++ "hi"))),
             (p ++ "fr", bo .xor (v (p ++ "ms")) (.lit 0xFFFF))]
  else [(p ++ "nw", .bit1 .not (v (p ++ "w"))), (p ++ "fr", bo .and (v (p ++ "nw")) (.lit H8))]
/-- Full lanes (top bit set): `p ++ "fu"`. -/
def fullOps (x : Bool) (p : String) : List (String × Op) :=
  if x then [(p ++ "fu", bo .msb16 (v (p ++ "lo")) (v (p ++ "hi")))]
  else [(p ++ "fu", bo .and (v (p ++ "w")) (.lit H8))]
/-- The lowest lane set in mask `m`. -/
def lane (x : Bool) (m out : String) : List (String × Op) :=
  if x then [(out, .bit1 .ctz (v m))]
  else [(out ++ "z", .bit1 .ctz (v m)), (out, bo .shr (v (out ++ "z")) (.lit 3))]
/-- `m & (m − 1)`: the mask without its lowest lane. -/
def clearLow (m out : String) : List (String × Op) :=
  [(out ++ "1", bo .wsub (v m) (.lit 1)), (out, bo .and (v m) (v (out ++ "1")))]

/-- Hash `k`, mix (`mulhi ⊕ wmul` by the golden ratio), split into `h2`
(control byte, top bit set) and `pos` (probe start). -/
def hashOps : List (String × Op) :=
  [("hv", .callc (v "hash") (v "k")), ("hA", bo .mulhi (v "hv") (.lit Cmix)),
   ("hB", bo .wmul (v "hv") (.lit Cmix)), ("hm", bo .xor (v "hA") (v "hB")),
   ("h7", bo .and (v "hm") (.lit 0x7F)), ("h2", bo .or (v "h7") (.lit 0x80)),
   ("pos", bo .shr (v "hm") (.lit 7))]

/-! ## Probing -/

/-- `find` [m, c]: walk the groups from `pos`; `inl sr` if slot `sr` holds `k`,
`inr ()` once a group with an empty slot has no match. -/
def findD (x : Bool) : Decl where
  name := "find"; tparams := [κKz, κVz]; idx := ["m", "c"]; arg := "a"
  argTy := .prod (CB x (.var 1)) (.prod (SB (.var 0)) (.prod (.intS (.var 1)) (.prod (.intS (.var 0))
    (.prod K (.prod EqT (.prod .int (.prod .int .int)))))))
  retTy := .prod (CB x (.var 1)) (.prod (SB (.var 0)) SR)
  body := splits "a" ["cb", "sb", "mv", "cv", "k", "eq", "h2", "pos", "st"]
    (lets ([("g", .band (v "pos") (v "mv"))] ++ load x "cb" "g" "G" ++ matchOps x "G" "h2" ++
           emptyOps x "G" ++ [("base", bo .shl (v "g") (.lit (lgW x)))] ++
           tuple "q" [v "sb", v "cv", v "k", v "eq", v "base", v "Gmk"] ++
           [("r", .call "cand" ["c"] (v "q0") [K, V])])
      (.split (v "r") "sb1" "res"
        (.case (v "res")
          "sr" (lets ([("fo", .inl .unit (v "sr"))] ++ tuple "o" [v "cb", v "sb1", v "fo"]) (.ret (v "o0")))
          "u" (.ifeq (v "Gem") (.lit 0)
                (lets ([("st1", bo .wadd (v "st") (.lit 1)), ("pos1", bo .wadd (v "pos") (v "st1"))] ++
                       tuple "n" [v "cb", v "sb1", v "mv", v "cv", v "k", v "eq", v "h2", v "pos1", v "st1"])
                  (.tail "find" ["m", "c"] (v "n0") [K, V]))
                (lets ([("ab", .inr .int .unit)] ++ tuple "o" [v "cb", v "sb1", v "ab"]) (.ret (v "o0")))))))

/-- `cand` [c]: try the candidate lanes `mk` of the group at slot `base`. -/
def candD (x : Bool) : Decl where
  name := "cand"; tparams := [κKz, κVz]; idx := ["c"]; arg := "a"
  argTy := .prod (SB (.var 0)) (.prod (.intS (.var 0)) (.prod K (.prod EqT (.prod .int .int))))
  retTy := .prod (SB (.var 0)) SR
  body := splits "a" ["sb", "cv", "k", "eq", "base", "mk"]
    (.ifeq (v "mk") (.lit 0)
      (lets ([("ab", .inr .int .unit)] ++ tuple "o" [v "sb", v "ab"]) (.ret (v "o0")))
      (lets (lane x "mk" "b" ++
             [("sr", bo .or (v "base") (v "b")), ("s", .band (v "sr") (v "cv")),
              ("k2", .loadAtF (v "sb") (v "s") [0]), ("kk", .pair (v "k") (v "k2")),
              ("t", .callc (v "eq") (v "kk"))])
        (.case (v "t")
          "t1" (lets ([("fo", .inl .unit (v "sr"))] ++ tuple "o" [v "sb", v "fo"]) (.ret (v "o0")))
          "f1" (lets (clearLow "mk" "mk1" ++ tuple "n" [v "sb", v "cv", v "k", v "eq", v "base", v "mk1"])
            (.tail "cand" ["c"] (v "n0") [K, V])))))

/-- `freeSlot` [m]: the first empty-or-deleted slot from `pos`: `(cb, sr, isEmpty)`. -/
def freeSlotD (x : Bool) : Decl where
  name := "freeSlot"; tparams := []; idx := ["m"]; arg := "a"
  argTy := .prod (CB x (.var 0)) (.prod (.intS (.var 0)) (.prod .int .int))
  retTy := .prod (CB x (.var 0)) (.prod .int .int)
  body := splits "a" ["cb", "mv", "pos", "st"]
    (lets ([("g", .band (v "pos") (v "mv"))] ++ load x "cb" "g" "G" ++ freeOps x "G")
      (.ifeq (v "Gfr") (.lit 0)
        (lets ([("st1", bo .wadd (v "st") (.lit 1)), ("pos1", bo .wadd (v "pos") (v "st1"))] ++
               tuple "n" [v "cb", v "mv", v "pos1", v "st1"])
          (.tail "freeSlot" ["m"] (v "n0") []))
        (lets (emptyOps x "G" ++
               [("bz", .bit1 .ctz (v "Gfr")), ("b", bo .shr (v "bz") (.lit (if x then 0 else 3))),
                ("e1", bo .shr (v "Gem") (v "bz")), ("isE", bo .and (v "e1") (.lit 1)),
                ("base", bo .shl (v "g") (.lit (lgW x))), ("sr", bo .or (v "base") (v "b"))] ++
               tuple "o" [v "cb", v "sr", v "isE"])
          (.ret (v "o0")))))

/-- Write control byte `val` into lane `b` (mod 8) of control word `wi`: one
byte store (`stlw`), as in absl. -/
def ctrlStore (wi : String) : Expr :=
  lets [("v8", .cvt false .w8 (v "val")), ("u", .stlw (v "cb") (v wi) (v "b") (v "v8"))]
    (.ret (v "cb"))

/-- `setCtrl` [m]: write control byte `val` for raw slot `sr`. -/
def setCtrlD (x : Bool) : Decl where
  name := "setCtrl"; tparams := []; idx := ["m"]; arg := "a"
  argTy := .prod (CB x (.var 0)) (.prod (.intS (.var 0)) (.prod .int .int))
  retTy := CB x (.var 0)
  body := splits "a" ["cb", "mv", "sr", "val"]
    (lets [("gi", bo .shr (v "sr") (.lit (lgW x))), ("g", .band (v "gi") (v "mv")),
           ("b", bo .and (v "sr") (.lit (W x - 1)))]
      (if x then
        lets [("sel", bo .shr (v "b") (.lit 3)), ("g2", .add (v "g") (v "g"))]
          (.ifeq (v "sel") (.lit 0) (ctrlStore "g2") (lets [("g3", .add (v "g2") (.lit 1))] (ctrlStore "g3")))
      else ctrlStore "g"))

/-- `eraseCtrl` [m]: mark `sr` empty (flag `1`) if its group still has an empty
slot, else deleted (flag `0`). -/
def eraseCtrlD (x : Bool) : Decl where
  name := "eraseCtrl"; tparams := []; idx := ["m"]; arg := "a"
  argTy := .prod (CB x (.var 0)) (.prod (.intS (.var 0)) .int)
  retTy := .prod (CB x (.var 0)) .int
  body := splits "a" ["cb", "mv", "sr"]
    (lets ([("gi", bo .shr (v "sr") (.lit (lgW x))), ("g", .band (v "gi") (v "mv"))] ++
           load x "cb" "g" "G" ++ emptyOps x "G")
      (.ifeq (v "Gem") (.lit 0)
        (lets (tuple "q" [v "cb", v "mv", v "sr", .lit 1] ++ [("cb2", .call "setCtrl" ["m"] (v "q0") [])] ++
               tuple "o" [v "cb2", .lit 0]) (.ret (v "o0")))
        (lets (tuple "q" [v "cb", v "mv", v "sr", .lit 0] ++ [("cb2", .call "setCtrl" ["m"] (v "q0") [])] ++
               tuple "o" [v "cb2", .lit 1]) (.ret (v "o0")))))

/-- Pack `((mv, cv), (cb, sb))` as a table at sizes `m`, `c`. -/
def mkTblD (x : Bool) : Decl where
  name := "mkTbl"; tparams := [κKz, κVz]; idx := ["m", "c"]; arg := "a"
  argTy := tblBody x (.var 1) (.var 0); retTy := Tbl x
  body := splits "a" ["mc", "bs"] (splits "mc" ["mv", "cv"] (splits "bs" ["cb", "sb"]
    (lets [("s0", .pair (v "cv") (v "sb")), ("s", .pack (v "s0") "c" Slots),
           ("mb", .pair (v "mv") (v "cb")), ("t", .pair (v "mb") (v "s")),
           ("o", .pack (v "t") "m" (Tbl x))] (.ret (v "o")))))

/-! ## The operations -/

/-- Take the map `mp` apart and hash `k`; `cont` sees `gl`, `n`, `fs`, `hash`,
`eq`, `h2`, `pos`, `m`, `c`, `mv`, `cv`, `cb`, `sb`. -/
def opening (cont : Expr) : Expr :=
  splits "mp" ["tb", "gn", "fs"] (splits "fs" ["hash", "eq"] (splits "gn" ["gl", "n"]
    (lets hashOps (.unpack (v "tb") "m" "t1" (splits "t1" ["mcb", "sl"] (splits "mcb" ["mv", "cb"]
      (.unpack (v "sl") "c" "t2" (splits "t2" ["cv", "sb"] cont))))))))

/-- Probe for `k`; `cont` sees `cb1`, `sb1`, `res`. -/
def finding (cont : Expr) : Expr :=
  lets (tuple "fq" [v "cb", v "sb", v "mv", v "cv", v "k", v "eq", v "h2", v "pos", .lit 0] ++
        [("fr", .call "find" ["m", "c"] (v "fq0") [K, V])])
    (splits "fr" ["cb1", "sb1", "res"] cont)

/-- The map back together, as `out`. -/
def repack (cb sb gl n out : String) : List (String × Op) :=
  [("rmc", .pair (v "mv") (v "cv")), ("rbs", .pair (v cb) (v sb)), ("rtb", .pair (v "rmc") (v "rbs")),
   ("rt", .call "mkTbl" ["m", "c"] (v "rtb") [K, V]), ("rgn", .pair (v gl) (v n)),
   ("rr", .pair (v "rgn") (v "fs")), (out, .pair (v "rt") (v "rr"))]

def done (cb sb gl n r : String) : Expr :=
  lets (repack cb sb gl n "mo" ++ [("out", .pair (v "mo") (v r))]) (.ret (v "out"))

/-- Place `(k, val)` in the first free slot from `pos` (the key is absent):
`fin` sees `cb3`, `gl1`, `n1`; the slot buffer is `sb`. -/
def place (cb sb : String) (fin : Expr) : Expr :=
  lets (tuple "fz" [v cb, v "mv", v "pos", .lit 0] ++ [("fs2", .call "freeSlot" ["m"] (v "fz0") [])])
    (splits "fs2" ["cb2", "sr", "isE"]
      (lets (tuple "sq" [v "cb2", v "mv", v "sr", v "h2"] ++
             [("cb3", .call "setCtrl" ["m"] (v "sq0") []), ("s", .band (v "sr") (v "cv")),
              ("kv", .pair (v "k") (v "val")), ("old", .xchgAt (v sb) (v "s") (v "kv")),
              ("gl1", bo .wsub (v "gl") (v "isE")), ("n1", bo .wadd (v "n") (.lit 1))]) fin))

/-- `insert(k, v)`: the map, and the displaced value (`inr old`) or `inl ()`. -/
def insertD (x : Bool) : Decl where
  name := "insert"; tparams := [κKz, κVz]; idx := []; arg := "a"
  argTy := .prod (MapT x) (.prod K V); retTy := .prod (MapT x) SV
  body := splits "a" ["mp", "k", "val"] (opening (finding
    (.case (v "res")
      "sr" (lets [("s", .band (v "sr") (v "cv")), ("old", .xchgAtF (v "sb1") (v "s") [1] (v "val")),
                  ("ro", .inr .unit (v "old"))] (done "cb1" "sb1" "gl" "n" "ro"))
      "u" (.ifeq (v "gl") (.lit 0)
            (lets (repack "cb1" "sb1" "gl" "n" "mo" ++ [("g", .call "grow" [] (v "mo") [K, V])] ++
                   tuple "w" [v "g", v "k", v "val"])
              (.tail "insert" [] (v "w0") [K, V]))
            (place "cb1" "sb1" (lets [("ro", .inl V .unit)] (done "cb3" "sb1" "gl1" "n1" "ro")))))))

/-- `lookup(k)`: a copy of the value; `V : copy`. -/
def lookupD (x : Bool) : Decl where
  name := "lookup"; tparams := [κKz, κVzc]; idx := []; arg := "a"
  argTy := .prod (MapT x) K; retTy := .prod (MapT x) SV
  body := splits "a" ["mp", "k"] (opening (finding
    (.case (v "res")
      "sr" (lets [("s", .band (v "sr") (v "cv")), ("y", .loadAtF (v "sb1") (v "s") [1]),
                  ("ro", .inr .unit (v "y"))] (done "cb1" "sb1" "gl" "n" "ro"))
      "u" (lets [("ro", .inl V .unit)] (done "cb1" "sb1" "gl" "n" "ro")))))

/-- `take(k)`: move the value out (a zero goes in); the key stays. -/
def takeD (x : Bool) : Decl where
  name := "take"; tparams := [κKz, κVz]; idx := []; arg := "a"
  argTy := .prod (MapT x) K; retTy := .prod (MapT x) SV
  body := splits "a" ["mp", "k"] (opening (finding
    (.case (v "res")
      "sr" (lets ([("s", .band (v "sr") (v "cv")), ("z", .zero V),
                   ("old", .xchgAtF (v "sb1") (v "s") [1] (v "z"))] ++
                  tuple "ez" [v "cb1", v "mv", v "sr"] ++ [("er", .call "eraseCtrl" ["m"] (v "ez0") [])])
        (splits "er" ["cb2", "fl"]
          (lets [("gl1", bo .wadd (v "gl") (v "fl")), ("n1", bo .wsub (v "n") (.lit 1)),
                 ("ro", .inr .unit (v "old"))] (done "cb2" "sb1" "gl1" "n1" "ro"))))
      "u" (lets [("ro", .inl V .unit)] (done "cb1" "sb1" "gl" "n" "ro")))))

/-- `new(hash, eq)`: one group, `W − W/8` fresh slots before growth. -/
def newD (x : Bool) : Decl where
  name := "new"; tparams := [κKz, κVz]; idx := []; arg := "a"
  argTy := Fns; retTy := MapT x
  body := lets ([("m0", .nameI (.lit 0)), ("c0", .nameI (.lit (W x - 1))), ("s0", .add (v "m0") (.lit 1))] ++
      (if x then [("cc", .add (v "s0") (v "s0"))] else [("cc", .atom (v "s0"))]) ++
      [("cb", .newBuf (v "cc") (.lanes false .w8)), ("sc", .add (v "c0") (.lit 1)), ("sb", .newBuf (v "sc") ST),
       ("mc", .pair (v "m0") (v "c0")), ("bs", .pair (v "cb") (v "sb")), ("tb0", .pair (v "mc") (v "bs")),
       ("tb", .call "mkTbl" ["m0", "c0"] (v "tb0") [K, V]),
       ("gn", .pair (.lit (W x - W x / 8)) (.lit 0)), ("r1", .pair (v "gn") (v "a")),
       ("mp", .pair (v "tb") (v "r1"))])
    (.ret (v "mp"))

/-- `rawIns`: insert a key known to be absent (growth's reinsertion). -/
def rawInsD (x : Bool) : Decl where
  name := "rawIns"; tparams := [κKz, κVz]; idx := []; arg := "a"
  argTy := .prod (MapT x) (.prod K V); retTy := MapT x
  body := splits "a" ["mp", "k", "val"] (opening
    (place "cb" "sb" (lets (repack "cb3" "sb" "gl1" "n1" "mo") (.ret (v "mo")))))

/-! ## Growth: twice the groups, every full slot moved across by value -/

def growD (x : Bool) : Decl where
  name := "grow"; tparams := [κKz, κVz]; idx := []; arg := "a"
  argTy := MapT x; retTy := MapT x
  body := splits "a" ["tb", "gn", "fs"] (.unpack (v "tb") "m" "t1" (splits "t1" ["mcb", "sl"]
    (splits "mcb" ["mv", "ocb"] (.unpack (v "sl") "c" "t2" (splits "t2" ["cv", "osb"]
      (lets ([("mv2", .add (v "mv") (v "mv")), ("mv3", .add (v "mv2") (.lit 1)), ("m2", .nameI (v "mv3")),
              ("s2", .add (v "m2") (.lit 1))] ++
             (if x then [("cc", .add (v "s2") (v "s2"))] else [("cc", .atom (v "s2"))]) ++
             [("cb", .newBuf (v "cc") (.lanes false .w8)),
              ("d1", .add (v "s2") (v "s2")), ("d2", .add (v "d1") (v "d1")), ("d3", .add (v "d2") (v "d2"))] ++
             (if x then [("d4", .add (v "d3") (v "d3")), ("c2r", .sub (v "d4") (.lit 1))]
              else [("c2r", .sub (v "d3") (.lit 1))]) ++
             [("c2", .nameI (v "c2r")), ("sc", .add (v "c2") (.lit 1)), ("sb", .newBuf (v "sc") ST),
              ("mc", .pair (v "m2") (v "c2")), ("bs2", .pair (v "cb") (v "sb")), ("tb0", .pair (v "mc") (v "bs2")),
              ("tb2", .call "mkTbl" ["m2", "c2"] (v "tb0") [K, V]),
              ("capI", bo .wadd (v "c2") (.lit 1)), ("c8", bo .shr (v "capI") (.lit 3)),
              ("gl", bo .wsub (v "capI") (v "c8")), ("gn2", .pair (v "gl") (.lit 0)),
              ("r1", .pair (v "gn2") (v "fs")), ("nm", .pair (v "tb2") (v "r1")), ("i0", .nameI (.lit 0))] ++
             tuple "gq" [v "nm", v "ocb", v "osb", v "i0", v "mv", v "cv"] ++
             [("res", .call "mvG" ["i0", "m", "c"] (v "gq0") [K, V])])
        (.ret (v "res"))))))))

/-- `mvG` [i, d, c]: move the full slots of old groups `i … i+d`. -/
def mvGD (x : Bool) : Decl :=
  let n : Idx := .add (.add (.var 2) (.lit 1)) (.var 1)
  { name := "mvG", tparams := [κKz, κVz], idx := ["i", "d", "c"], arg := "a"
    argTy := .prod (MapT x) (.prod (buf .own (.lanes false .w8) (ctrlS x n) (ctrlS x n)) (.prod (SB (.var 0))
      (.prod (.intS (.var 2)) (.prod (.intS (.var 1)) (.intS (.var 0))))))
    retTy := MapT x
    body := splits "a" ["nm", "ocb", "osb", "iv", "dv", "ocv"]
      (lets (load x "ocb" "iv" "G" ++ fullOps x "G" ++ [("base", bo .shl (v "iv") (.lit (lgW x)))] ++
             tuple "lq" [v "osb", v "ocv", v "nm", v "base", v "Gfu"] ++
             [("lr", .call "mvL" ["c"] (v "lq0") [K, V])])
        (splits "lr" ["osb1", "nm1"]
          (.ifeq (v "dv") (.lit 0) (.ret (v "nm1"))
            (lets ([("d1", .sub (v "dv") (.lit 1)), ("un", .nameI (v "d1")),
                    ("i1", .add (v "iv") (.lit 1)), ("jn", .nameI (v "i1"))] ++
                   tuple "n" [v "nm1", v "ocb", v "osb1", v "jn", v "un", v "ocv"])
              (.tail "mvG" ["jn", "un", "c"] (v "n0") [K, V]))))) }

/-- `mvL` [c]: move the full lanes `fm` of the old group at slot `base`. -/
def mvLD (x : Bool) : Decl where
  name := "mvL"; tparams := [κKz, κVz]; idx := ["c"]; arg := "a"
  argTy := .prod (SB (.var 0)) (.prod (.intS (.var 0)) (.prod (MapT x) (.prod .int .int)))
  retTy := .prod (SB (.var 0)) (MapT x)
  body := splits "a" ["osb", "ocv", "nm", "base", "fm"]
    (.ifeq (v "fm") (.lit 0) (lets (tuple "o" [v "osb", v "nm"]) (.ret (v "o0")))
      (lets (lane x "fm" "b" ++
             [("sr", bo .or (v "base") (v "b")), ("s", .band (v "sr") (v "ocv")), ("z", .zero ST),
              ("kv", .xchgAt (v "osb") (v "s") (v "z"))])
        (splits "kv" ["k", "val"]
          (lets (tuple "w" [v "nm", v "k", v "val"] ++ [("nm1", .call "rawIns" [] (v "w0") [K, V])] ++
                 clearLow "fm" "fm1" ++ tuple "n" [v "osb", v "ocv", v "nm1", v "base", v "fm1"])
            (.tail "mvL" ["c"] (v "n0") [K, V])))))

def lib (x : Bool) : Prog :=
  [mkTblD x, findD x, candD x, freeSlotD x, setCtrlD x, eraseCtrlD x, newD x, insertD x,
   lookupD x, takeD x, rawInsD x, growD x, mvGD x, mvLD x]

#guard accepts (checkProg (lib false))
#guard accepts (checkProg (lib true))

/-! ## The word primitives, evaluated -/

/-- The exact zero-byte test, as the portable group code computes it. -/
def zbN (y : Nat) : Nat :=
  bit1N .not (bitN .or (bitN .or (bitN .wadd (bitN .and y Lo7) Lo7) y) Lo7)

-- Bytes (low first) 00 7F 01 00 80 FF 00 01: zero at 0, 3, 6 — and not at 7,
-- the `01` above a `00` where absl's approximate test gives a false positive.
#guard zbN 0x0100FF8000017F00 == 0x0080000080000080
#guard bitN .wsub 0 1 == W64 - 1
#guard bitN .mulhi (2 ^ 63) 4 == 2
#guard bitN .shl 3 63 == 2 ^ 63 && bitN .shr (2 ^ 63) 63 == 1
#guard bitN .msb16 0x8000000000000080 0x80 == 0x181
#guard bit1N .ctz 0 == 64 && bit1N .ctz 0x80 == 7 && bit1N .popcnt 0xF0F0 == 8
#guard vmatchN 0x850085 0x85 0x85 == 0x105
#guard vmatchN 0 0 0 == 0xFFFF

/-! ## An instance: plain `Int` keys and values -/

def fStep (f mIn tag : String) (argOps : List (String × Op)) (arg : At) (k : Expr) : Expr :=
  lets (argOps ++ [(tag ++ "w", .pair (v mIn) arg), (tag ++ "r", .call f [] (v (tag ++ "w")) [.int, .int])])
    (.split (v (tag ++ "r")) (tag ++ "m") (tag ++ "o")
      (lets [(tag, .call "unw" [] (v (tag ++ "o")))] k))

/-- A script step `(op, tag, key, value)`: `i`nsert, `l`ookup, `t`ake. -/
def chain (mIn : String) : List (Char × String × Nat × Nat) → Expr → Expr
  | [], fin => fin
  | (op, tag, key, val) :: r, fin =>
      let f := if op == 'i' then "insert" else if op == 'l' then "lookup" else "take"
      let (ops, arg) : List (String × Op) × At :=
        if op == 'i' then ([(tag ++ "kv", .pair (.lit key) (.lit val))], v (tag ++ "kv")) else ([], .lit key)
      fStep f mIn tag ops arg (chain (tag ++ "m") r fin)

/-- Keys `1‥n`, an overwrite, a `take`, a miss, a re-insert; with `sum`, every
key is then looked up and the values summed.  Growth comes at the 8th fresh key
(portable) or the 15th (x64). -/
def script (n : Nat) (sum : Bool) : List (Char × String × Nat × Nat) :=
  ((List.range n).map fun i => ('i', s!"I{i + 1}", i + 1, 101 + i)) ++
  [('i', "O3", 3, 333), ('l', "L3", 3, 0), ('t', "T5", 5, 0), ('l', "L5", 5, 0), ('l', "Ln", n, 0),
   ('l', "L21", 21, 0), ('t', "T21", 21, 0), ('i', "R5", 5, 55), ('l', "L5b", 5, 0)] ++
  (if sum then (List.range n).map fun i => ('l', s!"S{i + 1}", i + 1, 0) else [])

def sumOps (n : Nat) (sum : Bool) : List (String × Op) :=
  if sum then
    ("acc1", .atom (v "S1")) :: (List.range (n - 1)).map fun i =>
      (s!"acc{i + 2}", bo .wadd (v s!"acc{i + 1}") (v s!"S{i + 2}"))
  else [(s!"acc{n}", .atom (.lit 0))]

def useD (n : Nat) (sum : Bool) : Decl where
  name := "use"; idx := []; arg := "a"; argTy := .unit
  retTy := .prod .int (.prod .int (.prod .int (.prod .int (.prod .int (.prod .int (.prod .int
    (.prod .int (.prod .int (.prod .int .int)))))))))
  body := lets [("h", .fnptr "hashInt"), ("e", .fnptr "eqInt"), ("fs", .pair (v "h") (v "e")),
                ("m", .call "new" [] (v "fs") [.int, .int])]
    (chain "m" (script n sum) (lets (sumOps n sum ++ tuple "o" [v "O3", v "L3", v "T5", v "L5", v "Ln",
        v "L21", v "T21", v "R5", v "L5b", v "I1", v s!"acc{n}"]) (.ret (v "o0"))))

def instLib (x : Bool) (n : Nat) (sum : Bool) : Prog := lib x ++ [hashIntD, eqIntD, unwD, useD n sum]

#guard accepts (checkProg (instLib false 9 false))
#guard accepts (checkProg (instLib true 20 true))

/-- The sum is `Σ (100 + i) + (333 − 103) + (55 − 105)`. -/
def expected (n : Nat) (sum : Bool) : List WeakMem.Val :=
  [.num 103, .num 333, .num 105, .num 0, .num (100 + n), .num 0, .num 0, .num 0, .num 55, .num 0,
   .num (if sum then (List.range n).foldl (fun a i => a + 101 + i) 0 + 230 - 50 else 0)]

def setup (x : Bool) (n : Nat) (sum : Bool) : Option Setup :=
  runSetup (instLib x n sum) "hashInt" [] .int [cst (.num 0)]

/-- Run the script on the promise machine. -/
def runUse (x : Bool) (n : Nat) (sum : Bool) (fuel : Nat) : Bool :=
  let r := runE (instLib x n sum) (setup x n sum) (fun _ => [("use", [], .unit, [])]) 0 fuel
  clean r && resultsOf r 0 == [expected n sum]

-- The machine keeps every message, so a run's cost grows with its length; the
-- gate runs one growth per target.  FlatHashMapSlow.lean runs 20 keys, summed.
#guard runUse false 9 false 8000
#guard runUse true 15 false 12000

/-! ## Owned values: `V = Ptr? own Int` (Zeroable: null) -/

def PO : Ty := .ptrOpt .own .int
/-- A displaced box's contents, or `0`. -/
def unbD : Decl := dcl "unbo" (.sum .unit PO) .int
  (.case (v "a") "e" (.ret (.lit 0)) "p"
    (.ifnull (v "p") (.ret (.lit 0)) "q" (lets [("y", .load false (v "q"))] (.ret (v "y")))))

def boxStep (f mIn tag : String) (argOps : List (String × Op)) (arg : At) (k : Expr) : Expr :=
  lets (argOps ++ [(tag ++ "w", .pair (v mIn) arg), (tag ++ "r", .call f [] (v (tag ++ "w")) [.int, PO])])
    (.split (v (tag ++ "r")) (tag ++ "m") (tag ++ "o")
      (lets [(tag, .call "unbo" [] (v (tag ++ "o")))] k))
def bIns (mIn tag : String) (key val : Nat) (k : Expr) : Expr :=
  boxStep "insert" mIn tag [(tag ++ "x", .call "idI" [] (.lit val)), (tag ++ "b", .new (v (tag ++ "x"))),
    (tag ++ "kv", .pair (.lit key) (v (tag ++ "b")))] (v (tag ++ "kv")) k
def bTake (mIn tag : String) (key : Nat) (k : Expr) : Expr :=
  boxStep "take" mIn tag [] (.lit key) k

/-- Boxes go in; the overwritten box and the taken one come back out, owned. -/
def ownD : Decl where
  name := "own"; idx := []; arg := "a"; argTy := .unit
  retTy := .prod .int (.prod .int (.prod .int .int))
  body := lets [("h", .fnptr "hashInt"), ("e", .fnptr "eqInt"), ("fs", .pair (v "h") (v "e")),
                ("m", .call "new" [] (v "fs") [.int, PO])]
    (bIns "m" "A" 1 10 <| bIns "Am" "B" 2 20 <| bIns "Bm" "C" 1 11 <| bTake "Cm" "D" 2 <|
     bTake "Dm" "E" 2 <| bTake "Em" "F" 1 <|
     lets (tuple "o" [v "C", v "D", v "E", v "F"]) (.ret (v "o0")))

def ownLib (x : Bool) : Prog := lib x ++ [hashIntD, eqIntD, HashMapOwn.idID, unbD, ownD]

#guard accepts (checkProg (ownLib false))
#guard accepts (checkProg (ownLib true))

def ownSetup (x : Bool) : Option Setup := runSetup (ownLib x) "idI" [] .int [cst (.num 0)]
def ownThr (_ : Setup) : List (String × List Ty × Ty × List Word) := [("own", [], .unit, [])]

#guard let r := runE (ownLib true) (ownSetup true) ownThr 0 20000
  clean r && resultsOf r 0 == [[.num 10, .num 20, .num 0, .num 11]]
#guard let r := runE (ownLib false) (ownSetup false) ownThr 0 20000
  clean r && resultsOf r 0 == [[.num 10, .num 20, .num 0, .num 11]]

/-! ## Hazards -/

-- `lookup` copies: an owned value type is refused by kind.
#guard rejects (checkDecl (ownLib true) { ownD with
    body := lets [("h", .fnptr "hashInt"), ("e", .fnptr "eqInt"), ("fs", .pair (v "h") (v "e")),
      ("m", .call "new" [] (v "fs") [.int, PO]), ("w", .pair (v "m") (.lit 1)),
      ("x", .call "lookup" [] (v "w") [.int, PO])] (.ret .unit), retTy := .unit })
  "a type argument does not have its parameter's kind"
-- A `band` result indexes a buffer of capacity `n + 1` …
def bandIdx (j : Op) : Decl :=
  dcl "bi" (.prod (.intS (.var 0)) .int) .int (splits "a" ["nv", "y"]
    (lets [("c", .add (v "nv") (.lit 1)), ("b", .newBuf (v "c") .int), ("j", j),
           ("r", .loadAt (v "b") (v "j"))] (.ret (v "r")))) (idx := ["n"])
#guard accepts (checkDecl [] (bandIdx (.band (v "y") (v "nv"))))
-- … a plain `and` gives no bound …
#guard rejects (checkDecl [] (bandIdx (bo .and (v "y") (v "nv")))) "expected an integer of known index"
-- … nor does a literal mask …
#guard rejects (checkDecl [] (bandIdx (.band (v "y") (.lit 7))))
  "band: the mask must be an undetermined index variable"
-- … and one mask variable bounds one `band` per block.
#guard rejects (checkDecl [] (dcl "b2" (.prod (.intS (.var 0)) .int) .int (splits "a" ["nv", "y"]
    (lets [("j", .band (v "y") (v "nv")), ("j2", .band (v "y") (v "nv"))] (.ret (v "y")))) (idx := ["n"])))
  "band: the mask must be an undetermined index variable"
-- Field paths: into a pair only; an affine component is not copied; the value
-- must have the component's type.
def PB : Ty := .prod .int PO
#guard rejects (checkDecl [] (dcl "fp" .unit .int
    (lets [("b", .newBuf (.lit 2) .int), ("x", .loadAtF (v "b") (.lit 0) [0])] (.ret (v "x")))))
  "loadAtF: bad field path"
#guard rejects (checkDecl [] (dcl "fa" .unit .unit
    (lets [("b", .newBuf (.lit 2) PB), ("x", .loadAtF (v "b") (.lit 0) [1])] (.ret .unit))))
  "loadAtF would duplicate"
#guard accepts (checkDecl [] (dcl "fx" .unit .int
    (lets [("b", .newBuf (.lit 2) PB), ("z", .zero PO), ("o", .xchgAtF (v "b") (.lit 1) [1] (v "z")),
           ("x", .loadAtF (v "b") (.lit 1) [0])] (.ret (v "x")))))
#guard rejects (checkDecl [] (dcl "fw" .unit .unit
    (lets [("b", .newBuf (.lit 2) PB), ("o", .xchgAtF (v "b") (.lit 1) [0] .unit)] (.ret .unit))))
  "xchgAtF: the value does not have the component type"
-- `zero` only at a Zeroable type; the word ops only on integers.
#guard rejects (checkDecl [] (dcl "z" .unit .unit
    (lets [("z", .zero (.ptr .own .int))] (.ret .unit)))) "zero: the type is not Zeroable"
#guard rejects (checkDecl [] (dcl "vm" .unit .int
    (lets [("x", .vmatch .unit (.lit 0) (.lit 0))] (.ret (v "x"))))) "vmatch needs integers"

end FlatHashMap
