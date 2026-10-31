import WeakCore.RWLock

/-!
# HashMap — a polymorphic hash map, written once

Open addressing with linear probing.  Two columns, each laid out per instance
(CoreLang §3.5's tiers): `keys : Buf (() + K)` and `vals : Buf (() + V)`.  With
`K`, `V` at most a word each, both columns are unboxed (`wide`, or `niche` for
pointers); a wider payload boxes only its own column.

* **Capabilities** (Caps.lean): every operation takes `Cap s r` and a
  `Ptr (rgn r) (Map r K V)`, so one library serves a private map (lend the
  token) and a readers–writer map (`bor` from the writer's token, `rd` from a
  reader's share).  `lookup` asks for `rd`; `insert`, `take` ask for `bor`.
* **The map lives in a region from birth.**  A region cell holds no `own`
  reference (D1), so the columns are region buffers of the map's own region
  `r`, which is part of the map's type: `hmNew` opens the key column as the
  region (`region`), moves the value column and the map cell in (`intoRgn`,
  one `dmb ishst` each) and returns `∃r. Ptr r (Map r K V) × Tok r`; `grow`
  moves each fresh column in the same way.  A table type that names its
  region is packed in the region's scope (`pack`'s target may mention the
  index variables in scope).
* **Hash and equality** are `code` values (`fnptr`), stored in the map, called
  with `callc`: a map cannot be probed with a different hash from the one that
  built it.
* **Indices are static.** `rem h n` gives a slot index below `n = m + 1`; loops
  over slots carry `i + 1 + d` capacities.  No dynamic bounds checks.
* **Affine values** move in and out by `xchg` (`insert` returns the displaced
  value, `take` removes).  A region cell holds no `own` reference (D1), so
  `V : noOwn` — affine is fine (tokens), `own` is not.  `V :
  noWord` too: `insert` writes a slot by a plain exchange, which must not reach
  a protocol word.  `lookup` copies, so it needs `V : copy`.
* **Deletion** leaves the key as a tombstone (`vals` slot empty); a resize drops
  tombstones.  `lim` counts the fresh keys left before a resize; `full` is the
  count at the current capacity.  No comparison operator exists, so both are
  counted down with `ifeq`/`sub` on `∃n. Int(n)` cells.
-/

namespace HashMap
open CoreLang CoreTerm TermRun TermSmoke

/-! ## Types -/

/-- Keys are copied out of the key column; the column is a region buffer, so
no `own` reference may be inside a key (`copy` does not imply `noOwn` in the
kind lattice: an own reference is affine, but the kind says only what it says). -/
def κK : Kind := { copy := true, noOwn := true }
def κV : Kind := { noOwn := true, noWord := true }
def κVc : Kind := { noOwn := true, copy := true, noWord := true }

/-- In every generic declaration: `tparams := [κK, κV]`, so `K` is `tvar 1`. -/
def K : Ty := .tvar 1
def V : Ty := .tvar 0
def bool : Ty := .sum .unit .unit
def SK : Ty := .sum .unit K
def SV : Ty := .sum .unit V
def c1 : Idx := .add (.var 0) (.lit 1)
/-- `∃n. Int(n+1) × Buf μ SK (n+1) (n+1) × Buf μ SV (n+1) (n+1)`: the columns at
mode `μ` (as seen under the package's binder). -/
def TblIn (μ : Mode) : Ty := .iex (.prod (.intS c1) (.prod (buf μ SK c1 c1) (buf μ SV c1 c1)))
/-- The table by value, columns own (HashMapOwn). -/
def Tbl : Ty := TblIn .own
def LimT : Ty := .iex (.intS (.var 0))
def Fns : Ty := .prod (.code K .int .plain) (.code (.prod K K) bool .plain)
/-- The table, `(lim, full)`, and the functions. -/
def MapTIn (μ : Mode) : Ty := .prod (TblIn μ) (.prod (.prod LimT LimT) Fns)
def MapT : Ty := MapTIn .own
/-- The table in region `r` (`r` an index of the scope outside the package). -/
def TblR (r : Idx) : Ty := TblIn (.rgn (r.shift 0))
/-- The map in region `r`: its columns are region buffers of `r`. -/
def MapTR (r : Idx) : Ty := MapTIn (.rgn (r.shift 0))
def MP (r : Idx) : Ty := .ptr (.rgn r) (MapTR r)
/-- What `hmNew` returns: the map in a fresh region, with the region's token. -/
def NewMap : Ty := .iex (.prod (MP (.var 0)) (.tok (.var 0) none))

/-- Pair up atoms right-nested under fresh names `pfx0, pfx1, …`; the result is `pfx0`. -/
def tuple (pfx : String) (xs : List At) : List (String × Op) :=
  let n := xs.length
  let nm (i : Nat) : String := pfx ++ toString i
  (List.range (n - 1)).reverse.map fun i =>
    (nm i, .pair (xs.getD i .unit) (if i + 2 == n then xs.getD (n - 1) .unit else .var (nm (i + 1))))

/-! ## Filling a fresh column with `inl ()`

Generic `() + α` is not statically Zeroable (its tier depends on `α`), so a new
column is filled in order: `Buf (i+1+d) i → Buf (i+1+d) (i+1+d)`.  At a Zeroable
instance the machine has already zeroed it; the loop rewrites the zeros. -/

def fillD : Decl where
  name := "fill"; tparams := [{}]; idx := ["i", "d"]; arg := "a"
  argTy := .prod (.intS (.var 1)) (.prod (.intS (.var 0))
    (buf .own (.sum .unit (.tvar 0)) (.add (.add (.var 1) (.lit 1)) (.var 0)) (.var 1)))
  retTy := let n : Idx := .add (.add (.var 1) (.lit 1)) (.var 0); buf .own (.sum .unit (.tvar 0)) n n
  body := .split (v "a") "iv" "r1" (.split (v "r1") "dv" "b"
    (lets [("e", .inl (.tvar 0) .unit), ("b2", .bufInit (v "b") (v "iv") (v "e"))]
      (.ifeq (v "dv") (.lit 0) (.ret (v "b2"))
        (lets ([("d1", .sub (v "dv") (.lit 1)), ("u", .nameI (v "d1")),
                ("i1", .add (v "iv") (.lit 1)), ("j", .nameI (v "i1"))] ++
               tuple "q" [v "j", v "u", v "b2"])
          (.tail "fill" ["j", "u"] (v "q0") [.tvar 0])))))

/-- Two fresh columns of capacity `z + 1` (`c2 : Int(z+1)`), filled: `kf`, `vf`.
(`nameI i0n` binds one index variable.) -/
def newCols (z c2 : String) : List (String × Op) :=
  [("kb2", .newBuf (v c2) SK), ("vb2", .newBuf (v c2) SV), ("i0n", .nameI (.lit 0))] ++
  tuple "x" [v "i0n", v z, v "kb2"] ++ [("kf", .call "fill" ["i0n", z] (v "x0") [K])] ++
  tuple "y" [v "i0n", v z, v "vb2"] ++ [("vf", .call "fill" ["i0n", z] (v "y0") [V])]

/-- A fresh table by value, packed as `out` (HashMapOwn). -/
def newTable (z c2 out : String) : List (String × Op) :=
  newCols z c2 ++ tuple "nt" [v c2, v "kf", v "vf"] ++ [(out, .pack (v "nt0") z Tbl)]

/-- A fresh table whose columns are moved into region `rn` (`r`: its index at
the `pack`, after `newCols`'s binder), packed as `out`. -/
def newTableR (rn : String) (r : Idx) (z c2 out : String) : List (String × Op) :=
  newCols z c2 ++ [("kr", .intoRgn rn (v "kf")), ("vr", .intoRgn rn (v "vf"))] ++
  tuple "nt" [v c2, v "kr", v "vr"] ++ [(out, .pack (v "nt0") z (TblR r))]

/-- The `(lim, full)` pair at `l4 = 4`, and the map cell `m0 = (tb, (lf, fs))`. -/
def mapCell (tb fs : String) : List (String × Op) :=
  [("l4", .nameI (.lit 4)), ("lim", .pack (v "l4") "l4" LimT), ("full", .pack (v "l4") "l4" LimT),
   ("lf", .pair (v "lim") (v "full"))] ++ tuple "m" [v tb, v "lf", v fs]

/-- `new(hash, eq)`: capacity 8, room for 4 fresh keys.  The key column is
opened as the map's region; the value column and the map cell are moved in. -/
def newD : Decl where
  name := "hmNew"; tparams := [κK, κV]; idx := []; arg := "a"
  argTy := Fns; retTy := NewMap
  body := lets ([("z", .nameI (.lit 7)), ("c2", .add (v "z") (.lit 1))] ++ newCols "z" "c2")
    (.region (v "kf") "r" "kb" "t"
      (lets ([("vr", .intoRgn "r" (v "vf"))] ++ tuple "nt" [v "c2", v "kb", v "vr"] ++
             [("tb", .pack (v "nt0") "z" (TblR (.var 0)))] ++ mapCell "tb" "a" ++
             [("p", .new (v "m0") (some (MapTR (.var 1)))), ("d", .intoRgn "r" (v "p")), ("g", .pair (v "d") (v "t")),
              ("res", .pack (v "g") "r" NewMap)])
        (.ret (v "res"))))

/-! ## Probing

`probe` walks from `pos`: `inl pos` if slot `pos mod n` holds `k`, `inr pos` if
it is empty.  It returns the unreduced position; the caller reduces it again
with its own `rem`.  Terminates because `lim` keeps a slot empty. -/

def probeD : Decl where
  name := "probe"; tparams := [κK, κV]; idx := ["r", "m"]; arg := "a"
  argTy := .prod (.cap .rd (.var 1)) (.prod (buf (.rgn (.var 1)) SK c1 c1)
    (.prod (.intS c1) (.prod K (.prod (.code (.prod K K) bool .plain) .int))))
  retTy := .sum .int .int
  body := .split (v "a") "c" "a1" (.split (v "a1") "kb" "a2" (.split (v "a2") "cv" "a3"
    (.split (v "a3") "k" "a4" (.split (v "a4") "eq" "pos"
      (lets [("j", .rem (v "pos") (v "cv")), ("lk", .idx (v "kb") (v "j")), ("sk", .load true (v "lk"))]
        (.case (v "sk") "e0" (lets [("res", .inr .int (v "pos"))] (.ret (v "res")))
          "k2" (lets [("kk", .pair (v "k") (v "k2")), ("b", .callc (v "eq") (v "kk"))]
            (.case (v "b") "t1" (lets [("res", .inl .int (v "pos"))] (.ret (v "res")))
              "f1" (lets ([("p1", .add (v "pos") (.lit 1))] ++
                          tuple "q" [v "c", v "kb", v "cv", v "k", v "eq", v "p1"])
                (.tail "probe" ["r", "m"] (v "q0") [K, V]))))))))))

/-- Load the functions and the table, hash `k`, probe; `cont` sees `f0` (the
`(lim, full) × Fns` locative), `t0`, `m`, `cv`, `kb`, `vb` and `res`. -/
def withProbe (cont : Expr) : Expr :=
  lets [("f0", .fld 1 (v "p")), ("f1", .fld 1 (v "f0")), ("fs", .load true (v "f1"))]
    (.split (v "fs") "hash" "eq"
      (lets [("hv", .callc (v "hash") (v "k")), ("t0", .fld 0 (v "p")), ("tb", .load true (v "t0"))]
        (.unpack (v "tb") "m" "tt" (.split (v "tt") "cv" "bs" (.split (v "bs") "kb" "vb"
          (lets (tuple "q" [v "c", v "kb", v "cv", v "k", v "eq", v "hv"] ++
                 [("res", .call "probe" ["r", "m"] (v "q0") [K, V])]) cont))))))

/-! ## Operations -/

/-- `insert(k, v)`: the displaced value, or `inl ()`. -/
def insertD : Decl where
  name := "insert"; tparams := [κK, κV]; idx := ["r"]; arg := "a"
  argTy := .prod (.cap .bor (.var 0)) (.prod (MP (.var 0)) (.prod K V)); retTy := SV
  body := .split (v "a") "c" "a1" (.split (v "a1") "p" "a2" (.split (v "a2") "k" "val"
    (withProbe
      (.case (v "res")
        -- present: exchange the value
        "pf" (lets [("j", .rem (v "pf") (v "cv")), ("lv", .idx (v "vb") (v "j")),
                    ("nv", .inr .unit (v "val")), ("old", .xchg (v "lv") (v "nv"))] (.ret (v "old")))
        -- absent: a fresh key needs room
        "pe" (lets [("lc0", .fld 0 (v "f0")), ("lc", .fld 0 (v "lc0")), ("lp", .load true (v "lc"))]
          (.unpack (v "lp") "l" "lv0"
            (.ifeq (v "lv0") (.lit 0)
              (lets ([("g0", .pair (v "c") (v "p")), ("u", .call "grow" ["r"] (v "g0") [K, V])] ++
                     tuple "w" [v "c", v "p", v "k", v "val"])
                (.tail "insert" ["r"] (v "w0") [K, V]))
              (lets [("l1", .sub (v "lv0") (.lit 1)), ("ln", .nameI (v "l1")),
                     ("lk", .pack (v "ln") "ln" LimT), ("u1", .store true (v "lc") (v "lk") none),
                     ("j", .rem (v "pe") (v "cv")), ("kl", .idx (v "kb") (v "j")),
                     ("nk", .inr .unit (v "k")), ("u2", .store true (v "kl") (v "nk") none),
                     ("vl", .idx (v "vb") (v "j")), ("nv", .inr .unit (v "val")),
                     ("old", .xchg (v "vl") (v "nv"))] (.ret (v "old"))))))))))

/-- `take(k)`: remove and return the value; the key stays as a tombstone. -/
def takeD : Decl where
  name := "take"; tparams := [κK, κV]; idx := ["r"]; arg := "a"
  argTy := .prod (.cap .bor (.var 0)) (.prod (MP (.var 0)) K); retTy := SV
  body := .split (v "a") "c" "a1" (.split (v "a1") "p" "k"
    (withProbe
      (.case (v "res")
        "pf" (lets [("j", .rem (v "pf") (v "cv")), ("lv", .idx (v "vb") (v "j")),
                    ("e", .inl V .unit), ("old", .xchg (v "lv") (v "e"))] (.ret (v "old")))
        "pe" (lets [("e", .inl V .unit)] (.ret (v "e"))))))

/-- `lookup(k)`: a copy of the value.  Only `rd`, and `V : copy`. -/
def lookupD : Decl where
  name := "lookup"; tparams := [κK, κVc]; idx := ["r"]; arg := "a"
  argTy := .prod (.cap .rd (.var 0)) (.prod (MP (.var 0)) K); retTy := SV
  body := .split (v "a") "c" "a1" (.split (v "a1") "p" "k"
    (withProbe
      (.case (v "res")
        "pf" (lets [("j", .rem (v "pf") (v "cv")), ("lv", .idx (v "vb") (v "j")),
                    ("sv", .load true (v "lv"))] (.ret (v "sv")))
        "pe" (lets [("e", .inl V .unit)] (.ret (v "e"))))))

/-! ## Resizing

`grow` doubles the capacity: it installs a fresh table (`lim := full`,
`full := 2·full`), then `rehash` walks the old columns — still region memory —
moving each live entry out with `xchg` and in with `insert`. -/

def growD : Decl where
  name := "grow"; tparams := [κK, κV]; idx := ["r"]; arg := "a"
  argTy := .prod (.cap .bor (.var 0)) (MP (.var 0)); retTy := .unit
  body := .split (v "a") "c" "p"
    (lets [("t0", .fld 0 (v "p")), ("tb", .load true (v "t0"))]
      (.unpack (v "tb") "m" "tt" (.split (v "tt") "cv" "bs" (.split (v "bs") "kb" "vb"
        -- the index scope at the `pack`: `i0n, z, m, r`, so `r` is `var 3`
        (lets ([("nc", .add (v "cv") (v "cv")), ("nm", .sub (v "nc") (.lit 1)), ("z", .nameI (v "nm")),
                ("c2", .add (v "z") (.lit 1))] ++ newTableR "r" (.var 3) "z" "c2" "ntb" ++
               [("u1", .store true (v "t0") (v "ntb") none),
                ("f0", .fld 1 (v "p")), ("lc0", .fld 0 (v "f0")), ("fl", .fld 1 (v "lc0")),
                ("fp", .load true (v "fl"))])
          (.unpack (v "fp") "f" "fv"
            (lets ([("nl", .pack (v "fv") "f" LimT), ("f2", .add (v "fv") (v "fv")), ("fn", .nameI (v "f2")),
                    ("nf", .pack (v "fn") "fn" LimT), ("lim", .pair (v "nl") (v "nf")),
                    ("u2", .store true (v "lc0") (v "lim") none),
                    ("i0", .nameI (.lit 0)), ("mv", .sub (v "cv") (.lit 1))] ++
                   tuple "r" [v "c", v "p", v "kb", v "vb", v "i0", v "mv"] ++
                   [("u3", .call "rehash" ["r", "i0", "m"] (v "r0") [K, V])])
              (.ret .unit))))))))

def rehashD : Decl :=
  let n : Idx := .add (.add (.var 1) (.lit 1)) (.var 0)
  let next : Expr :=
    .ifeq (v "dv") (.lit 0) (.ret .unit)
      (lets ([("d1", .sub (v "dv") (.lit 1)), ("un", .nameI (v "d1")),
              ("i1", .add (v "iv") (.lit 1)), ("jn", .nameI (v "i1"))] ++
             tuple "n" [v "c", v "p", v "kb", v "vb", v "jn", v "un"])
        (.tail "rehash" ["r", "jn", "un"] (v "n0") [K, V]))
  { name := "rehash", tparams := [κK, κV], idx := ["r", "i", "d"], arg := "a"
    argTy := .prod (.cap .bor (.var 2)) (.prod (MP (.var 2)) (.prod (buf (.rgn (.var 2)) SK n n)
      (.prod (buf (.rgn (.var 2)) SV n n) (.prod (.intS (.var 1)) (.intS (.var 0))))))
    retTy := .unit
    body := .split (v "a") "c" "a1" (.split (v "a1") "p" "a2" (.split (v "a2") "kb" "a3"
      (.split (v "a3") "vb" "a4" (.split (v "a4") "iv" "dv"
        (lets [("lk", .idx (v "kb") (v "iv")), ("sk", .load true (v "lk"))]
          (.case (v "sk") "e0" next
            "k" (lets [("vl", .idx (v "vb") (v "iv")), ("e1", .inl V .unit), ("sv", .xchg (v "vl") (v "e1"))]
              (.case (v "sv") "e2" next
                "val" (lets (tuple "w" [v "c", v "p", v "k", v "val"] ++
                             [("u", .call "insert" ["r"] (v "w0") [K, V])]) next))))))))) }

def hmLib : Prog := [fillD, newD, probeD, insertD, takeD, lookupD, growD, rehashD]

#guard accepts (checkProg hmLib)

/-! ## An instance: `∃n. Int(n)` keys, `Int` values

A key must be compared, and `ifeq` compares only integers of known index, so a
key is `∃n. Int(n)`: one word, copyable; its column is `wide` (tag + word). -/

def KI : Ty := .iex (.intS (.var 0))

def dcl (name : String) (argTy retTy : Ty) (body : Expr) (idx : List String := []) : Decl :=
  { name := name, idx := idx, arg := "a", argTy := argTy, retTy := retTy, body := body }

def hashKID : Decl := dcl "hashKI" KI .int (.unpack (v "a") "n" "x" (.ret (v "x")))
def eqKID : Decl := dcl "eqKI" (.prod KI KI) bool
  (.split (v "a") "x" "y" (.unpack (v "x") "i" "xi" (.unpack (v "y") "j" "yj"
    (.ifeq (v "xi") (v "yj") (lets [("t", .inl .unit .unit)] (.ret (v "t")))
      (lets [("f", .inr .unit .unit)] (.ret (v "f")))))))
def unwD : Decl := dcl "unw" (.sum .unit .int) .int (.case (v "a") "e" (.ret (.lit 0)) "x" (.ret (v "x")))

def keyOps (tag : String) (n : Nat) : List (String × Op) :=
  [(tag ++ "i", .nameI (.lit n)), (tag ++ "k", .pack (v (tag ++ "i")) (tag ++ "i") KI)]
def insOps (tag : String) (n val : Nat) : List (String × Op) :=
  keyOps tag n ++ tuple (tag ++ "q") [v "c", v "d", v (tag ++ "k"), .lit val] ++
  [(tag ++ "r", .call "insert" ["r"] (v (tag ++ "q0")) [KI, .int])]
def getOps (f tag : String) (n : Nat) : List (String × Op) :=
  keyOps tag n ++ tuple (tag ++ "q") [v "c", v "d", v (tag ++ "k")] ++
  [(tag ++ "s", .call f ["r"] (v (tag ++ "q0")) [KI, .int]), (tag, .call "unw" [] (v (tag ++ "s")))]

def fnsOps : List (String × Op) :=
  [("h", .fnptr "hashKI"), ("e", .fnptr "eqKI"), ("fs", .pair (v "h") (v "e"))]

/-- A private map (the thread keeps the token): `9` collides with `1`, `2`
then probes past `9`, `1` is overwritten, and the fifth fresh key (`5`) grows
the table to 16. -/
def ownUseD : Decl where
  name := "ownUse"; idx := []; arg := "a"; argTy := .unit
  retTy := .prod .int (.prod .int (.prod .int (.prod .int (.prod .int .int))))
  body := lets (fnsOps ++ [("p", .call "hmNew" [] (v "fs") [KI, .int])])
    (.unpack (v "p") "r" "g" (.split (v "g") "d" "t"
      (lets ([("c", .borrow .bor (v "t"))] ++ insOps "A" 1 10 ++ insOps "B" 9 90 ++ insOps "C" 2 20 ++
             insOps "D" 1 30 ++ insOps "E" 3 33 ++ insOps "F" 5 50 ++
             getOps "lookup" "L1" 1 ++ getOps "lookup" "L9" 9 ++ getOps "take" "T2" 2 ++
             getOps "lookup" "L2" 2 ++ getOps "lookup" "L5" 5 ++ getOps "lookup" "L3" 3 ++
             tuple "o" [v "L1", v "L9", v "T2", v "L2", v "L5", v "L3"])
        (.ret (v "o0")))))

def instLib : Prog := hmLib ++ [hashKID, eqKID, unwD, ownUseD]

#guard accepts (checkProg instLib)

/-! ## Hazards, each refused for its reason -/

-- `lookup` copies a value out, so an affine `V` is refused at the instance.
#guard rejects (checkDecl instLib { ownUseD with
    body := lets [("x", .call "lookup" ["r"] .unit [KI, .tok (.lit 0) none])] (.ret .unit),
    retTy := .unit }) "a type argument does not have its parameter's kind"
-- … but `insert` and `take` take any `noOwn, noWord` value, affine included: the
-- library was checked once at `V : noOwn, noWord`, and `hmNew` at a token type is
-- accepted …
#guard accepts (checkDecl instLib { ownUseD with
    body := lets ([("h", .fnptr "hashKI"), ("e", .fnptr "eqKI"), ("fs", .pair (v "h") (v "e")),
                   ("p", .call "hmNew" [] (v "fs") [KI, .tok (.lit 0) none])]) (.ret .unit),
    retTy := .unit })
-- … and at a protocol word refused: `insert` would write it by a plain exchange.
#guard rejects (checkDecl instLib { ownUseD with
    body := lets ([("h", .fnptr "hashKI"), ("e", .fnptr "eqKI"), ("fs", .pair (v "h") (v "e")),
                   ("p", .call "hmNew" [] (v "fs") [KI, .word (.lit 0) CoreLang.seqP])]) (.ret .unit),
    retTy := .unit }) "a type argument does not have its parameter's kind"
-- An `own` value type is refused: a region cell holds no `own` reference (D1).
#guard rejects (checkDecl instLib { ownUseD with
    body := lets (fnsOps ++ [("p", .call "hmNew" [] (v "fs") [KI, .ptr .own .int])]) (.ret .unit),
    retTy := .unit }) "a type argument does not have its parameter's kind"
-- `xchg` at a type variable that may be `own`: refused (F2).  (`noWord`, so the
-- word-free check passes and the `own` one is what refuses.)
def xTop : Decl where
  name := "x"; tparams := [{ noWord := true }]; idx := ["r"]; arg := "a"
  argTy := .prod (.cap .bor (.var 0)) (.prod (.ptr (.rgn (.var 0)) (.tvar 0)) (.tvar 0)); retTy := .tvar 0
  body := .split (v "a") "c" "a1" (.split (v "a1") "p" "x"
    (lets [("o", .xchg (v "p") (v "x"))] (.ret (v "o"))))
#guard rejects (checkDecl [] xTop) "a type variable that may be own"
-- `insert` under `rd`: a read share does not write.
def badIns : Decl where
  name := "bad"; tparams := [κK, κVc]; idx := ["r"]; arg := "a"
  argTy := lookupD.argTy; retTy := SV
  body := .split (v "a") "c" "a1" (.split (v "a1") "p" "k"
      (lets [("e", .inl V .unit)] (lets (tuple "w" [v "c", v "p", v "k", v "e"] ++
        [("u", .call "insert" ["r"] (v "w0") [K, V])]) (.ret (v "e")))))
#guard rejects (checkDecl hmLib badIns) "call insert: argument type mismatch"
-- A slot index that was not reduced: `idx` needs `j < n`.
#guard rejects (checkDecl hmLib { lookupD with
    body := .split (v "a") "c" "a1" (.split (v "a1") "p" "k"
      (withProbe (.case (v "res")
        "pf" (lets [("lv", .idx (v "vb") (v "pf")), ("sv", .load true (v "lv"))] (.ret (v "sv")))
        "pe" (lets [("e", .inl V .unit)] (.ret (v "e")))))) })
  "expected an integer of known index"
-- Two reductions by the same modulus in one block: the second has no free `m`.
#guard rejects (checkDecl hmLib { lookupD with
    body := .split (v "a") "c" "a1" (.split (v "a1") "p" "k"
      (withProbe (.case (v "res")
        "pf" (lets [("j", .rem (v "pf") (v "cv")), ("j2", .rem (v "pf") (v "cv")),
                    ("lv", .idx (v "vb") (v "j")), ("sv", .load true (v "lv"))] (.ret (v "sv")))
        "pe" (lets [("e", .inl V .unit)] (.ret (v "e")))))) })
  "rem: the modulus must be v + 1"
-- `xchg` on published memory: two racing exchanges would duplicate.
#guard rejects (checkDecl [] (dcl "xp" (.ptr .pub .int) .int
    (lets [("o", .xchg (v "a") (.lit 1))] (.ret (v "o"))))) "xchg on published memory"
-- … and under a `pub` capability (published memory opened as a region).
#guard rejects (checkDecl [] (dcl "xo" (.ptr .pub .int) .int
    (.openPub (v "a") "r" "q" "cp" (lets [("o", .xchg (v "q") (.lit 1))] (.ret (v "o"))))))
  "needs its sealed token or a bor capability"
-- `fnptr` of a polymorphic block: a word cannot carry type arguments.
#guard rejects (checkDecl instLib (dcl "fp" .unit .unit
    (lets [("f", .fnptr "insert")] (.ret .unit)))) "only a monomorphic code block"

/-! ## On the promise machine -/

def oSetup : Option Setup := runSetup instLib "unw" [] (.sum .unit .int) [cst (.num 0), cst (.num 0)]
#guard oSetup.isSome

-- One thread, the own map: the collisions, the overwrite, the resize, `take`.
#guard let r := runE instLib oSetup (fun _ => [("ownUse", [], .unit, [])]) 0 4000
  clean r && resultsOf r 0 == [[.num 30, .num 90, .num 20, .num 0, .num 50, .num 33]]

/-! ## A plain-`Int` instance

`ifeq` on plain integers learns nothing, but it decides: that is all a key
comparison needs, so keys can be plain `Int` rather than `∃n. Int(n)`. -/

def hashIntD : Decl := dcl "hashInt" .int .int (.ret (v "a"))
def eqIntD : Decl := dcl "eqInt" (.prod .int .int) bool
  (.split (v "a") "x" "y"
    (.ifeq (v "x") (v "y") (lets [("t", .inl .unit .unit)] (.ret (v "t")))
      (lets [("f", .inr .unit .unit)] (.ret (v "f")))))

def insI (tag : String) (n val : Nat) : List (String × Op) :=
  tuple (tag ++ "q") [v "c", v "d", .lit n, .lit val] ++
  [(tag ++ "r", .call "insert" ["r"] (v (tag ++ "q0")) [.int, .int])]
def getI (f tag : String) (n : Nat) : List (String × Op) :=
  tuple (tag ++ "q") [v "c", v "d", .lit n] ++
  [(tag ++ "s", .call f ["r"] (v (tag ++ "q0")) [.int, .int]), (tag, .call "unw" [] (v (tag ++ "s")))]

/-- `ownUse` again, with `Int` keys. -/
def intUseD : Decl where
  name := "intUse"; idx := []; arg := "a"; argTy := .unit
  retTy := ownUseD.retTy
  body := lets [("h", .fnptr "hashInt"), ("e", .fnptr "eqInt"), ("fs", .pair (v "h") (v "e")),
                ("p", .call "hmNew" [] (v "fs") [.int, .int])]
    (.unpack (v "p") "r" "g" (.split (v "g") "d" "t"
      (lets ([("c", .borrow .bor (v "t"))] ++ insI "A" 1 10 ++ insI "B" 9 90 ++ insI "C" 2 20 ++
             insI "D" 1 30 ++ insI "E" 3 33 ++ insI "F" 5 50 ++
             getI "lookup" "L1" 1 ++ getI "lookup" "L9" 9 ++ getI "take" "T2" 2 ++
             getI "lookup" "L2" 2 ++ getI "lookup" "L5" 5 ++ getI "lookup" "L3" 3 ++
             tuple "o" [v "L1", v "L9", v "T2", v "L2", v "L5", v "L3"])
        (.ret (v "o0")))))

def intLib : Prog := hmLib ++ [hashIntD, eqIntD, unwD, intUseD]

#guard accepts (checkProg intLib)

-- A plain comparison teaches nothing: after `x = 3` succeeds, `x` still has no index.
#guard rejects (checkDecl [] (dcl "pl" .int .int
  (lets [("b", .newBuf (.lit 4) .int)]
    (.ifeq (v "a") (.lit 3) (lets [("l", .idx (v "b") (v "a")), ("x", .load false (v "l"))] (.ret (v "x")))
      (.ret (.lit 0))))))
  "expected an integer of known index"

def iSetup : Option Setup := runSetup intLib "unw" [] (.sum .unit .int) [cst (.num 0), cst (.num 0)]
#guard iSetup.isSome

#guard let r := runE intLib iSetup (fun _ => [("intUse", [], .unit, [])]) 0 4000
  clean r && resultsOf r 0 == [[.num 30, .num 90, .num 20, .num 0, .num 50, .num 33]]

/-! ## The readers–writer map

The same library behind the readers–writer lock (RWLock.lean): the writer lends
its token as `bor` to `insert`, a reader lends its share as `rd` to `lookup`.
The lock's code is monomorphic in its payload, so it is instantiated here at
the map's concrete type. -/

/-- The map at `KI`, `Int`, in region `r`. -/
def MapKI (r : Idx) : Ty := substTs [.int, KI] 0 0 (MapTR r)

/-- `Ptr pub (Word[r, P] × Ptr r τ)` for a `τ` that itself names `r` (the
innermost index): `cell` without its shift. -/
def cellR (P : Proto) (τ : Ty) : Ty := .ptr .pub (.prod (.word (.var 0) P) (.ptr (.rgn (.var 0)) τ))

def lockFor (τ : Ty) : Prog :=
  [{ RWLock.readLockD true 2 with argTy := cellR RWLock.rwP τ },
   { RWLock.readUnlockD true 2 with argTy := .prod (cellR RWLock.rwP τ) (.share (.var 0)) },
   { RWLock.writeLockD with argTy := cellR RWLock.rwP τ },
   { RWLock.writeUnlockD with argTy := .prod (cellR RWLock.rwP τ) (.tok (.var 0) (some (RWLock.rwP, .lit 1))) }]

/-- `∃r. Ptr pub (Word[r, rw] × Ptr r (Map r KI Int))`: the lock's word guards
the region the map was born in. -/
def GM : Ty := .iex (cellR RWLock.rwP (MapKI (.var 0)))

def mkMapRWD : Decl := dcl "mkMapRW" .unit GM
  (lets (fnsOps ++ [("p", .call "hmNew" [] (v "fs") [KI, .int])])
    (.unpack (v "p") "r" "g" (.split (v "g") "d" "t0"
      (lets [("wv", .mkWord "r" RWLock.rwP (.lit 0) (v "t0")), ("pr", .pair (v "wv") (v "d")),
             ("s", .new (v "pr") (some (.prod (.word (.var 0) RWLock.rwP) (.ptr (.rgn (.var 0)) (MapKI (.var 0)))))), ("s2", .publish (v "s")), ("mx", .pack (v "s2") "r" GM)]
        (.ret (v "mx"))))))

/-- Writer: `insert k ↦ val` under the lock; the displaced value, unwrapped. -/
def rwPutD (name : String) (k val : Nat) : Decl := dcl name GM .int
  (.unpack (v "a") "r" "m"
    (lets (keyOps "K" k ++
           [("t", .call "writeLock" ["r"] (v "m")), ("d0", .fld 1 (v "m")), ("d", .load false (v "d0")),
            ("c", .borrow .bor (v "t"))] ++ tuple "w" [v "c", v "d", v "Kk", .lit val] ++
           [("o", .call "insert" ["r"] (v "w0") [KI, .int]), ("e", .endBorrow (v "t")),
            ("pp", .pair (v "m") (v "t")), ("u", .call "writeUnlock" ["r"] (v "pp")),
            ("x", .call "unw" [] (v "o"))])
      (.ret (v "x"))))

/-- Reader: `lookup k` under a share. -/
def rwGetD (name : String) (k : Nat) : Decl := dcl name GM .int
  (.unpack (v "a") "r" "m"
    (lets (keyOps "K" k ++
           [("sh", .call "readLock" ["r"] (v "m")), ("d0", .fld 1 (v "m")), ("d", .load false (v "d0")),
            ("c", .borrow .rd (v "sh"))] ++ tuple "w" [v "c", v "d", v "Kk"] ++
           [("o", .call "lookup" ["r"] (v "w0") [KI, .int]), ("e", .endBorrow (v "sh")),
            ("pp", .pair (v "m") (v "sh")), ("u", .call "readUnlock" ["r"] (v "pp")),
            ("x", .call "unw" [] (v "o"))])
      (.ret (v "x"))))

def rwProg : Prog := instLib ++ lockFor (MapKI (.var 0)) ++
  [mkMapRWD, rwPutD "w1" 1 10, rwPutD "w1b" 1 20, rwGetD "g1" 1]

#guard accepts (checkProg rwProg)

-- A reader that lends its share as `bor`, to write: refused.
#guard rejects (checkDecl rwProg { rwGetD "g1" 1 with
    body := .unpack (v "a") "r" "m" (lets [("sh", .call "readLock" ["r"] (v "m")),
      ("c", .borrow .bor (v "sh"))] (.ret (.lit 0))) }) "a read share lends only rd"

def rwSetup : Option Setup := runSetup rwProg "mkMapRW" [] .unit [] 600
#guard rwSetup.isSome

-- A writer and a reader: the reader sees the key absent (0) or present (10).
#guard let r := runE rwProg rwSetup (fun s => [("w1", [], GM, s.res), ("g1", [], GM, s.res)]) 0 3000
  clean r && resultsOf r 0 == [[.num 0]] && sameSet (resultsOf r 1) [[.num 0], [.num 10]]
-- Two writers of the same key: one displaces the other's value.
#guard let r := runE rwProg rwSetup (fun s => [("w1", [], GM, s.res), ("w1b", [], GM, s.res)]) 0 3000
  clean r && sameSet ((resultsOf r 0) ++ (resultsOf r 1)).eraseDups [[.num 0], [.num 10], [.num 20]]

end HashMap
