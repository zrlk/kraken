import WeakCore.HashMap

/-!
# HashMapOwn — the map by value, for any value type

HashMap.lean keeps its map behind a region pointer, so one library serves a
private map and a readers–writer map; the price is `V : noOwn` (a region cell
holds no `own` reference).  Here the map is a plain affine value,
threaded through each operation (`MapT → MapT × result`), and its columns are
own buffers throughout.  Slots are reached with the by-value primitives
`xchgAt b i v` and `loadAt b i`, which look at the buffer without making a
locative (`idx` on an own buffer uses it up: a locative is a second owner).
With no region there is no alias to fear, so `V` has the top kind: `Ptr own T`
goes in and comes back out owned.  `lookup` copies, so it asks `V : copy`.

Same layout, hash/equality, probing and resize policy as HashMap.lean.
-/

namespace HashMapOwn
open CoreLang CoreTerm TermRun TermSmoke HashMap

def κVo : Kind := {}
def κVoc : Kind := { copy := true }

def SKB : Ty := buf .own SK c1 c1

/-- Pack the table `(cv, kb, vb)` at `m`, then the map with `lf` and `fs`, as `mm0`. -/
def repack (kb vb lf : String) : List (String × Op) :=
  tuple "nt" [v "cv", v kb, v vb] ++ [("tb2", .pack (v "nt0") "m" Tbl)] ++
  tuple "mm" [v "tb2", v lf, v "fs"]

/-- `new(hash, eq)`: capacity 8, room for 4 fresh keys; the map itself. -/
def onewD : Decl where
  name := "onew"; tparams := [κK, κVo]; idx := []; arg := "a"
  argTy := Fns; retTy := MapT
  body := lets ([("z", .nameI (.lit 7)), ("c2", .add (v "z") (.lit 1))] ++ newTable "z" "c2" "tb" ++
      [("l4", .nameI (.lit 4)), ("lim", .pack (v "l4") "l4" LimT), ("full", .pack (v "l4") "l4" LimT),
       ("lf", .pair (v "lim") (v "full"))] ++ tuple "m" [v "tb", v "lf", v "a"])
    (.ret (v "m0"))

/-- As `probe`, but the key column is an own buffer, passed in and handed back. -/
def oprobeD : Decl where
  name := "oprobe"; tparams := [κK, κVo]; idx := ["m"]; arg := "a"
  argTy := .prod SKB (.prod (.intS c1) (.prod K (.prod (.code (.prod K K) HashMap.bool .plain) .int)))
  retTy := .prod SKB (.sum .int .int)
  body := .split (v "a") "kb" "a2" (.split (v "a2") "cv" "a3"
    (.split (v "a3") "k" "a4" (.split (v "a4") "eq" "pos"
      (lets [("j", .rem (v "pos") (v "cv")), ("sk", .loadAt (v "kb") (v "j"))]
        (.case (v "sk") "e0" (lets [("res", .inr .int (v "pos")), ("o", .pair (v "kb") (v "res"))] (.ret (v "o")))
          "k2" (lets [("kk", .pair (v "k") (v "k2")), ("b", .callc (v "eq") (v "kk"))]
            (.case (v "b") "t1" (lets [("res", .inl .int (v "pos")), ("o", .pair (v "kb") (v "res"))] (.ret (v "o")))
              "f1" (lets ([("p1", .add (v "pos") (.lit 1))] ++
                          tuple "q" [v "kb", v "cv", v "k", v "eq", v "p1"])
                (.tail "oprobe" ["m"] (v "q0") [K, V])))))))))

/-- Take the map `mp` apart, hash `k`, probe; `cont` sees `lf`, `fs`, `m`, `cv`,
`kb1` (the key column back from the probe), `vb` and `res`. -/
def withOProbe (cont : Expr) : Expr :=
  .split (v "mp") "tb" "rest" (.split (v "rest") "lf" "fs" (.split (v "fs") "hash" "eq"
    (lets [("hv", .callc (v "hash") (v "k"))]
      (.unpack (v "tb") "m" "tt" (.split (v "tt") "cv" "bs" (.split (v "bs") "kb" "vb"
        (lets (tuple "q" [v "kb", v "cv", v "k", v "eq", v "hv"] ++
               [("pr", .call "oprobe" ["m"] (v "q0") [K, V])])
          (.split (v "pr") "kb1" "res" cont))))))))

/-- The map back together with `lf'`, paired with the result `r`. -/
def done (lf r : String) : Expr :=
  lets (repack "kb1" "vb" lf ++ [("out", .pair (v "mm0") (v r))]) (.ret (v "out"))

/-- `insert(k, v)`: the map, and the displaced value or `inl ()`. -/
def oinsertD : Decl where
  name := "oinsert"; tparams := [κK, κVo]; idx := []; arg := "a"
  argTy := .prod MapT (.prod K V); retTy := .prod MapT SV
  body := .split (v "a") "mp" "kv" (.split (v "kv") "k" "val"
    (withOProbe
      (.case (v "res")
        -- present: exchange the value
        "pf" (lets [("j", .rem (v "pf") (v "cv")), ("nv", .inr .unit (v "val")),
                    ("old", .xchgAt (v "vb") (v "j") (v "nv"))] (done "lf" "old"))
        -- absent: a fresh key needs room
        "pe" (.split (v "lf") "lp" "fp" (.unpack (v "lp") "l" "lv0"
          (.ifeq (v "lv0") (.lit 0)
            (lets ([("lp2", .pack (v "lv0") "l" LimT), ("lf2", .pair (v "lp2") (v "fp"))] ++
                   repack "kb1" "vb" "lf2" ++
                   [("g", .call "ogrow" [] (v "mm0") [K, V])] ++ tuple "w" [v "g", v "k", v "val"])
              (.tail "oinsert" [] (v "w0") [K, V]))
            (lets [("l1", .sub (v "lv0") (.lit 1)), ("ln", .nameI (v "l1")),
                   ("lk", .pack (v "ln") "ln" LimT), ("lf2", .pair (v "lk") (v "fp")),
                   ("j", .rem (v "pe") (v "cv")),
                   ("nk", .inr .unit (v "k")), ("u2", .xchgAt (v "kb1") (v "j") (v "nk")),
                   ("nv", .inr .unit (v "val")), ("old", .xchgAt (v "vb") (v "j") (v "nv"))]
              (done "lf2" "old"))))))))

/-- `take(k)`: remove and return the value; the key stays as a tombstone. -/
def otakeD : Decl where
  name := "otake"; tparams := [κK, κVo]; idx := []; arg := "a"
  argTy := .prod MapT K; retTy := .prod MapT SV
  body := .split (v "a") "mp" "k"
    (withOProbe
      (.case (v "res")
        "pf" (lets [("j", .rem (v "pf") (v "cv")), ("e", .inl V .unit),
                    ("old", .xchgAt (v "vb") (v "j") (v "e"))] (done "lf" "old"))
        "pe" (lets [("e", .inl V .unit)] (done "lf" "e"))))

/-- `lookup(k)`: a copy of the value; `V : copy`. -/
def olookupD : Decl where
  name := "olookup"; tparams := [κK, κVoc]; idx := []; arg := "a"
  argTy := .prod MapT K; retTy := .prod MapT SV
  body := .split (v "a") "mp" "k"
    (withOProbe
      (.case (v "res")
        "pf" (lets [("j", .rem (v "pf") (v "cv")), ("sv", .loadAt (v "vb") (v "j"))] (done "lf" "sv"))
        "pe" (lets [("e", .inl V .unit)] (done "lf" "e"))))

/-! ## Resizing: a fresh map, then every live entry moved across by value -/

def ogrowD : Decl where
  name := "ogrow"; tparams := [κK, κVo]; idx := []; arg := "a"
  argTy := MapT; retTy := MapT
  body := .split (v "a") "tb" "rest" (.split (v "rest") "lf" "fs"
    (.unpack (v "tb") "m" "tt" (.split (v "tt") "cv" "bs" (.split (v "bs") "kb" "vb"
      (lets ([("nc", .add (v "cv") (v "cv")), ("nm", .sub (v "nc") (.lit 1)), ("z", .nameI (v "nm")),
              ("c2", .add (v "z") (.lit 1))] ++ newTable "z" "c2" "ntb")
        (.split (v "lf") "lp" "fp" (.unpack (v "fp") "f" "fv"
          (lets ([("nl", .pack (v "fv") "f" LimT), ("f2", .add (v "fv") (v "fv")), ("fn", .nameI (v "f2")),
                  ("nf", .pack (v "fn") "fn" LimT), ("lf2", .pair (v "nl") (v "nf"))] ++
                 tuple "mm" [v "ntb", v "lf2", v "fs"] ++
                 [("i0", .nameI (.lit 0)), ("mv", .sub (v "cv") (.lit 1))] ++
                 tuple "r" [v "mm0", v "kb", v "vb", v "i0", v "mv"] ++
                 [("res", .call "orehash" ["i0", "m"] (v "r0") [K, V])])
            (.ret (v "res"))))))))))

def orehashD : Decl :=
  let n : Idx := .add (.add (.var 1) (.lit 1)) (.var 0)
  let next (mp : String) : Expr :=
    .ifeq (v "dv") (.lit 0) (.ret (v mp))
      (lets ([("d1", .sub (v "dv") (.lit 1)), ("un", .nameI (v "d1")),
              ("i1", .add (v "iv") (.lit 1)), ("jn", .nameI (v "i1"))] ++
             tuple "n" [v mp, v "kb", v "vb", v "jn", v "un"])
        (.tail "orehash" ["jn", "un"] (v "n0") [K, V]))
  { name := "orehash", tparams := [κK, κVo], idx := ["i", "d"], arg := "a"
    argTy := .prod MapT (.prod (buf .own SK n n) (.prod (buf .own SV n n) (.prod (.intS (.var 1)) (.intS (.var 0)))))
    retTy := MapT
    body := .split (v "a") "mp" "a2" (.split (v "a2") "kb" "a3"
      (.split (v "a3") "vb" "a4" (.split (v "a4") "iv" "dv"
        (lets [("sk", .loadAt (v "kb") (v "iv"))]
          (.case (v "sk") "e0" (next "mp")
            "k" (lets [("e1", .inl V .unit), ("sv", .xchgAt (v "vb") (v "iv") (v "e1"))]
              (.case (v "sv") "e2" (next "mp")
                "val" (lets (tuple "w" [v "mp", v "k", v "val"] ++
                             [("ins", .call "oinsert" [] (v "w0") [K, V])])
                  (.split (v "ins") "mp2" "old" (next "mp2")))))))))) }

def ohmLib : Prog := [fillD, onewD, oprobeD, oinsertD, otakeD, olookupD, ogrowD, orehashD]

#guard accepts (checkProg ohmLib)

/-! ## An instance: `∃n. Int(n)` keys, owned boxes `Ptr own Int` as values

HashMap.lean refuses this `V` by kind (`noOwn`).  Here a box goes in, and the
same box comes back out on overwrite or `take`, still owned. -/

def PI : Ty := .ptr .own .int
def idID : Decl := dcl "idI" .int .int (.ret (v "a"))
/-- Unwrap a displaced box: its contents, or `0` for `inl ()`. -/
def unbD : Decl := dcl "unb" (.sum .unit PI) .int
  (.case (v "a") "e" (.ret (.lit 0)) "p" (lets [("x", .load false (v "p"))] (.ret (v "x"))))

/-- One map operation: `call f (mIn, arg)`, split into the next map `tag ++ "m"`
and the result, unwrapped as `tag`. -/
def oStep (f mIn tag : String) (argOps : List (String × Op)) (arg : At) (k : Expr) : Expr :=
  lets (argOps ++ [(tag ++ "w", .pair (v mIn) arg), (tag ++ "r", .call f [] (v (tag ++ "w")) [KI, PI])])
    (.split (v (tag ++ "r")) (tag ++ "m") (tag ++ "o")
      (lets [(tag, .call "unb" [] (v (tag ++ "o")))] k))

def oIns (mIn tag : String) (n val : Nat) (k : Expr) : Expr :=
  oStep "oinsert" mIn tag (keyOps tag n ++ [(tag ++ "x", .call "idI" [] (.lit val)),
    (tag ++ "b", .new (v (tag ++ "x")) (some .int)), (tag ++ "kv", .pair (v (tag ++ "k")) (v (tag ++ "b")))])
    (v (tag ++ "kv")) k
def oTake (mIn tag : String) (n : Nat) (k : Expr) : Expr :=
  oStep "otake" mIn tag (keyOps tag n) (v (tag ++ "k")) k

/-- `9` collides with `1`; re-inserting `1` gives back the box of `10`; `5` is
the fifth fresh key and grows the table; then the boxes come back out by `take`. -/
def ownValD : Decl where
  name := "ownVal"; idx := []; arg := "a"; argTy := .unit
  retTy := .prod .int (.prod .int (.prod .int (.prod .int (.prod .int .int))))
  body := lets (fnsOps ++ [("m", .call "onew" [] (v "fs") [KI, PI])])
    (oIns "m" "A" 1 10 <| oIns "Am" "B" 9 90 <| oIns "Bm" "C" 2 20 <| oIns "Cm" "D" 1 30 <|
     oIns "Dm" "E" 3 33 <| oIns "Em" "F" 5 50 <|
     oTake "Fm" "T1" 1 <| oTake "T1m" "T9" 9 <| oTake "T9m" "T5" 5 <| oTake "T5m" "T2" 2 <|
     oTake "T2m" "U2" 2 <|
     lets (tuple "o" [v "D", v "T1", v "T9", v "T5", v "T2", v "U2"]) (.ret (v "o0")))

def oInstLib : Prog := ohmLib ++ [hashKID, eqKID, idID, unbD, ownValD]

#guard accepts (checkProg oInstLib)

/-! ## Hazards -/

-- `lookup` copies, so an owned box is refused by kind.
#guard rejects (checkDecl oInstLib { ownValD with
    body := lets (fnsOps ++ [("m", .call "onew" [] (v "fs") [KI, PI]), ("k", .nameI (.lit 1)),
      ("kk", .pack (v "k") "k" KI), ("w", .pair (v "m") (v "kk")),
      ("x", .call "olookup" [] (v "w") [KI, PI])]) (.ret .unit), retTy := .unit })
  "a type argument does not have its parameter's kind"
-- The map is affine: using it twice is refused.
#guard rejects (checkDecl oInstLib { ownValD with
    body := lets (fnsOps ++ [("m", .call "onew" [] (v "fs") [KI, PI]), ("k", .nameI (.lit 1)),
      ("kk", .pack (v "k") "k" KI), ("w", .pair (v "m") (v "kk")), ("w2", .pair (v "m") (v "kk"))])
      (.ret .unit), retTy := .unit })
  "already used"

/-- A two-slot own buffer of a Zeroable `τ`, born initialised, bound to `b3`. -/
def bufOps (τ : Ty) : List (String × Op) := [("b3", .newBuf (.lit 2) τ)]
/-- A fresh box of `5`, bound to `q`. -/
def boxOps : List (String × Op) := [("y", .call "idI" [] (.lit 5)), ("q", .new (v "y") (some .int))]

-- Two exchanges on one own buffer: accepted (the buffer is only looked at) …
#guard accepts (checkDecl [] (dcl "xx" PI PI
  (lets (bufOps (.sum .unit .int) ++ [("e", .inl .int .unit),
          ("x1", .xchgAt (v "b3") (.lit 0) (v "e")), ("x2", .xchgAt (v "b3") (.lit 1) (v "e"))])
    (.ret (v "a")))))
-- … while `idx` on an own buffer uses it up.
#guard rejects (checkDecl [] (dcl "ii" .unit .int
  (lets (bufOps .int ++ [("l1", .idx (v "b3") (.lit 0)), ("l2", .idx (v "b3") (.lit 1))])
    (.ret (.lit 0))))) "already used"
-- `loadAt` of an affine element would duplicate it.
#guard rejects (checkDecl [idID] (dcl "la" PI PI
  (lets [("b0", .newBuf (.lit 1) PI), ("b1", .bufInit (v "b0") (.lit 0) (v "a")),
         ("x", .loadAt (v "b1") (.lit 0))] (.ret (v "x"))))) "loadAt would duplicate"
-- … but `xchgAt` moves it out, putting another in.
#guard accepts (checkDecl [idID] (dcl "xa" PI PI
  (lets ([("b0", .newBuf (.lit 1) PI), ("b1", .bufInit (v "b0") (.lit 0) (v "a"))] ++ boxOps ++
         [("x", .xchgAt (v "b1") (.lit 0) (v "q"))]) (.ret (v "x")))))
-- An uninitialised slot (a box buffer is born empty), and a slot past the capacity.
#guard rejects (checkDecl [idID] (dcl "un" PI PI
  (lets ([("b0", .newBuf (.lit 2) PI), ("b1", .bufInit (v "b0") (.lit 0) (v "a"))] ++ boxOps ++
         [("x", .xchgAt (v "b1") (.lit 1) (v "q"))]) (.ret (v "x")))))
  "xchgAt: the slot is not provably initialised"
#guard rejects (checkDecl [] (dcl "oc" .unit .int
  (lets (bufOps .int ++ [("x", .loadAt (v "b3") (.lit 2))]) (.ret (v "x")))))
  "loadAt: the index is not provably below the capacity"

-- A published buffer: by-value access is for own buffers only.
#guard rejects (checkDecl [] (dcl "pb" .unit .int
  (lets (bufOps .int ++ [("p", .publish (v "b3")), ("x", .loadAt (v "p") (.lit 0))]) (.ret (v "x")))))
  "loadAt works on own buffers"

/-! ## On the promise machine -/

def ooSetup : Option Setup := runSetup oInstLib "idI" [] .int [cst (.num 0)]
#guard ooSetup.isSome

#guard let r := runE oInstLib ooSetup (fun _ => [("ownVal", [], .unit, [])]) 0 6000
  clean r && resultsOf r 0 == [[.num 10, .num 30, .num 90, .num 50, .num 20, .num 0]]

end HashMapOwn
