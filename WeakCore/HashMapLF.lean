import WeakCore.HashMap

/-!
# HashMapLF — the lock-free variant

A separate development, because every trade-off differs from the locked map.

* **Fixed capacity, keys never removed.**  Resizing a lock-free table needs
  cooperative migration; this one does not grow.  `put` answers `false` when a
  full probe finds no slot.
* **Boxed cells.**  The only atomic read-modify-write is a one-word `cas`
  (§3.5), and a reader may race any writer, so a slot must be read and written
  whole in one word: `keys : Buf pub (Ptr? pub K)`, `vals : Buf pub (Ptr? pub V)`.
  A key is claimed by `cas null → box`; a value is published with `rel` and
  read with `acq`.  `Ptr? pub _` is Zeroable for *every* target, so the columns
  are born empty, with no fill loop even generically.
* **Kinds.**  Published, so `K`, `V : share, noOwn`; `K : copy` (a probe loads
  the key to compare it); `get` needs `V : copy`.
* **Deletion** stores `null` into the value cell; the key stays (a tombstone).
* **Linearisation.**  A key claimed but not yet valued reads as absent: the
  `put` has not taken effect until its value store.
-/

namespace HashMapLF
open CoreLang CoreTerm TermRun TermSmoke HashMap

def κKL : Kind := { copy := true, share := true, noOwn := true }
def κVL : Kind := { share := true, noOwn := true }
def κVLc : Kind := { copy := true, share := true, noOwn := true }

def PK : Ty := .ptrOpt .pub K
def PV : Ty := .ptrOpt .pub V
def TblL : Ty := .iex (.prod (.intS c1) (.prod (buf .pub PK c1 c1) (buf .pub PV c1 c1)))
def LMap : Ty := .prod TblL Fns

/-- `new(hash, eq)`: capacity 8, both columns born `null` and published. -/
def lfNewD : Decl where
  name := "lfNew"; tparams := [κKL, κVL]; idx := []; arg := "a"; argTy := Fns; retTy := LMap
  body := lets ([("z", .nameI (.lit 7)), ("c2", .add (v "z") (.lit 1)),
                 ("kb", .newBuf (v "c2") PK), ("kp", .publish (v "kb")),
                 ("vb", .newBuf (v "c2") PV), ("vp", .publish (v "vb"))] ++
                tuple "t" [v "c2", v "kp", v "vp"] ++
                [("tb", .pack (v "t0") "z" TblL), ("m", .pair (v "tb") (v "a"))])
    (.ret (v "m"))

/-- Walk from `pos` with `l` slots left: `inl pos` (found `k`), `inr (inl pos)`
(an empty slot), `inr (inr ())` (full). -/
def lfProbeD : Decl where
  name := "lfProbe"; tparams := [κKL, κVL]; idx := ["m", "l"]; arg := "a"
  argTy := .prod (buf .pub PK (.add (.var 1) (.lit 1)) (.add (.var 1) (.lit 1)))
    (.prod (.intS (.add (.var 1) (.lit 1))) (.prod K (.prod (.code (.prod K K) HashMap.bool)
      (.prod .int (.intS (.var 0))))))
  retTy := .sum .int (.sum .int .unit)
  body := .split (v "a") "kb" "a1" (.split (v "a1") "cv" "a2" (.split (v "a2") "k" "a3"
    (.split (v "a3") "eq" "a4" (.split (v "a4") "pos" "lv"
      (.ifeq (v "lv") (.lit 0)
        (lets [("u", .inr .int .unit), ("res", .inr .int (v "u"))] (.ret (v "res")))
        (lets [("j", .rem (v "pos") (v "cv")), ("kl", .idx (v "kb") (v "j")), ("kc", .load true (v "kl"))]
          (.ifnull (v "kc")
            (lets [("u", .inl .unit (v "pos")), ("res", .inr .int (v "u"))] (.ret (v "res")))
            "kp" (lets [("k2", .load true (v "kp")), ("kk", .pair (v "k") (v "k2")), ("b", .callc (v "eq") (v "kk"))]
              (.case (v "b")
                "t1" (lets [("res", .inl (.sum .int .unit) (v "pos"))] (.ret (v "res")))
                "f1" (lets ([("l1", .sub (v "lv") (.lit 1)), ("ln", .nameI (v "l1")),
                             ("p1", .add (v "pos") (.lit 1))] ++
                            tuple "q" [v "kb", v "cv", v "k", v "eq", v "p1", v "ln"])
                  (.tail "lfProbe" ["m", "ln"] (v "q0") [K, V])))))))))))

/-- Open the map, hash, probe from the hash with a full budget; `cont` sees
`kb`, `vb`, `cv`, `res`. -/
def withLF (cont : Expr) : Expr :=
  .split (v "mp") "tb" "fs" (.split (v "fs") "hash" "eq"
    (.unpack (v "tb") "m" "tt" (.split (v "tt") "cv" "bs" (.split (v "bs") "kb" "vb"
      (lets ([("hv", .callc (v "hash") (v "k")), ("l0", .nameI (v "cv"))] ++
             tuple "q" [v "kb", v "cv", v "k", v "eq", v "hv", v "l0"] ++
             [("res", .call "lfProbe" ["m", "l0"] (v "q0") [K, V])]) cont)))))

/-- Publish a boxed `val` into slot `j`'s value cell. -/
def putVal : List (String × Op) :=
  [("vl", .idx (v "vb") (v "j")), ("bx", .new (v "val")), ("vp", .publish (v "bx")),
   ("u9", .store true (v "vl") (v "vp") none)]

def tt : Ty := HashMap.bool
def yes : Expr := lets [("y", .inl .unit .unit)] (.ret (v "y"))
def no : Expr := lets [("n", .inr .unit .unit)] (.ret (v "n"))

/-- `put(k, v)`: `true`, or `false` when the table is full. -/
def lfPutD : Decl where
  name := "lfPut"; tparams := [κKL, κVL]; idx := []; arg := "a"
  argTy := .prod LMap (.prod K V); retTy := HashMap.bool
  body := .split (v "a") "mp" "a1" (.split (v "a1") "k" "val"
    (withLF
      (.case (v "res")
        "pf" (lets ([("j", .rem (v "pf") (v "cv"))] ++ putVal) yes)
        "re" (.case (v "re")
          "pe" (lets [("j", .rem (v "pe") (v "cv")), ("kl", .idx (v "kb") (v "j")),
                      ("nl", .null .pub K), ("kx", .new (v "k")), ("kp", .publish (v "kx"))]
            (.cas true true (v "kl") (v "nl") (v "kp") "t" (lets putVal yes)
              (lets (tuple "w" [v "mp", v "k", v "val"]) (.tail "lfPut" [] (v "w0") [K, V]))))
          "full" no))))

/-- `get(k)`: a copy of the value, or `inl ()`. -/
def lfGetD : Decl where
  name := "lfGet"; tparams := [κKL, κVLc]; idx := []; arg := "a"
  argTy := .prod LMap K; retTy := SV
  body := .split (v "a") "mp" "k"
    (withLF
      (.case (v "res")
        "pf" (lets [("j", .rem (v "pf") (v "cv")), ("vl", .idx (v "vb") (v "j")), ("vo", .load true (v "vl"))]
          (.ifnull (v "vo") (lets [("e", .inl V .unit)] (.ret (v "e")))
            "vp" (lets [("x", .load true (v "vp")), ("r1", .inr .unit (v "x"))] (.ret (v "r1")))))
        "re" (lets [("e", .inl V .unit)] (.ret (v "e")))))

/-- `del(k)`: empty the value cell; the key stays. -/
def lfDelD : Decl where
  name := "lfDel"; tparams := [κKL, κVL]; idx := []; arg := "a"
  argTy := .prod LMap K; retTy := .unit
  body := .split (v "a") "mp" "k"
    (withLF
      (.case (v "res")
        "pf" (lets [("j", .rem (v "pf") (v "cv")), ("vl", .idx (v "vb") (v "j")),
                    ("nl", .null .pub V), ("u", .store true (v "vl") (v "nl") none)] (.ret .unit))
        "re" (.ret .unit)))

def lfLib : Prog := [lfNewD, lfProbeD, lfPutD, lfGetD, lfDelD]

#guard accepts (checkProg lfLib)

/-! ## Hazards -/

-- A plain claim store instead of `cas`: two putters could both claim the slot.
-- The checker does not see the race (a plain `rel` store to a pub cell is
-- legal), so this is a *functional* hazard the explorer shows below.
-- Finding: a claim `cas` without `acq`/`rel` is *accepted*.  A `Ptr? pub K`
-- cell is not view-sensitive (§3.5): the box was filled before `publish`'s
-- `dmb ishst`, and a reader reaches it through an address dependency.
#guard accepts (checkDecl lfLib { lfPutD with
    body := .split (v "a") "mp" "a1" (.split (v "a1") "k" "val"
      (withLF (.case (v "res") "pf" yes
        "re" (.case (v "re")
          "pe" (lets [("j", .rem (v "pe") (v "cv")), ("kl", .idx (v "kb") (v "j")),
                      ("nl", .null .pub K), ("kx", .new (v "k")), ("kp", .publish (v "kx"))]
            (.cas false false (v "kl") (v "nl") (v "kp") "t" yes no))
          "full" no)))) })

-- A key type that is not shareable cannot be published: `K : share` is required.
#guard rejects (checkDecl lfLib { lfNewD with name := "n2", tparams := [{ copy := true }, κVL] })
  "publish: the target is not shareable"
-- `get` with an affine value type: refused at the instance.
#guard rejects (checkDecl (lfLib ++ instLib) (dcl "g" .unit .unit
    (lets [("x", .call "lfGet" [] .unit [KI, .word (.lit 0) CoreLang.seqP])] (.ret .unit))))
  "a type argument does not have its parameter's kind"

/-! ## On the promise machine -/

def mkD : Decl := dcl "mkLF" .unit (substTs [.int, KI] 0 0 LMap)
  (lets (fnsOps ++ [("m", .call "lfNew" [] (v "fs") [KI, .int])]) (.ret (v "m")))

def LMI : Ty := substTs [.int, KI] 0 0 LMap

/-- Put `k ↦ val`, then read `k` back. -/
def putGetD (name : String) (k val : Nat) : Decl := dcl name LMI .int
  (lets (keyOps "K" k ++ tuple "w" [v "a", v "Kk", .lit val] ++
         [("ok", .call "lfPut" [] (v "w0") [KI, .int]), ("g", .pair (v "a") (v "Kk")),
          ("s", .call "lfGet" [] (v "g") [KI, .int]), ("x", .call "unw" [] (v "s"))])
    (.ret (v "x")))

def getD (name : String) (k : Nat) : Decl := dcl name LMI .int
  (lets (keyOps "K" k ++ [("g", .pair (v "a") (v "Kk")),
          ("s", .call "lfGet" [] (v "g") [KI, .int]), ("x", .call "unw" [] (v "s"))])
    (.ret (v "x")))

def lfProg : Prog := lfLib ++ [hashKID, eqKID, unwD, mkD,
  putGetD "p1" 1 10, putGetD "p9" 9 90, putGetD "p1b" 1 20, getD "g1" 1]

#guard accepts (checkProg lfProg)

def lfSetup : Option Setup := runSetup lfProg "mkLF" [] .unit [] 400
#guard lfSetup.isSome

-- One thread: put, then get back (the concurrent runs are in HashMapLFSlow.lean).
#guard let r := runE lfProg lfSetup (fun s => [("p1", [], LMI, s.res)]) 0 2000
  clean r && resultsOf r 0 == [[.num 10]]

end HashMapLF
