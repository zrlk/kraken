/-
# USyntaxTest — pinned behaviour of the UnElab parser (`USyntax`)

The EM0 prelude and `em0.u` parse, elaborate in the stated order (one
counter per block, left to right, innermost first), and the elaboration is accepted by the
core checker; the refused forms are refused with their messages; spans, `--print-elab`, scenarios, `.i`
signatures, and resynchronisation after errors.
-/
import WeakCore.USyntax
open CoreLang CoreTerm Syntax UnElab USyntax

namespace USyntaxTest

/-- The EM0 prelude (`EM0Prelude.u`), verbatim. -/
def preludeU : String := "
def spin(n : Int) : Void = tail spin(n)
def exit(n : Int) : Void =
  let _ = exitEv n
  tail spin(n)
def emit8(a : LanesU8 * U64 * Int) : U64 =
  let (w, cnt, j) = a
  if (fcmp eq cnt (cvt U64 0)) = 1 then ret cnt
  else
    let _ = emit (lane w j)
    let cnt1 = fop sub cnt (cvt U64 1)
    if j = 7 then ret cnt1 else tail emit8(w, cnt1, j + 1)
def printL{i, d}(a : {Loc pub Array[i+1+d] LanesU8 | ini >= i+1+d} * Int[i] * Int[d] * U64) : U64 =
  let (s, iv, dv, cnt) = a
  let cnt1 = emit8(load (s[iv]), cnt, 0)
  if dv = 0 then ret cnt1
  else
    let un = nameI (dv - 1)
    let jn = nameI (iv + 1)
    tail printL{jn, un}(s, jn, un, cnt1)
def print{m}(a : ({Loc pub Array[m] LanesU8 | ini >= m} * Int[m]) * Int) : Unit =
  let ((s, mv), n) = a
  let cnt = cvt U64 n
  if mv = 0 then ret ()
  else
    let kn = nameI (mv - 1)
    let z = nameI 0
    let _ = printL{z, kn}(s, z, kn, cnt)
    ret ()
"

/-- The EM0 program `em0.u`, verbatim. -/
def em0U : String := "\nimport EM0Prelude
def hello(u : Unit) : exists q. ({Loc pub Array[q] LanesU8 | ini >= q} * Int[q]) * Int =
  let m = nameI 2
  let b = newBuf[LanesU8] m
  let _ = xchg b[0] (asLanes U8 8583909746840200520)
  let _ = xchg b[1] (asLanes U8 44634501743)
  ret (pack ((publish b, m), 13) at m : exists a. ({Loc pub Array[a] LanesU8 | ini >= a} * Int[a]) * Int)
def worker(a : ((exists q. ({Loc pub Array[q] LanesU8 | ini >= q} * Int[q]) * Int) * Ptr pub Int) * ThreadId) : Unit =
  let ((sl0, c), j) = a
  let <q, sl> = unpack sl0
  let _ = print{q}(sl)
  let _ = store rel c 1
  let _ = unpark j
  ret ()
def waitLoop(c : Ptr pub Int) : Int =
  if (load acq c) = 1 then ret 0 else
    let _ = park ()
    tail waitLoop(c)
def main(u : Unit) : Int =
  let sl = hello(())
  let c = publish (new (zero[Int]))
  let me = current ()
  let t = spawn worker ((sl, c), me) : ((exists q. ({Loc pub Array[q] LanesU8 | ini >= q} * Int[q]) * Int) * Ptr pub Int) * ThreadId
  tail waitLoop(c)
"

def preludeR : Except Err UParsed := parseUnit preludeU
def preludeP : Prog := match preludeR with | .ok r => elabProg r.unit.decls | .error _ => []
/-- `em0.u` against the prelude's signatures (as `sce` reads an import). -/
def em0R : Except Err UParsed := parseUnit em0U { lib := preludeP.reverse }
def em0P : Prog := match em0R with | .ok r => elabProg r.unit.decls | .error _ => []

#guard preludeR matches .ok _
#guard em0R matches .ok _
#guard (match em0R with | .ok r => r.unit.imports | .error _ => []) == ["EM0Prelude"]
#guard preludeP.map (·.name) == ["spin", "exit", "emit8", "printL", "print"]
#guard em0P.map (·.name) == ["hello", "worker", "waitLoop", "main"]
-- The elaboration is accepted by the core checker (the whole program, as `sce` emits it).
#guard accepts (checkProg (preludeP ++ em0P))
-- And it survives the core printer and parser (what Kraken's `scc` reads).
#guard match parseProg (showProg (preludeP ++ em0P)) with
  | .ok p => p.length == 9 && (p.zip (preludeP ++ em0P)).all fun (a, b) => sameDecl a b
  | .error _ => false

/-- The elaboration of one block, as `.w` text (no positions). -/
def blockW (p : Prog) (n : String) : String :=
  match p.find? (·.name == n) with
  | some d => showDecl d
  | none => "?"

-- emit8: one counter, the hidden pair first, innermost first.
#guard blockW preludeP "emit8" == "def emit8(a : LanesU8 * U64 * Int) : U64 =
  let (w, «%0») = a
  let (cnt, j) = «%0»
  let «%1» = cvt U64 0
  let «%2» = fcmp eq cnt «%1»
  if «%2» = 1 then
    ret cnt
  else
    let «%3» = lane w j
    let «%4» = emit «%3»
    let «%5» = cvt U64 1
    let cnt1 = fop sub cnt «%5»
    if j = 7 then
      ret cnt1
    else
      let «%6» = j + 1
      let «%7» = (cnt1, «%6»)
      let «%8» = (w, «%7»)
      tail emit8(«%8»)"
-- printL: `%2 = s[iv]`, `%3 = load %2`, `%4 = (cnt, 0)`, `%5 = (%3, %4)`, then the index names by lets.
#guard blockW preludeP "printL" == "def printL{i, d}(a : {Loc pub Array[i + 1 + d] LanesU8 | ini >= i + 1 + d} * Int[i] * Int[d] * U64) : U64 =
  let (s, «%0») = a
  let (iv, «%1») = «%0»
  let (dv, cnt) = «%1»
  let «%2» = s[iv]
  let «%3» = load «%2»
  let «%4» = (cnt, 0)
  let «%5» = («%3», «%4»)
  let cnt1 = emit8(«%5»)
  if dv = 0 then
    ret cnt1
  else
    let «%6» = dv - 1
    let un = nameI «%6»
    let «%7» = iv + 1
    let jn = nameI «%7»
    let «%8» = (un, cnt1)
    let «%9» = (jn, «%8»)
    let «%10» = (s, «%9»)
    tail printL{jn, un}(«%10»)"
-- hello: the pack's type is resolved after its operands (index `m` bound by the let, `q`/`a` by the types).
#guard blockW em0P "hello" == "def hello(u : Unit) : exists a. ({Loc pub Array[a] LanesU8 | ini >= a} * Int[a]) * Int =
  let m = nameI 2
  let b = newBuf[LanesU8] m
  let «%0» = asLanes U8 8583909746840200520
  let «%1» = xchg b[0] «%0»
  let «%2» = asLanes U8 44634501743
  let «%3» = xchg b[1] «%2»
  let «%4» = publish b
  let «%5» = («%4», m)
  let «%6» = («%5», 13)
  let «%7» = pack «%6» at m : exists a. ({Loc pub Array[a] LanesU8 | ini >= a} * Int[a]) * Int
  ret «%7»"
#guard blockW em0P "main" == "def main(u : Unit) : Int =
  let sl = hello(())
  let «%0» = zero[Int]
  let «%1» = new «%0»
  let c = publish «%1»
  let me = current ()
  let «%2» = (sl, c)
  let «%3» = («%2», me)
  let t = spawn worker «%3» : ((exists a. ({Loc pub Array[a] LanesU8 | ini >= a} * Int[a]) * Int) * Ptr pub Int) * ThreadId
  tail waitLoop(c)"
#guard blockW em0P "waitLoop" == "def waitLoop(c : Ptr pub Int) : Int =
  let «%0» = load acq c
  if «%0» = 1 then
    ret 0
  else
    let «%1» = park ()
    tail waitLoop(c)"

/-! ## Refused forms -/

def errOf (s : String) : String :=
  match parseUnit s with
  | .ok _ => "accepted"
  | .error e => s!"{e.line}:{e.col}: {e.msg}"

def refused (s msg : String) : Bool := ((errOf s).splitOn msg).length > 1

#guard refused "def f(x : Int) : Int = let y = if x = 1 then ret 0 else ret 1" msgJoin
#guard refused "def f(x : Int) : Int = let y = case x of inl a => ret 0 inr b => ret 1" msgJoin
#guard refused "def f(x : Int) : Int = let y = «%1» ret y" msgReserved
#guard refused "def f(x : Int) : Int = let «%1» = x ret x" msgReserved
#guard refused "def f(x : Int) : Int = let y = x + x + x ret y" msgChain
#guard refused "def f(m : Ptr pub (Int * Int)) : Int = let y = load fld 0 m ret y" msgParen
#guard refused "def f(c : Ptr pub Int) : Unit = let _ = store rel c f(1) ret ()" msgParen
#guard refused "def f(x : Int + Int) : Int = case x of inl _ => ret 0 inr b => ret 1" msgUnderscore
#guard refused "def f(x : Int) : Int = ret _" msgUnderscore
#guard refused "def f(x : Int) : Int = ret x + 1" msgParenT
#guard refused "def f(x : Int) : Int = if x + 1 = 2 then ret 0 else ret 1" msgParenT
-- Error positions are the source's.
#guard errOf "def f(x : Int) : Int =\n  let y = x + x + x\n  ret y" == s!"2:17: {msgChain}"
-- Accepted: a call bare as a term-form operand, a pattern-let right-hand side, a call argument; a call
-- parenthesised as an operand; whitespace is not significant.
#guard errOf "def g(x : Int) : Int = ret x
def f(c : Ptr pub Int) : Int =
  let _ = store rel c (g (1))
  let (a, b) = (g(1), g (2))
  let y = g(a) + 1
  let z = b[g(y)]
  if g(a) = 1 then ret g(b) else ret (g(b))" == "accepted"
-- `live`, `scenario`, `import` are keywords only at the top level, before an item (rule 8).
#guard errOf "def f(live : Int) : Int = let scenario = live let import = scenario ret import" == "accepted"

/-! ## Top level: `live`, `scenario`, `.i`, resynchronisation -/

def scen : String := "
scenario S = { setup = init(()) ; threads = [worker(0), worker(1)] ; promises = 0 ; depth = 300 ; crash = 1 ; live = 0 }
live[S] def worker(a : Int) : Unit = ret ()
live def push(a : Int) : Unit = ret ()
def init(u : Unit) : Unit = ret ()
"
#guard match parseUnit scen with
  | .ok r => (match r.unit.items with
      | [.scenario s, .decl d1 (some (some "S")), .decl d2 (some none), .decl d3 none] =>
          s.name == "S" && s.setup.1 == "init" && s.threads.map (·.1) == ["worker", "worker"] &&
          s.promises == some 0 && s.depth == some 300 && s.crash == some 1 && s.live == 0 &&
          d1.name == "worker" && d2.name == "push" && d3.name == "init"
      | _ => false) && r.itemAt == [(2, 1), (3, 1), (4, 1), (5, 1)]
  | .error _ => false

-- An interface: signatures without bodies.
#guard match parseUnit "import EM0Prelude\ntype P = Int * Int\ndef f[α : *]{r}(x : Ptr[r] α) : P\nlive def g(u : Unit) : Unit" {} true with
  | .ok r => r.unit.imports == ["EM0Prelude"] &&
      (match r.unit.items with
       | [.type "P" _, .sig f none, .sig g (some none)] => f.name == "f" && f.idx == ["r"] && f.tparams.length == 1 && g.name == "g"
       | _ => false)
  | .error _ => false

-- Parsing resumes at the next item: two errors, the good blocks kept.
#guard let r := parseUnitAll "def a(x : Int) : Int = ret x\ndef b(x : Int) : Int = let y = x + x + x ret y\ndef c(x : Int) : Int = ret x\ndef d(x : Int) : Int = let = 1\ndef e(x : Int) : Int = ret x"
  r.errs.map (·.line) == [2, 4] && r.unit.decls.map (·.name) == ["a", "c", "e"]

/-! ## Spans and `--print-elab` -/

#guard match preludeR with
  | .ok r => (spanAt r.spans.toList "emit8" [0, 0]).map (fun s => (s.line, s.col, s.eline, s.ecol, s.what)) ==
      some (8, 19, 8, 30, "%1")   -- `cvt U64 0` inside `if (fcmp eq cnt (cvt U64 0)) = 1`
  | .error _ => false

#guard printElab "def f(m : Ptr pub (Int * Int)) : Int =\n  let y = load acq (fld 0 m)\n  ret y" matches
  .ok "def f(m : Ptr pub (Int * Int)) : Int =\n  let «%0» = fld 0 m  -- 2:20\n  let y = load acq «%0»  -- 2:11\n  ret y  -- 3:3"

/-! ## (M1) The TEXTS T2 extern surface in UnElab: tuple arguments are operands -/

def m1U : String := "
def pk(u : Unit) : Unit =
  let x = park ()
  ret x
def upk(t : ThreadId) : Unit =
  let x = unpark t
  ret x
def mr(r : Reg[32, rw]) : Reg[32, rw] * U32 =
  let x = mmioRead[32, rw, acq] r
  ret x
def ra(b : Blk[16, 32, rw, stride 8; 0 3]) : Reg[32, rw] * Blk[16, 32, rw, stride 8; 1 0 3] =
  let x = regAt[1 of Blk[16, 32, rw, stride 8; 0 3]] b
  ret x
device def dr(d : Reg[32, wo]) : U32 =
  let x = devRecv[32] d
  ret x
device def dc(u : Unit) : U32 =
  let x = devChoice[32] ()
  ret x
device def di(l : Irq) : Unit =
  let x = devIrq l
  ret x
device def dout(v : U64) : Unit =
  let x = devOut[64] v
  ret x
def mw(a : Reg[32, rw] * U32) : Reg[32, rw] =
  let (r, v) = a
  let x = mmioWrite[32, rw, rel] (r, v)
  ret x
device def dw(a : Reg[32, ro] * U32) : Unit =
  let (s, v) = a
  let x = devWrite[32] (s, v)
  ret x
"

def m1UR : Except Err UParsed := parseUnit m1U
def m1UP : Prog := match m1UR with | .ok r => elabProg r.unit.decls | .error _ => []

#guard m1UR matches .ok _
#guard m1UP.length == 10
#guard accepts (checkProg m1UP)
#guard match parseUnit "def rb(b : Blk[16, 32, rw, stride 8; 0 3]) : Reg[32, rw] * Blk[16, 32, rw, stride 8; 3 0 3] =\n  let x = regAt[3 of Blk[16, 32, rw, stride 8; 0 3]] b\n  ret x" with
  | .ok r => match checkProg (elabProg r.unit.decls) with
    | .ok _ => false
    | .error e => (e.splitOn "inadmissible extern").length > 1
  | .error _ => false

end USyntaxTest
