import Scc.Cert.MapsCheckA64
import Scc.Emit.A64
import Scc.Frontend
import Scc.Lower.Program
import Scc.Test.Src

/-!
# scc's check of the tables on AArch64 (untrusted test)

`Scc.Cert.MapsA64.checkTables`, the check `scc-arm` runs before it writes a text: on `hello.w`,
`hello1.w`, `ret0.w`, `call1.w` and `wake.w` it passes with the constants of the default
configuration, and also without constants (`rtTablesOf`). It refuses when a constant is wrong:
a root map whose roots are dropped, or a root whose tag is changed. A constant set whose key
does not resolve is not used (the tables are computed instead), so the check still passes.
The result-tag guard (`checkResultTags`) passes on the five programs and refuses the two
disagreements scc once had: the allocator's result untagged (`oldAlloc`) and `scc_rt_main`'s
`rodata` result untagged (`oldMain`).
The certificate's checker with liveness witnesses (`checkW`) accepts scc's witnesses on the five
programs and refuses a witness with one live slot dropped (`dropLive`).
The frame state (`frameCheck`) agrees with the text on the five programs, and a flipped flag,
tables without the frame state, or a constant with a flipped flag are refused.
-/

namespace Scc.Cert.MapsCheckA64Test
open Scc.Cert.Maps Scc.Cert.MapsA64 Scc.Cert.MapsRtA64

/-- The AArch64 IR, items and safepoints of a WeakCore source. -/
def compileW (src : String) :
    Except String (IR.Program × List Scc.Emit.A64.Item × List (String × List Int × List Int)) := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error ds => throw (String.intercalate "\n" (ds.map (·.render "input")))
  let ir ← Lower.lowerProgram { arch := .arm } c
  let (its, ms) ← Scc.Emit.A64.emitItemsMaps ir
  pure (ir, its, ms)

/-- The check passes with the constants `c`. -/
def passes (c : Option RTables) (src : String) : Bool :=
  match compileW src with
  | .ok (p, its, ms) => (checkTablesWith c p its ms).toBool
  | .error _ => false

/-- `rtConstA64` with the roots of its first root map that has roots dropped. -/
def dropRoots (c : RTables) : RTables :=
  match c.maps.findIdx? (!·.roots.isEmpty) with
  | some i => { c with maps := c.maps.modify i fun m => { m with roots := [] } }
  | none => c

/-- `rtConstA64` with the tag of the first root of its first root map that has roots flipped. -/
def flipTag (c : RTables) : RTables :=
  let flip : Tag → Tag := fun | .heap => .stack | .stack => .heap
  match c.maps.findIdx? (!·.roots.isEmpty) with
  | some i => { c with maps := c.maps.modify i fun m =>
      { m with roots := m.roots.modify 0 fun (l, t) => (l, flip t) } }
  | none => c

/-- `rtConstA64` with the key of its first root map pointing past its routine's end. -/
def badKey (c : RTables) : RTables :=
  { c with maps := c.maps.modify 0 fun m => { m with key := { m.key with idx := 100000 } } }

-- The corruptions change the constants.
#guard dropRoots rtConstA64 != rtConstA64
#guard flipTag rtConstA64 != rtConstA64
#guard badKey rtConstA64 != rtConstA64

-- The check scc runs: the default configuration's constants.
#guard (consts? {}).isSome
#guard passes (consts? {}) (w_src% "Scc/Test/hello.w")
#guard passes (consts? {}) (w_src% "Scc/Test/hello1.w")
#guard passes (consts? {}) (w_src% "Scc/Test/ret0.w")
#guard passes (consts? {}) (w_src% "Scc/Test/call1.w")
#guard passes (consts? {}) (w_src% "Scc/Test/wake.w")

-- Without constants (another configuration): the routines' tables computed.
#guard passes none (w_src% "Scc/Test/hello1.w")
#guard passes none (w_src% "Scc/Test/wake.w")

-- A wrong constant is refused.
#guard !passes (some (dropRoots rtConstA64)) (w_src% "Scc/Test/hello1.w")
#guard !passes (some (dropRoots rtConstA64)) (w_src% "Scc/Test/wake.w")
#guard !passes (some (flipTag rtConstA64)) (w_src% "Scc/Test/hello1.w")
#guard !passes (some (flipTag rtConstA64)) (w_src% "Scc/Test/wake.w")

-- A constant set whose key does not resolve is not used.
#guard passes (some (badKey rtConstA64)) (w_src% "Scc/Test/hello1.w")

/-- The allocator before its result was tagged: no heap registers. -/
def oldAlloc (p : IR.Program) : IR.Program :=
  { p with funcs := p.funcs.map fun f =>
      if f.name == "scc_rt_alloc" then { f with heapRegs := [] } else f }

/-- `scc_rt_main` before `rodata`'s result was tagged: only `tcb` tagged. -/
def oldMain (p : IR.Program) : IR.Program :=
  { p with funcs := p.funcs.map fun f =>
      if f.name == "scc_rt_main" then { f with heapRegs := ["tcb"], scalarRegs := [] } else f }

/-- `oldMain` with `scc_rt_main`'s call of `rodata` writing fresh registers that it never reads:
an unused heap result, not compared. -/
def deadMain (p : IR.Program) : IR.Program :=
  let q := oldMain p
  { q with funcs := q.funcs.map fun f =>
      if f.name == "scc_rt_main" then
        { f with blocks := f.blocks.map fun b => { b with insts := b.insts.map fun
            | .call ds g a => if g == "wc_rodata" then .call (ds.map (· ++ "_dead")) g a
                              else .call ds g a
            | i => i } }
      else f }

/-- The result-tag guard on `v` of the IR of a WeakCore source. -/
def resultTagsOk (v : IR.Program → IR.Program) (src : String) : Except String Unit := do
  let (p, _, _) ← compileW src
  checkResultTags (v p)

-- The result tags agree on the five programs.
#guard (resultTagsOk id (w_src% "Scc/Test/hello.w")).toBool
#guard (resultTagsOk id (w_src% "Scc/Test/hello1.w")).toBool
#guard (resultTagsOk id (w_src% "Scc/Test/ret0.w")).toBool
#guard (resultTagsOk id (w_src% "Scc/Test/call1.w")).toBool
#guard (resultTagsOk id (w_src% "Scc/Test/wake.w")).toBool

-- The two old disagreements are refused.
/-- info: Except.error "tables: wc_rodata's call of scc_rt_alloc: result b%0's tag differs from scc_rt_alloc's" -/
#guard_msgs in
#eval resultTagsOk oldAlloc (w_src% "Scc/Test/hello1.w")
#guard !(resultTagsOk oldAlloc (w_src% "Scc/Test/wake.w")).toBool
/-- info: Except.error "tables: scc_rt_main's call of wc_rodata: result s%0's tag differs from wc_rodata's" -/
#guard_msgs in
#eval resultTagsOk oldMain (w_src% "Scc/Test/hello1.w")

-- An unused result is not compared: `rodata`'s heap result into a register never read passes.
#guard deadMain (compileW (w_src% "Scc/Test/hello1.w") |>.toOption |>.get!).1 !=
  oldMain (compileW (w_src% "Scc/Test/hello1.w") |>.toOption |>.get!).1
#guard (resultTagsOk deadMain (w_src% "Scc/Test/hello1.w")).toBool

/-- The witnesses with the first slot of the first non-empty entry dropped. -/
def dropLive (ws : List (Array (List Int))) : List (Array (List Int)) :=
  match ws.findIdx? (·.any (!·.isEmpty)) with
  | some i => ws.modify i fun w => match w.findIdx? (!·.isEmpty) with
    | some k => w.modify k List.tail
    | none => w
  | none => ws

/-- On the tables of a WeakCore source and scc's witnesses `ws`: whether `v ws` differs from
`ws`, and whether the checker with witnesses accepts `v ws`. -/
def witnessOk (v : List (Array (List Int)) → List (Array (List Int))) (src : String) :
    Option (Bool × Bool) :=
  match (do
    let (p, its, _) ← compileW src
    let (items, fns) ← fnTagsA64 p its
    let t ← compute fns items
    let ws := witness fns items
    pure (v ws != ws, checkW fns items (v ws) t)) with
  | .ok r => some r
  | .error _ => none

-- scc's witnesses pass the certificate's checker.
#guard witnessOk id (w_src% "Scc/Test/hello.w") == some (false, true)
#guard witnessOk id (w_src% "Scc/Test/hello1.w") == some (false, true)
#guard witnessOk id (w_src% "Scc/Test/ret0.w") == some (false, true)
#guard witnessOk id (w_src% "Scc/Test/call1.w") == some (false, true)
#guard witnessOk id (w_src% "Scc/Test/wake.w") == some (false, true)
-- A witness with a live slot dropped is refused (no post-fixpoint: the reference is the least).
#guard witnessOk dropLive (w_src% "Scc/Test/hello1.w") == some (true, false)
#guard witnessOk dropLive (w_src% "Scc/Test/wake.w") == some (true, false)

/-- `frameCheck` on the full tables of a WeakCore source, changed by `v`. -/
def frameOk (v : Tables → Tables) (src : String) : Except String Unit := do
  let (p, its, _) ← compileW src
  let items ← itemsOf its
  let t ← computeA64 p its
  frameCheck p its items (v t)

/-- The tables with the frame state of the first map whose kind is `k` flipped. -/
def flipFrame (k : Kind) (t : Tables) : Tables :=
  match t.maps.findIdx? (·.pt.kind == k) with
  | some i => { t with maps := t.maps.modify i fun m => { m with frameless := !m.frameless } }
  | none => t

/-- The tables with every map's frame state cleared (the tables before the frame state). -/
def noFrame (t : Tables) : Tables := { t with maps := t.maps.map ({ · with frameless := false }) }

/-- `rtConstA64` with the frame state of its first root map flipped. -/
def flipConstFrame (c : RTables) : RTables :=
  { c with maps := c.maps.modify 0 fun m => { m with frameless := !m.frameless } }

#guard flipConstFrame rtConstA64 != rtConstA64

-- The frame state agrees with the text on the five programs.
#guard (frameOk id (w_src% "Scc/Test/hello.w")).toBool
#guard (frameOk id (w_src% "Scc/Test/hello1.w")).toBool
#guard (frameOk id (w_src% "Scc/Test/ret0.w")).toBool
#guard (frameOk id (w_src% "Scc/Test/call1.w")).toBool
#guard (frameOk id (w_src% "Scc/Test/wake.w")).toBool
-- A frameless map that is not, a map that is but is not flagged, and tables without the
-- frame state are refused.
#guard !(frameOk (flipFrame .call) (w_src% "Scc/Test/hello1.w")).toBool
#guard !(frameOk (flipFrame .ret) (w_src% "Scc/Test/hello1.w")).toBool
#guard !(frameOk (flipFrame .blockEntry) (w_src% "Scc/Test/hello1.w")).toBool
#guard !(frameOk noFrame (w_src% "Scc/Test/wake.w")).toBool
-- A constant with its frame state flipped is refused (the merged tables differ).
#guard !passes (some (flipConstFrame rtConstA64)) (w_src% "Scc/Test/hello1.w")

end Scc.Cert.MapsCheckA64Test
