/-
**Unaligned 16-byte moves on the fuel-free
machine.** `movups xmm, [m]` / `movups [m], xmm` are
not single-copy atomic: `toEv` splits them into two 8-byte
pieces (`loadPieces`/`storePieces`), in address order, the piece at `a`
holding the low 64 bits. `EventsX64.lean` left these rows unstated; this
file states them and lifts them to `InstrSemInf`.

- `exec_movups_load`/`exec_movups_store`: the tree when neither piece is in
  the private `dmem` and neither crosses a 64-byte line (so neither faults);
  `_agrees`: with both accesses resolved to `⟨a, 8⟩` and `⟨a + 8, 8⟩`.
- `run_load2_iff`/`run_store2_iff`: a run of two reads (two non-exclusive
  writes) in closed form; the second event starts from the first's context.
  The second write's data views are `iv.forStore c1.stores` (`runTree`'s
  per-store views, after the first write).
- `instrSemInf_movups_load`/`instrSemInf_movups_store`: the machine step is
  the two events, then `finishInstr` and certification, all in one step.
  The two pieces are separate events: another thread can interleave a write
  between them only through the promise/timestamp choices `readSuccs` and
  `writeSuccs` already allow (tearing, as `ReachX64PublishMovups` shows).
-/
import Kraken.Promising.Lower.EventsX64Inf

namespace Kraken.Promising.Lower.X64

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Live Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep

/-! ## The tree -/

/-- Read a vector cell through `exec_of_cellAt` and unfold it (as the local
`cellV` of `EventsX64.lean`). -/
local macro "cellV" hc:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  show X64.exec _ = _
  rw [exec_of_cellAt $hc]
  try simp only [eaddr, BitVec.setWidth_eq] at *
  simp [Directive.interp, Instr.interp, AvxOperation.interp, toEv, EvTree.map, AvxRegOrMem.interp,
    MachineData.loadAvx, MachineData.storeAvx, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
    MachineData.rmw16K, $ts,*]
  try (simp only [map_access, EvTree.map])
  try rfl))

/-- The 128-bit value of two 8-byte pieces read as `v1` (at `a`, low half)
and `v2` (at `a + 8`), as `toEv` assembles it from their bytes. -/
def pairVal (v1 v2 : Val) : BitVec 128 :=
  BitVec.ofInt 128 (Int.ofBytes (Int.toBytes 8 (v1.toNat : Int) ++ Int.toBytes 8 (v2.toNat : Int)))

/-- The value written by the low piece (at `a`) of a 16-byte store of `v`. -/
def pieceLo (v : BitVec 128) : Val := (pieceVal ((Int.toBytes 16 v.toInt).take 8)).setWidth 128

/-- The value written by the high piece (at `a + 8`) of a 16-byte store of `v`. -/
def pieceHi (v : BitVec 128) : Val := (pieceVal ((Int.toBytes 16 v.toInt).drop 8)).setWidth 128

-- The piece at `a` carries the low 64 bits, both ways.
/-- info: true -/
#guard_msgs in
#eval pairVal 0x1111#128 0x2222#128 == 0x0000000000002222_0000000000001111#128
  && pieceLo 0x0000000000002222_0000000000001111#128 == 0x1111#128
  && pieceHi 0x0000000000002222_0000000000001111#128 == 0x2222#128

section Exec

variable {st : State} {sz : Nat}

/-- **`movups xmm, [m]`**, both pieces unmapped and line-internal: two plain
8-byte loads, at `a` then `a + 8`; `xmm := pairVal v1 v2`. -/
theorem exec_movups_load {x : AvxReg .W128} {m : AddrExpr}
    (hc : CellAt st (.instr (.avx .W64 .W128 (.movups (.avx x) (.mem m)))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a)
    (hdm : Mem.loadInt st.st.1.dmem a 16 = none)
    (hb1 : st.st.1.dmem.loadBytes a 8 = none) (hb2 : st.st.1.dmem.loadBytes (a + 8#64) 8 = none)
    (hl1 : crossesLine a = false) (hl2 : crossesLine (a + 8#64) = false) :
    isa.exec st = some (.access st.decls a 8 fun l1 => .load .plain false l1 fun v1 =>
      .access st.decls (a + 8#64) 8 fun l2 => .load .plain false l2 fun v2 =>
      .done (after st sz { st.st.1 with zmms := st.st.1.zmms.setLegacy x (pairVal v1 v2) })) := by
  cellV hc [ha, hdm, loadPieces, hb1, hb2, hl1, hl2]

/-- **`movups [m], xmm`**, both pieces unmapped and line-internal: two plain
8-byte stores, `pieceLo` at `a` then `pieceHi` at `a + 8`. -/
theorem exec_movups_store {x : AvxReg .W128} {m : AddrExpr}
    (hc : CellAt st (.instr (.avx .W64 .W128 (.movups (.mem m) (.avx x)))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a)
    (hdm : Mem.loadInt st.st.1.dmem a 16 = none)
    (hb1 : st.st.1.dmem.loadBytes a 8 = none) (hb2 : st.st.1.dmem.loadBytes (a + 8#64) 8 = none)
    (hl1 : crossesLine a = false) (hl2 : crossesLine (a + 8#64) = false) :
    isa.exec st = some (.access st.decls a 8 fun l1 =>
      .store .plain false l1 (pieceLo (st.st.1.zmms.get x)) fun _ =>
      .access st.decls (a + 8#64) 8 fun l2 =>
      .store .plain false l2 (pieceHi (st.st.1.zmms.get x)) fun _ =>
      .done (after st sz st.st.1)) := by
  cellV hc [ha, hdm, storePieces, hb1, hb2, hl1, hl2, pieceLo, pieceHi]

/-- `exec_movups_load` with both accesses resolved. -/
theorem exec_movups_load_agrees {x : AvxReg .W128} {m : AddrExpr}
    (hc : CellAt st (.instr (.avx .W64 .W128 (.movups (.avx x) (.mem m)))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a)
    (hdm : Mem.loadInt st.st.1.dmem a 16 = none)
    (hb1 : st.st.1.dmem.loadBytes a 8 = none) (hb2 : st.st.1.dmem.loadBytes (a + 8#64) 8 = none)
    (hl1 : crossesLine a = false) (hl2 : crossesLine (a + 8#64) = false)
    (hag1 : st.decls.AgreesAt a 8) (hag2 : st.decls.AgreesAt (a + 8#64) 8) :
    isa.exec st = some (.load .plain false ⟨a, 8⟩ fun v1 => .load .plain false ⟨a + 8#64, 8⟩ fun v2 =>
      .done (after st sz { st.st.1 with zmms := st.st.1.zmms.setLegacy x (pairVal v1 v2) })) := by
  rw [exec_movups_load hc ha hdm hb1 hb2 hl1 hl2]
  simp only [access_agrees hag1, access_agrees hag2]

/-- `exec_movups_store` with both accesses resolved. -/
theorem exec_movups_store_agrees {x : AvxReg .W128} {m : AddrExpr}
    (hc : CellAt st (.instr (.avx .W64 .W128 (.movups (.mem m) (.avx x)))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a)
    (hdm : Mem.loadInt st.st.1.dmem a 16 = none)
    (hb1 : st.st.1.dmem.loadBytes a 8 = none) (hb2 : st.st.1.dmem.loadBytes (a + 8#64) 8 = none)
    (hl1 : crossesLine a = false) (hl2 : crossesLine (a + 8#64) = false)
    (hag1 : st.decls.AgreesAt a 8) (hag2 : st.decls.AgreesAt (a + 8#64) 8) :
    isa.exec st = some (.store .plain false ⟨a, 8⟩ (pieceLo (st.st.1.zmms.get x)) fun _ =>
      .store .plain false ⟨a + 8#64, 8⟩ (pieceHi (st.st.1.zmms.get x)) fun _ =>
      .done (after st sz st.st.1)) := by
  rw [exec_movups_store hc ha hdm hb1 hb2 hl1 hl2]
  simp only [access_agrees hag1, access_agrees hag2]

end Exec

/-! ## Runs of two events -/

section Run

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **Two loads**: a read of `l1` from `c`, then a read of `l2` from its
context `c1`. -/
theorem run_load2_iff {σ : Type} {c c' : Ctx} {k1 k2 : LoadKind} {x1 x2 : Bool} {l1 l2 : Loc}
    {f : Val → Val → σ} {st : σ} :
    .ok (st, c') ∈ runTree A tid iv c (.load k1 x1 l1 fun v1 => .load k2 x2 l2 fun v2 => .done (f v1 v2)) ↔
      ∃ ts1 v1 c1 ts2 v2, (ts1, v1, c1) ∈ readSuccs A iv c k1 x1 l1 ∧
        (ts2, v2, c') ∈ readSuccs A iv c1 k2 x2 l2 ∧ st = f v1 v2 := by
  simp only [runTree, List.mem_flatMap, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨ts1, v1, c1⟩, h1, ⟨ts2, v2, c2⟩, h2, rfl, rfl⟩
    exact ⟨ts1, v1, c1, ts2, v2, h1, h2, rfl⟩
  · rintro ⟨ts1, v1, c1, ts2, v2, h1, h2, rfl⟩
    exact ⟨(ts1, v1, c1), h1, (ts2, v2, c'), h2, rfl, rfl⟩

/-- **Two non-exclusive stores**: a write to `l1` from `c`, then a write to
`l2` from its context `c1`, each with its own data views. -/
theorem run_store2_iff {σ : Type} {c c' : Ctx} {k1 k2 : StoreKind} {l1 l2 : Loc} {v1 v2 : Val}
    {s st : σ} :
    .ok (st, c') ∈ runTree A tid iv c (.store k1 false l1 v1 fun _ => .store k2 false l2 v2 fun _ => .done s) ↔
      st = s ∧ ∃ c1, c1 ∈ writeSuccs A tid (iv.forStore c.stores) c k1 false l1 v1 none ∧
        c' ∈ writeSuccs A tid (iv.forStore c1.stores) c1 k2 false l2 v2 none := by
  simp only [runTree, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_flatMap,
    List.mem_singleton, Except.ok.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨c1, h1, c2, h2, rfl, rfl⟩; exact ⟨rfl, c1, h1, h2⟩
  · rintro ⟨rfl, c1, h1, h2⟩; exact ⟨c1, h1, c', h2, rfl, rfl⟩

end Run

/-! ## The machine step -/

section Machine

variable (A : Arch) (tid : Nat) {c c' : Config isa} {t : Thread isa}
  (ht : c.threads[tid]? = some t) {sz : Nat}
include ht

/-- **`movups xmm, [m]`**: two plain 8-byte reads, of `⟨a, 8⟩` then
`⟨a + 8, 8⟩`, in one step; `xmm := pairVal v1 v2`. -/
theorem instrSemInf_movups_load {x : AvxReg .W128} {m : AddrExpr}
    (hc : CellAt (stOf t) (.instr (.avx .W64 .W128 (.movups (.avx x) (.mem m)))) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a)
    (hdm : Mem.loadInt (stOf t).st.1.dmem a 16 = none)
    (hb1 : (stOf t).st.1.dmem.loadBytes a 8 = none) (hb2 : (stOf t).st.1.dmem.loadBytes (a + 8#64) 8 = none)
    (hl1 : crossesLine a = false) (hl2 : crossesLine (a + 8#64) = false)
    (hag1 : (stOf t).decls.AgreesAt a 8) (hag2 : (stOf t).decls.AgreesAt (a + 8#64) 8) :
    InstrSemInf A tid c c' ↔ ∃ ts1 v1 c1 ts2 v2 c2 th,
      (ts1, v1, c1) ∈ readSuccs A (ivOf t) (ctx0 tid t c.mem) .plain false ⟨a, 8⟩ ∧
      (ts2, v2, c2) ∈ readSuccs A (ivOf t) c1 .plain false ⟨a + 8#64, 8⟩ ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with zmms := (stOf t).st.1.zmms.setLegacy x (pairVal v1 v2) }) c2 ∧
      CertOk A tid th c2.mem ∧ c' = c.withThread tid th c2.mem := by
  rw [instrSemInf_iff_of_exec A tid ht (exec_movups_load_agrees hc ha hdm hb1 hb2 hl1 hl2 hag1 hag2)]
  constructor
  · rintro ⟨th, mem', ⟨st, c2, hr, hth, rfl⟩, hcert, rfl⟩
    obtain ⟨ts1, v1, c1, ts2, v2, h1, h2, rfl⟩ := (run_load2_iff A tid _).mp hr
    exact ⟨ts1, v1, c1, ts2, v2, c2, th, h1, h2, hth, hcert, rfl⟩
  · rintro ⟨ts1, v1, c1, ts2, v2, c2, th, h1, h2, hth, hcert, rfl⟩
    exact ⟨th, c2.mem, ⟨_, c2, (run_load2_iff A tid _).mpr ⟨ts1, v1, c1, ts2, v2, h1, h2, rfl⟩, hth, rfl⟩,
      hcert, rfl⟩

/-- **`movups [m], xmm`**: two plain, non-exclusive 8-byte writes, `pieceLo`
to `⟨a, 8⟩` then `pieceHi` to `⟨a + 8, 8⟩`, in one step. -/
theorem instrSemInf_movups_store {x : AvxReg .W128} {m : AddrExpr}
    (hc : CellAt (stOf t) (.instr (.avx .W64 .W128 (.movups (.mem m) (.avx x)))) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a)
    (hdm : Mem.loadInt (stOf t).st.1.dmem a 16 = none)
    (hb1 : (stOf t).st.1.dmem.loadBytes a 8 = none) (hb2 : (stOf t).st.1.dmem.loadBytes (a + 8#64) 8 = none)
    (hl1 : crossesLine a = false) (hl2 : crossesLine (a + 8#64) = false)
    (hag1 : (stOf t).decls.AgreesAt a 8) (hag2 : (stOf t).decls.AgreesAt (a + 8#64) 8) :
    InstrSemInf A tid c c' ↔ ∃ c1 c2 th,
      c1 ∈ writeSuccs A tid ((ivOf t).forStore (ctx0 tid t c.mem).stores) (ctx0 tid t c.mem) .plain false
        ⟨a, 8⟩ (pieceLo ((stOf t).st.1.zmms.get x)) none ∧
      c2 ∈ writeSuccs A tid ((ivOf t).forStore c1.stores) c1 .plain false
        ⟨a + 8#64, 8⟩ (pieceHi ((stOf t).st.1.zmms.get x)) none ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t) (after (stOf t) sz (stOf t).st.1) c2 ∧
      CertOk A tid th c2.mem ∧ c' = c.withThread tid th c2.mem := by
  rw [instrSemInf_iff_of_exec A tid ht (exec_movups_store_agrees hc ha hdm hb1 hb2 hl1 hl2 hag1 hag2)]
  constructor
  · rintro ⟨th, mem', ⟨st, c2, hr, hth, rfl⟩, hcert, rfl⟩
    obtain ⟨rfl, c1, h1, h2⟩ := (run_store2_iff A tid _).mp hr
    exact ⟨c1, c2, th, h1, h2, hth, hcert, rfl⟩
  · rintro ⟨c1, c2, th, h1, h2, hth, hcert, rfl⟩
    exact ⟨th, c2.mem, ⟨_, c2, (run_store2_iff A tid _).mpr ⟨rfl, c1, h1, h2⟩, hth, rfl⟩, hcert, rfl⟩

end Machine

end Kraken.Promising.Lower.X64
