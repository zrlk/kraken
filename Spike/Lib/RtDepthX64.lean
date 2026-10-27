import Scc.Cert.Code1X64
import Spike.Lib.X64Abort
import Spike.Lib.X64Print
import Spike.Lib.X64Alloc

/-!
# The runtime routines' depths from their segment lemmas (x86-64)

`Code1X64.rtDepth` claims, for each runtime routine a stack-checked
function may call, the most bytes it uses below the caller's `%rsp` at the
`call`: `scc_rt_abort` 48, `scc_rt_print` 96, `scc_rt_alloc` 208. This file
derives a bound for each from the region bounds (`hlo`, `hhi`) of the
routines' segment lemmas, composed along the chain of calls:

* the caller's region `T`, based at its `%rsp` at the `call`, with
  `T.lo ≤ -d` for the routine's `rtDepth` entry `d`;
* the `call` pushes the return address, so the routine is entered with
  `%rsp` at `T`'s offset `-8`, and its region is based its entry offset
  `oE` below that (`routineR T sp lo hi`, at `T`'s offset `-8 - sp`):
  `scc_rt_abort` and `scc_rt_print` are entered at their frame base's offset
  `8`, `scc_rt_alloc` at its region's base (`abort_entry_sp`,
  `print_entry_sp`, `alloc_entry_sp`); `seg_abort`,
  `seg_print`, `seg_alloc` need their regions' `lo ≤ -24`, `-40`, `-160`
  and `hi ≥ 16`, `16`, `8`;
* `scc_rt_print` and `scc_rt_alloc` exit into `scc_rt_abort` with `%rsp`
  at their exit node's offset `e` (`Print.E … .abort`, `Alloc.E … .abort`:
  `-40`, `-160`, the return address of the `call scc_rt_abort` pushed);
  `scc_rt_abort`'s region there is based `8` below (its entry offset,
  `abortAt`), which is `T.callee` at the sum of the offsets
  (`Region.callee_callee`);
* `scc_rt_abort` reaches its exit stub by a tail jump with `%rsp` back at
  its entry value, in the same region (`Disp.seg_abort` composes the
  dispatcher with the five stubs under one `hlo : R.lo ≤ -24`).

The chains' depths from the caller's `%rsp` are 40, 88 and 200 bytes, each
8 below its `rtDepth` entry: the `rtDepth` entries count from the emitted
code's `%rsp` (`scc_rt_abort`'s and the stubs' `subq` leave their lowest 8
bytes unused), the regions only the cells the code accesses.

`abort_fits`, `print_fits`, `alloc_fits` give every region hypothesis of
every link from `T.lo ≤ -d`, each region inside `T`; `abort_chain`,
`print_chain`, `alloc_chain` state the chain's depth (the deepest link) at
most `d`. `Spike.Test.RtDepthX64` feeds the derived bounds into the segment
lemmas themselves, so a change of a lemma's region that `rtDepth` no
longer covers breaks the build.

What is not here: no theorem yet composes `scc_rt_print`'s or
`scc_rt_alloc`'s abort exit with `seg_abort` into one segment (their
consumers stop at the exit, `scc_rt_abort`'s entry); the bounds above are
those such a composition needs.
-/

namespace Spike.Lib.RtDepthX64

open Spike.Lib Scc.Cert.Code1X64

/-- A callee of a callee is a callee at the sum of the offsets. -/
theorem _root_.Spike.Lib.Region.callee_callee (T : Region) (a lo hi b lo' hi' : Int) :
    (T.callee a lo hi).callee b lo' hi' = T.callee (a + b) lo' hi' := by
  simp only [Region.callee, Region.addr, BitVec.ofInt_add, BitVec.add_assoc]

/-- The region `[lo, hi)` of a routine entered by a `call` with `%rsp` at
offset `sp` of its region, from its caller's region `T` (based at the
caller's `%rsp` at the `call`). -/
abbrev routineR (T : Region) (sp lo hi : Int) : Region := T.callee (-8 - sp) lo hi

/-- `scc_rt_abort`'s region when its caller's region `P` reaches its entry
(the return address pushed) with `%rsp` at offset `e`. -/
abbrev abortAt (P : Region) (e : Int) : Region := P.callee (e - X64.Abort.oE.sp) (-24) 16

/-- **A callee region's facts**: `OK`, its bounds, and inside `T`. -/
theorem callee_in {T : Region} {kc lo hi : Int} (hT : T.OK) (hlo : T.lo ≤ kc + lo) (hlo0 : lo ≤ 0)
    (hkc : kc < T.hi) (hhi : kc + hi ≤ T.hi) :
    (T.callee kc lo hi).OK ∧ (T.callee kc lo hi).lo ≤ lo ∧ hi ≤ (T.callee kc lo hi).hi ∧
      T.lo ≤ kc + (T.callee kc lo hi).lo ∧ kc + (T.callee kc lo hi).hi ≤ T.hi :=
  ⟨Region.callee_ok hT hlo hlo0 hkc hhi, Int.le_refl _, Int.le_refl _, hlo, hhi⟩

/-- `scc_rt_print`'s abort exit is at `%rsp` offset `-40` of its region. -/
theorem print_abort_sp (lab : String → Int64) (c0 : Ctl) (rbp0 ra : BitVec 64) :
    (X64.Print.E lab c0 rbp0 ra .abort).o.sp = -40 := rfl

/-- `scc_rt_alloc`'s heap abort exit is at `%rsp` offset `-160` of its region. -/
theorem alloc_abort_sp (lab : String → Int64) (ms : MemSide Kraken.Promising.X64.isa) (q : X64.Alloc.Call)
    (lbl : WeakMem.AllocLabel → Option Nat) :
    (X64.Alloc.E lab ms q lbl .abort).o.sp = -160 := rfl

/-- The entry offsets: `scc_rt_abort` (and its stubs) and `scc_rt_print`
are entered with `%rsp` at offset `8` of their regions, `scc_rt_alloc` at
offset `0`. -/
theorem abort_entry_sp : X64.Abort.oE.sp = 8 := rfl

theorem print_entry_sp : X64.Print.oE.sp = 8 := rfl

theorem alloc_entry_sp (lab : String → Int64) (ms : MemSide Kraken.Promising.X64.isa) (q : X64.Alloc.Call) :
    (X64.Alloc.N lab ms q .e).o.sp = 0 := rfl

theorem lookup_abort {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.abort = some d) : d = 48 := by
  have h : rtDepth.lookup Scc.Lower.Names.abort = some 48 := by decide
  rw [h] at hd; exact (Option.some.inj hd).symm

theorem lookup_print {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.print = some d) : d = 96 := by
  have h : rtDepth.lookup Scc.Lower.Names.print = some 96 := by decide
  rw [h] at hd; exact (Option.some.inj hd).symm

theorem lookup_alloc {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.alloc = some d) : d = 208 := by
  have h : rtDepth.lookup Scc.Lower.Names.alloc = some 208 := by decide
  rw [h] at hd; exact (Option.some.inj hd).symm

/-! ## The chains' depths -/

/-- **`scc_rt_abort`'s depth** from the caller's `%rsp`: the return
address, its region below its entry `%rsp` (`seg_abort`, dispatcher and
stubs in one region) is within its `rtDepth` entry. -/
theorem abort_chain {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.abort = some d) :
    8 + X64.Abort.oE.sp + 24 ≤ (d : Int) := by
  rw [lookup_abort hd]; decide

/-- **`scc_rt_print`'s depth**: the deeper of its own region (`seg_print`)
and `scc_rt_abort`'s below its abort exit is within its `rtDepth` entry. -/
theorem print_chain {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.print = some d)
    (lab : String → Int64) (c0 : Ctl) (rbp0 ra : BitVec 64) :
    max (8 + X64.Print.oE.sp + 40)
      (8 + X64.Print.oE.sp - (X64.Print.E lab c0 rbp0 ra .abort).o.sp + X64.Abort.oE.sp + 24) ≤ (d : Int) := by
  rw [lookup_print hd, print_abort_sp]; decide

/-- **`scc_rt_alloc`'s depth**: the deeper of its own region (`seg_alloc`)
and `scc_rt_abort`'s below its heap abort exit is within its `rtDepth`
entry. -/
theorem alloc_chain {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.alloc = some d)
    (lab : String → Int64) (ms : MemSide Kraken.Promising.X64.isa) (q : X64.Alloc.Call)
    (lbl : WeakMem.AllocLabel → Option Nat) :
    max (8 + (X64.Alloc.N lab ms q .e).o.sp + 160)
      (8 + (X64.Alloc.N lab ms q .e).o.sp - (X64.Alloc.E lab ms q lbl .abort).o.sp + X64.Abort.oE.sp + 24)
      ≤ (d : Int) := by
  rw [lookup_alloc hd, alloc_abort_sp, alloc_entry_sp]; decide

/-! ## Every link's region hypotheses from `T.lo ≤ -d` -/

/-- **`scc_rt_abort` called with `T.lo ≤ -d`**: `seg_abort`'s `hR`, `hlo`,
`hhi` for its region, inside `T`. -/
theorem abort_fits {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.abort = some d) {T : Region}
    (hT : T.OK) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int)) :
    let A := routineR T X64.Abort.oE.sp (-24) 16
    A.OK ∧ A.lo ≤ -24 ∧ 16 ≤ A.hi ∧ T.lo ≤ -16 + A.lo ∧ -16 + A.hi ≤ T.hi := by
  have := lookup_abort hd; subst this
  simp only [routineR]
  exact callee_in hT (by omega) (by omega) (by omega) (by omega)

/-- **`scc_rt_print` called with `T.lo ≤ -d`**: `seg_print`'s `hR`, `hlo`,
`hhi` for its region `P`, and `seg_abort`'s for `scc_rt_abort`'s at its
abort exit (`abortAt P e`, `T.callee` at the sum of the offsets), each
inside `T`. -/
theorem print_fits {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.print = some d) {T : Region}
    (hT : T.OK) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int))
    (lab : String → Int64) (c0 : Ctl) (rbp0 ra : BitVec 64) :
    let P := routineR T X64.Print.oE.sp (-40) 16
    let A := abortAt P (X64.Print.E lab c0 rbp0 ra .abort).o.sp
    (P.OK ∧ P.lo ≤ -40 ∧ 16 ≤ P.hi ∧ T.lo ≤ -16 + P.lo ∧ -16 + P.hi ≤ T.hi) ∧
      A = T.callee (-64) (-24) 16 ∧
      (A.OK ∧ A.lo ≤ -24 ∧ 16 ≤ A.hi ∧ T.lo ≤ -64 + A.lo ∧ -64 + A.hi ≤ T.hi) := by
  have := lookup_print hd; subst this
  simp only [routineR, abortAt, print_abort_sp, Region.callee_callee]
  exact ⟨callee_in hT (by omega) (by omega) (by omega) (by omega), rfl,
    callee_in hT (by omega) (by omega) (by omega) (by omega)⟩

/-- **`scc_rt_alloc` called with `T.lo ≤ -d`**: `seg_alloc`'s `hR`, `hlo`,
`hhi` for its region `L`, and `seg_abort`'s for `scc_rt_abort`'s at its
heap abort exit (`abortAt L e`, `T.callee` at the sum of the offsets),
each inside `T`. -/
theorem alloc_fits {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.alloc = some d) {T : Region}
    (hT : T.OK) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int))
    (lab : String → Int64) (ms : MemSide Kraken.Promising.X64.isa) (q : X64.Alloc.Call)
    (lbl : WeakMem.AllocLabel → Option Nat) :
    let L := routineR T (X64.Alloc.N lab ms q .e).o.sp (-160) 8
    let A := abortAt L (X64.Alloc.E lab ms q lbl .abort).o.sp
    (L.OK ∧ L.lo ≤ -160 ∧ 8 ≤ L.hi ∧ T.lo ≤ -8 + L.lo ∧ -8 + L.hi ≤ T.hi) ∧
      A = T.callee (-176) (-24) 16 ∧
      (A.OK ∧ A.lo ≤ -24 ∧ 16 ≤ A.hi ∧ T.lo ≤ -176 + A.lo ∧ -176 + A.hi ≤ T.hi) := by
  have := lookup_alloc hd; subst this
  simp only [routineR, abortAt, alloc_abort_sp, alloc_entry_sp, Region.callee_callee]
  exact ⟨callee_in hT (by omega) (by omega) (by omega) (by omega), rfl,
    callee_in hT (by omega) (by omega) (by omega) (by omega)⟩

end Spike.Lib.RtDepthX64
