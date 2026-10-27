import Scc.Cert.Code1A64
import Spike.Lib.A64Abort
import Spike.Lib.A64Print
import Spike.Lib.A64Alloc

/-!
# The runtime routines' depths from their segment lemmas (AArch64)

`Code1A64.rtDepth` claims, for each runtime routine a stack-checked
function may call, the most bytes it uses below the caller's `sp` at the
`bl`: `scc_rt_abort` 48, `scc_rt_print` 96, `scc_rt_alloc` 208. This file
derives each from the region bounds (`hlo`, `hhi`, `hal`) of the routines'
segment lemmas, composed along the chain of calls:

* the caller's region `T`, based at its `sp` at the `bl` (the routine's
  entry `sp`: `bl` pushes nothing, and every routine's entry offset `oE`
  is `0`), with `T.lo ≤ -d` for the routine's `rtDepth` entry `d`;
* the routine's own region is `T` (`seg_abort`, `seg_print`, `seg_alloc`
  need `T.lo ≤ -48`, `-48`, `-160`);
* `scc_rt_print` and `scc_rt_alloc` exit into `scc_rt_abort` with `sp` at
  their exit node's offset `e` (`Print.E … .abort`, `Alloc.E … .abort`:
  `-48`, `-160`); `scc_rt_abort`'s region there is `abortR T e`
  (`T.callee e (-48) 0`), which `seg_abort` needs to be `OK`, 16-aligned,
  with `lo ≤ -48` and `0 ≤ hi`, and which lies inside `T`;
* `scc_rt_abort` reaches its exit stub by a tail branch with `sp` back at
  its entry value, in the same region (`Disp.seg_abort` composes the
  dispatcher with the five stubs under one `hlo : R.lo ≤ -48`).

`abort_fits`, `print_fits`, `alloc_fits` give every region hypothesis of
every link from `T.lo ≤ -d`; `abort_chain`, `print_chain`, `alloc_chain`
state the chain's depth (the deepest link) at most `d`.
`Spike.Test.RtDepthA64` feeds the derived bounds into the segment lemmas
themselves, so a change of a lemma's region that `rtDepth` no longer covers
breaks the build.

What is not here: no theorem yet composes `scc_rt_print`'s or
`scc_rt_alloc`'s abort exit with `seg_abort` into one segment (their
consumers stop at the exit, `scc_rt_abort`'s entry); the bounds above are
those such a composition needs.
-/

namespace Spike.Lib.RtDepthA64

open Spike.Lib Scc.Cert.Code1A64

/-- `scc_rt_abort`'s region when entered with `sp` at offset `e` of `T`. -/
abbrev abortR (T : Region) (e : Int) : Region := T.callee e (-48) 0

/-- **`scc_rt_abort`'s region facts** at offset `e` of `T` (`seg_abort`'s
`hR`, `hal`, `hlo`, `hhi`), and inside `T`, given `T.lo ≤ e - 48`. -/
theorem abortR_ok {T : Region} {e : Int} (hT : T.OK) (hal : T.base.toNat % 16 = 0) (hhi : 0 ≤ T.hi)
    (he0 : e < 0) (he16 : e % 16 = 0) (hlo : T.lo ≤ e - 48) :
    (abortR T e).OK ∧ (abortR T e).base.toNat % 16 = 0 ∧ (abortR T e).lo ≤ -48 ∧ 0 ≤ (abortR T e).hi ∧
      T.lo ≤ e + (abortR T e).lo ∧ e + (abortR T e).hi ≤ T.hi := by
  have hb := Region.callee_base (hi' := 0) hT (kc := e) (lo' := -48) (by omega) (by omega) (by omega)
  refine ⟨Region.callee_ok hT (by omega) (by omega) (by omega) (by omega), ?_, Int.le_refl _, Int.le_refl _,
    by simp only [abortR, Region.callee]; omega, by simp only [abortR, Region.callee]; omega⟩
  simp only [abortR] at hb ⊢
  omega

/-- `scc_rt_print`'s abort exit is at `sp` offset `-48` of its region. -/
theorem print_abort_sp (lab : Label → Int64) (c0 : Ctl) (x29 ra : BitVec 64) :
    (A64.Print.E lab c0 x29 ra .abort).o.sp = -48 := rfl

/-- `scc_rt_alloc`'s heap abort exit is at `sp` offset `-160` of its region. -/
theorem alloc_abort_sp (lab : Label → Int64) (ms : MemSide Kraken.Promising.AArch64.isaLSE2) (q : A64.Alloc.Call)
    (lbl : WeakMem.AllocLabel → Option Nat) :
    (A64.Alloc.E lab ms q lbl .abort).o.sp = -160 := rfl

/-- The entry offsets are `0` (`bl` pushes nothing): every routine's region
is based at the caller's `sp` at the `bl`. -/
theorem entry_sp : A64.Abort.oE.sp = 0 ∧ A64.Print.oE.sp = 0 ∧ A64.Alloc.oE.sp = 0 := ⟨rfl, rfl, rfl⟩

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

/-- **`scc_rt_abort`'s depth**: its region's `lo` (`seg_abort`, dispatcher
and stubs in one region) is within its `rtDepth` entry. -/
theorem abort_chain {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.abort = some d) : (48 : Int) ≤ d := by
  rw [lookup_abort hd]; decide

/-- **`scc_rt_print`'s depth**: the deeper of its own region (`seg_print`)
and `scc_rt_abort`'s below its abort exit is within its `rtDepth` entry. -/
theorem print_chain {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.print = some d)
    (lab : Label → Int64) (c0 : Ctl) (x29 ra : BitVec 64) :
    max 48 (48 - (A64.Print.E lab c0 x29 ra .abort).o.sp) ≤ d := by
  rw [lookup_print hd, print_abort_sp]; decide

/-- **`scc_rt_alloc`'s depth**: the deeper of its own region (`seg_alloc`)
and `scc_rt_abort`'s below its heap abort exit is within its `rtDepth`
entry. -/
theorem alloc_chain {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.alloc = some d)
    (lab : Label → Int64) (ms : MemSide Kraken.Promising.AArch64.isaLSE2) (q : A64.Alloc.Call) (lbl : WeakMem.AllocLabel → Option Nat) :
    max 160 (48 - (A64.Alloc.E lab ms q lbl .abort).o.sp) ≤ d := by
  rw [lookup_alloc hd, alloc_abort_sp]; decide

/-! ## Every link's region hypotheses from `T.lo ≤ -d` -/

/-- **`scc_rt_abort` called with `T.lo ≤ -d`**: `seg_abort`'s `hlo`. -/
theorem abort_fits {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.abort = some d) {T : Region}
    (hlo : T.lo ≤ -(d : Int)) : T.lo ≤ -48 := by
  have := lookup_abort hd; subst this; simpa using hlo

/-- **`scc_rt_print` called with `T.lo ≤ -d`**: `seg_print`'s `hlo` in `T`,
and `seg_abort`'s region hypotheses at its abort exit, inside `T`. -/
theorem print_fits {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.print = some d) {T : Region}
    (hT : T.OK) (hal : T.base.toNat % 16 = 0) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int))
    (lab : Label → Int64) (c0 : Ctl) (x29 ra : BitVec 64) :
    let e := (A64.Print.E lab c0 x29 ra .abort).o.sp
    T.lo ≤ -48 ∧ (abortR T e).OK ∧ (abortR T e).base.toNat % 16 = 0 ∧ (abortR T e).lo ≤ -48 ∧
      0 ≤ (abortR T e).hi ∧ T.lo ≤ e + (abortR T e).lo ∧ e + (abortR T e).hi ≤ T.hi := by
  have := lookup_print hd; subst this
  simp only [print_abort_sp]
  exact ⟨by omega, abortR_ok hT hal hhi (by decide) (by decide) (by omega)⟩

/-- **`scc_rt_alloc` called with `T.lo ≤ -d`**: `seg_alloc`'s `hlo` in `T`,
and `seg_abort`'s region hypotheses at its heap abort exit, inside `T`. -/
theorem alloc_fits {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.alloc = some d) {T : Region}
    (hT : T.OK) (hal : T.base.toNat % 16 = 0) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int))
    (lab : Label → Int64) (ms : MemSide Kraken.Promising.AArch64.isaLSE2) (q : A64.Alloc.Call) (lbl : WeakMem.AllocLabel → Option Nat) :
    let e := (A64.Alloc.E lab ms q lbl .abort).o.sp
    T.lo ≤ -160 ∧ (abortR T e).OK ∧ (abortR T e).base.toNat % 16 = 0 ∧ (abortR T e).lo ≤ -48 ∧
      0 ≤ (abortR T e).hi ∧ T.lo ≤ e + (abortR T e).lo ∧ e + (abortR T e).hi ≤ T.hi := by
  have := lookup_alloc hd; subst this
  simp only [alloc_abort_sp]
  exact ⟨by omega, abortR_ok hT hal hhi (by decide) (by decide) (by omega)⟩

end Spike.Lib.RtDepthA64
