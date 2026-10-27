import Spike.Lib.RtDepthA64

/-!
The runtime routines' depths from their segment lemmas
(`Spike/Lib/RtDepthA64.lean`): their axioms, and the derived region
bounds fed into the segment lemmas themselves (`seg_abort`, `seg_print`,
`seg_alloc`, and `seg_abort` at the abort exits of the latter two), so that
a lemma's region no longer covered by `Code1A64.rtDepth` breaks the build.
-/

namespace Spike.Lib.RtDepthA64.Test

open Spike.Lib Spike.Lib.RtDepthA64 Scc.Cert.Code1A64

/--
info: 'Spike.Lib.RtDepthA64.print_fits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms print_fits

/--
info: 'Spike.Lib.RtDepthA64.alloc_fits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms alloc_fits

/--
info: 'Spike.Lib.RtDepthA64.alloc_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms alloc_chain

-- `scc_rt_abort` called directly: `seg_abort` in the caller's region.
example {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.abort = some d) {T : Region}
    (hlo : T.lo ≤ -(d : Int)) :=
  @A64.Abort.Disp.seg_abort (R := T) (hlo := abort_fits hd hlo)

-- `scc_rt_print`: `seg_print` in the caller's region, `seg_abort` at its
-- abort exit.
example {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.print = some d) {T : Region}
    (hT : T.OK) (hal : T.base.toNat % 16 = 0) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int))
    (lab : String → Int64) (c0 : Ctl) (x29 ra : BitVec 64) :=
  @A64.Print.seg_print (R := T) (hlo := (print_fits hd hT hal hhi hlo lab c0 x29 ra).1)
example {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.print = some d) {T : Region}
    (hT : T.OK) (hal : T.base.toNat % 16 = 0) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int))
    (lab : String → Int64) (c0 : Ctl) (x29 ra : BitVec 64) :=
  let h := print_fits hd hT hal hhi hlo lab c0 x29 ra
  @A64.Abort.Disp.seg_abort (R := abortR T (A64.Print.E lab c0 x29 ra .abort).o.sp)
    (hR := h.2.1) (hal := h.2.2.1) (hlo := h.2.2.2.1) (hhi := h.2.2.2.2.1)

-- `scc_rt_alloc`: `seg_alloc` in the caller's region, `seg_abort` at its
-- heap abort exit.
example {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.alloc = some d) {T : Region}
    (hT : T.OK) (hal : T.base.toNat % 16 = 0) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int))
    (lab : String → Int64) (ms : MemSide Kraken.Promising.AArch64.isaLSE2)
    (q : A64.Alloc.Call) (lbl : WeakMem.AllocLabel → Option Nat) :=
  @A64.Alloc.seg_alloc (R := T) (hlo := (alloc_fits hd hT hal hhi hlo lab ms q lbl).1)
example {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.alloc = some d) {T : Region}
    (hT : T.OK) (hal : T.base.toNat % 16 = 0) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int))
    (lab : String → Int64) (ms : MemSide Kraken.Promising.AArch64.isaLSE2)
    (q : A64.Alloc.Call) (lbl : WeakMem.AllocLabel → Option Nat) :=
  let h := alloc_fits hd hT hal hhi hlo lab ms q lbl
  @A64.Abort.Disp.seg_abort (R := abortR T (A64.Alloc.E lab ms q lbl .abort).o.sp)
    (hR := h.2.1) (hal := h.2.2.1) (hlo := h.2.2.2.1) (hhi := h.2.2.2.2.1)

end Spike.Lib.RtDepthA64.Test
