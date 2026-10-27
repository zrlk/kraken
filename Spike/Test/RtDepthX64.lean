import Spike.Lib.RtDepthX64

/-!
The runtime routines' depths from their segment lemmas
(`Spike/Lib/RtDepthX64.lean`): their axioms, and the derived region
bounds fed into the segment lemmas themselves (`seg_abort`, `seg_print`,
`seg_alloc`, and `seg_abort` at the abort exits of the latter two), so that
a lemma's region no longer covered by `Code1X64.rtDepth` breaks the build.
-/

namespace Spike.Lib.RtDepthX64.Test

open Spike.Lib Spike.Lib.RtDepthX64 Scc.Cert.Code1X64

/--
info: 'Spike.Lib.RtDepthX64.print_fits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms print_fits

/--
info: 'Spike.Lib.RtDepthX64.alloc_fits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms alloc_fits

/--
info: 'Spike.Lib.RtDepthX64.alloc_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms alloc_chain

-- `scc_rt_abort` called directly: `seg_abort` in its region.
example {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.abort = some d) {T : Region}
    (hT : T.OK) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int)) :=
  let h := abort_fits hd hT hhi hlo
  @X64.Abort.Disp.seg_abort (R := routineR T X64.Abort.oE.sp (-24) 16)
    (hR := h.1) (hlo := h.2.1) (hhi := h.2.2.1)

-- `scc_rt_print`: `seg_print` in its region, `seg_abort` at its abort exit.
example {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.print = some d) {T : Region}
    (hT : T.OK) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int))
    (lab : String → Int64) (c0 : Ctl) (rbp0 ra : BitVec 64) :=
  let h := print_fits hd hT hhi hlo lab c0 rbp0 ra
  @X64.Print.seg_print (R := routineR T X64.Print.oE.sp (-40) 16)
    (hR := h.1.1) (hlo := h.1.2.1) (hhi := h.1.2.2.1)
example {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.print = some d) {T : Region}
    (hT : T.OK) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int))
    (lab : String → Int64) (c0 : Ctl) (rbp0 ra : BitVec 64) :=
  let h := print_fits hd hT hhi hlo lab c0 rbp0 ra
  @X64.Abort.Disp.seg_abort
    (R := abortAt (routineR T X64.Print.oE.sp (-40) 16) (X64.Print.E lab c0 rbp0 ra .abort).o.sp)
    (hR := h.2.2.1) (hlo := h.2.2.2.1) (hhi := h.2.2.2.2.1)

-- `scc_rt_alloc`: `seg_alloc` in its region, `seg_abort` at its heap abort
-- exit.
example {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.alloc = some d) {T : Region}
    (hT : T.OK) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int))
    (lab : String → Int64) (ms : MemSide Kraken.Promising.X64.isa) (q : X64.Alloc.Call)
    (lbl : WeakMem.AllocLabel → Option Nat) :=
  let h := alloc_fits hd hT hhi hlo lab ms q lbl
  @X64.Alloc.seg_alloc (R := routineR T (X64.Alloc.N lab ms q .e).o.sp (-160) 8)
    (hR := h.1.1) (hlo := h.1.2.1) (hhi := h.1.2.2.1)
example {d : Nat} (hd : rtDepth.lookup Scc.Lower.Names.alloc = some d) {T : Region}
    (hT : T.OK) (hhi : 0 ≤ T.hi) (hlo : T.lo ≤ -(d : Int))
    (lab : String → Int64) (ms : MemSide Kraken.Promising.X64.isa) (q : X64.Alloc.Call)
    (lbl : WeakMem.AllocLabel → Option Nat) :=
  let h := alloc_fits hd hT hhi hlo lab ms q lbl
  @X64.Abort.Disp.seg_abort
    (R := abortAt (routineR T (X64.Alloc.N lab ms q .e).o.sp (-160) 8) (X64.Alloc.E lab ms q lbl .abort).o.sp)
    (hR := h.2.2.1) (hlo := h.2.2.2.1) (hhi := h.2.2.2.2.1)

end Spike.Lib.RtDepthX64.Test
