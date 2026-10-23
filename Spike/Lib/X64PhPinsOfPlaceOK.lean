/-
**The atomic accesses' phases from `placeOK`** (x86-64): at the runtime's
layout of an output passing `placeOK` (`RuntimeLayout.ofPlaceOK`), the
phase index (`PhRec.ph`, A6's `phOf`) at the runtime's three atomic
accesses whose owned counters the start segment reads, from A6's runtime
phase table (`rtPh_of_placeOKAt`, `Spike/Lib/Rt/X64RtPhTab.lean`'s `.ph` rows):

- `hphT_ofPlaceOK`: `scc_rt_alloc_tcb`'s `lock xadd` (`AllocTcb.rmwPc`,
  `.len` + 158) at `13`;
- `hphL_ofPlaceOK`: `scc_rt_stack_take`'s `xchg` (`StackTake.swpPc`,
  `.spin14` + 11) at `12`;
- `hphN_ofPlaceOK`: `scc_rt_stack_take`'s store of `scc_rt_stack_next`
  (`StackTake.nextPc`, `.bump` + 56) at `12`;
- the other ends, at the label plus the byte offset: `hphT1_ofPlaceOK`
  (`.len` + 163, `12`), `hphL1_ofPlaceOK` (`.spin14` + 14, `14`),
  `hphU0_ofPlaceOK`/`hphU1_ofPlaceOK` (the lock's release `.bump` + 28,
  `14`, then `.bump` + 31, `12`), `hphN1_ofPlaceOK` (`.bump` + 61, `8`),
  `hphS0_ofPlaceOK`/`hphS1_ofPlaceOK` (the take site, `8` then `0`).

`ph_of_rtPh` gives any `.ph` row of the table the same way.
-/
import Spike.Lib.X64PhRec
import Spike.Lib.Rt.X64RtPhTab
import Spike.Lib.Rt.X64RtPhOfTab

namespace Spike.Lib.X64.PhRec

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Link.X64 (linkOf)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

set_option hygiene false in
/-- The layout of `ofPlaceOK`. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

/-- **A `.ph` row of the runtime's phase table** (`rtPhTab none`) gives its
phase index at its label plus its byte offset. -/
theorem ph_of_rtPh {l : String} {off v : Nat} (hf : .ph l off v ∈ Spike.Lib.X64.Rt.rtPhTab none) :
    ph Ly ((Ly).lab l + Int64.ofNat off).toBitVec.toNat = v := by
  haveI : Kraken.Executable.ValidLayout (Scc.Sem.X64.threadAt Scc.Sem.Entry.linux (Λ).code.lo
      o.prog (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).exe :=
    (RuntimeLayout.ofPlaceOK h i).valid
  exact Spike.Lib.X64.Rt.PhOfTab.ph_of_factOk (lab := (Ly).lab) (fun _ _ ha =>
    Scc.Cert.Rt.X64.label_threadAt_of_codeLabel (E := Scc.Sem.Entry.linux)
      (syms := Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)
          (by exact Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK_above h i) ha)
    (Scc.Cert.Rt.X64.factOk_of_rtPhOk (rtPh_of_placeOKAt h) hf)

/-- **The counter's `lock xadd` in `scc_rt_alloc_tcb`** is at phase `13`. -/
theorem hphT_ofPlaceOK : ph Ly (Spike.Lib.X64.Flow.Ret0.AllocTcb.rmwPc (Ly).lab).toBitVec.toNat = 13 :=
  ph_of_rtPh h i (by simp [Spike.Lib.X64.Rt.rtPhTab, Spike.Lib.X64.Rt.tcbPhTab])

/-- **The lock's `xchg` in `scc_rt_stack_take`** is at phase `12`. -/
theorem hphL_ofPlaceOK : ph Ly (Spike.Lib.X64.Flow.Ret0.StackTake.swpPc (Ly).lab).toBitVec.toNat = 12 :=
  ph_of_rtPh h i (by simp [Spike.Lib.X64.Rt.rtPhTab, Spike.Lib.X64.Rt.takePhTab])

/-- **`scc_rt_stack_next`'s store in `scc_rt_stack_take`** is at phase `12`. -/
theorem hphN_ofPlaceOK : ph Ly (Spike.Lib.X64.Flow.Ret0.StackTake.nextPc (Ly).lab).toBitVec.toNat = 12 :=
  ph_of_rtPh h i (by simp [Spike.Lib.X64.Rt.rtPhTab, Spike.Lib.X64.Rt.takePhTab])

/-- **After the counter's `lock xadd`** is at phase `12`. -/
theorem hphT1_ofPlaceOK : ph Ly ((Ly).lab Spike.Lib.X64.Rt.Code.Tcb.lenL + Int64.ofNat 163).toBitVec.toNat = 12 :=
  ph_of_rtPh h i (by simp [Spike.Lib.X64.Rt.rtPhTab, Spike.Lib.X64.Rt.tcbPhTab])

/-- **After the lock's `xchg` (the lock held)** is at phase `14`. -/
theorem hphL1_ofPlaceOK : ph Ly ((Ly).lab Spike.Lib.X64.Rt.Code.Take.spinL + Int64.ofNat 14).toBitVec.toNat = 14 :=
  ph_of_rtPh h i (by simp [Spike.Lib.X64.Rt.rtPhTab, Spike.Lib.X64.Rt.takePhTab])

/-- **The lock's release** is at phase `14`. -/
theorem hphU0_ofPlaceOK : ph Ly ((Ly).lab Spike.Lib.X64.Rt.Code.Take.bumpL + Int64.ofNat 28).toBitVec.toNat = 14 :=
  ph_of_rtPh h i (by simp [Spike.Lib.X64.Rt.rtPhTab, Spike.Lib.X64.Rt.takePhTab])

/-- **After the lock's release** is at phase `12`. -/
theorem hphU1_ofPlaceOK : ph Ly ((Ly).lab Spike.Lib.X64.Rt.Code.Take.bumpL + Int64.ofNat 31).toBitVec.toNat = 12 :=
  ph_of_rtPh h i (by simp [Spike.Lib.X64.Rt.rtPhTab, Spike.Lib.X64.Rt.takePhTab])

/-- **After `scc_rt_stack_next`'s store** is at phase `8`. -/
theorem hphN1_ofPlaceOK : ph Ly ((Ly).lab Spike.Lib.X64.Rt.Code.Take.bumpL + Int64.ofNat 61).toBitVec.toNat = 8 :=
  ph_of_rtPh h i (by simp [Spike.Lib.X64.Rt.rtPhTab, Spike.Lib.X64.Rt.takePhTab])

/-- **The take site** is at phase `8`. -/
theorem hphS0_ofPlaceOK : ph Ly ((Ly).lab Spike.Lib.X64.Rt.Code.Take.siteL + Int64.ofNat 0).toBitVec.toNat = 8 :=
  ph_of_rtPh h i (by simp [Spike.Lib.X64.Rt.rtPhTab, Spike.Lib.X64.Rt.takePhTab])

/-- **After the take site** is at phase `0`. -/
theorem hphS1_ofPlaceOK : ph Ly ((Ly).lab Spike.Lib.X64.Rt.Code.Take.siteL + Int64.ofNat 1).toBitVec.toNat = 0 :=
  ph_of_rtPh h i (by simp [Spike.Lib.X64.Rt.rtPhTab, Spike.Lib.X64.Rt.takePhTab])

end Place

end Spike.Lib.X64.PhRec
