/-
**The heap abort path's state facts lift to `ownGXW`** (x86-64): the
producer of `StartH0C.HabLft`, the premise `wake_hab_closed`,
`Land5.inv0_of_habW`, `StartH0B.hst0_W` and `LandU.hland_RU` carry.

- `hpathW_noW`: no write at any node of the heap abort path
  (`Abort.Disp.HPathW`; the dispatcher's blocks at code 2, the heap stub's
  nodes), from `blkW_noW`, `nodeW_noW_si`, `nodeW_noW_sys`.
- `hpathW_lft2`: `Lft2` at every node of the heap abort path from `AbP`
  there and at the successors (`AbPH`), no write (`hpathW_noW`) and the
  appended words at every `AbP` state (`hcls`), by `cstOk_of`.
- `bandIn_topAb`: the dispatcher's band `[-32, 8]` below `wc_main`'s frame
  at the first stack's top (`(wR (RS wcLsw (topS L 0)) wcD).callee (-248)
  (-24) 16`) is on the stack pool.
- `raAb_ne_x23`: the heap abort's return address is not `.Lwc_main.x23`.
- `cst_abH`: on the heap path in a band on the pool, main's word only
  (`selfOwn` from the pool above `.x1`; `selfOwnW` false, the return
  address not `.x23`).
- `habLft_W`: `HabLft` at `ofPlaceWX`.

The threads path's counterpart is `X64WakeRefLft` (`tpathW_noW`,
`tpathW_lft2`, `cst_x23`, `bandIn_pre`, `refLft`), whose node producers
(`NoW`, `blkW_noW`, `nodeW_noW_si`, `nodeW_noW_sys`) are used here.

No AArch64 counterpart: A64's level owns `ownG`, so its heap abort path
needs no lift (`StartH0C.HabLft` is x86-64's). Unlike the threads path,
the worker's word is not held here (`ownSW = []`: the return address is
`raAb`, past `scc_rt_alloc`'s full branch, not `.x23`).
-/
import Spike.Lib.X64WakeRefLft
import Spike.Lib.X64WakeStartH0C

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open SccCode (wakeCells)
open Spike.Lib (Region)
open Spike.Lib.X64 (BlkW NodeW ND At)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Abort.Disp (HPathW)
open Spike.Lib.X64.Flow.WakeM (wR)
open Spike.Lib.X64.Flow.WakeWc (raAb)
open Spike.Lib.X64.WakePh.MainGlue (RS topS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)

/-- **`NoW` at every node of the heap abort path**, in a region covering
the dispatcher's and the stub's frames `[-24, 16)`. -/
theorem hpathW_noW {L : RuntimeLayout} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    {ra : BitVec 64} (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hd : Abort.Disp.Code c0 L.exe endPc) (hs : Abort.Code Abort.heap c0 Abort.x1Heap L.exe endPc) :
    HPathW NoW (fun _ _ => False) L.exe endPc R F c0 ra :=
  ⟨blkW_noW hd.e Abort.Disp.d0_ok hR (by omega) (by omega),
    blkW_noW hd.t1 Abort.Disp.t1_ok hR (by omega) (by omega),
    blkW_noW hd.j1 Abort.Disp.j1_ok hR (by omega) (by omega),
    blkW_noW hd.t2 Abort.Disp.t2_ok hR (by omega) (by omega),
    blkW_noW hd.g2 Abort.Disp.g2_ok hR (by omega) (by omega),
    blkW_noW hs.e Abort.x0_ok hR (by omega) (by omega),
    nodeW_noW_si fun s _ ⟨he, hn, _, hp, _⟩ => (hs.n1 s he hn).cell0 rfl rfl hp,
    blkW_noW hs.n2 Abort.x1Heap_ok hR (by omega) (by omega),
    nodeW_noW_sys fun s _ ⟨he, hn, _, hp, _⟩ => (hs.sys s he hn).cell0 rfl rfl hp,
    blkW_noW hs.n5 Abort.x2_ok hR (by omega) (by omega),
    nodeW_noW_sys fun s _ ⟨he, hn, _, hp, _⟩ => (hs.ex s he hn).cell0 rfl rfl hp⟩

/-- **`Lft2` at every node of the heap abort path**: `AbP` there and at the
successors (`hP`, `abPH`'s), no write (`hpathW_noW`), the appended words
`c1`, `c2` at every `AbP` state (`hcls`), `tcbM` off `ownG`'s words (`hs`,
`ha`) and `tcb2` off `ownGX`'s (`hW`). -/
theorem hpathW_lft2 {Λ : Scc.Sem.Layout} {Dt : State → Prop} {L : RuntimeLayout} {a : BitVec 64}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    {c1 c2 : List (Loc × Val)}
    (hs : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hP : AbPH L (Spike.Lib.X64.PhRec.μ L) endPc R F c0 ra)
    (hd : Abort.Disp.Code c0 L.exe endPc) (hst : Abort.Code Abort.heap c0 Abort.x1Heap L.exe endPc)
    (hcls : ∀ s, AbP L R ra s → Cst L c1 c2 s) :
    HPathW (Lft2 Λ L a Dt) (fun _ _ => False) L.exe endPc R F c0 ra := by
  have h := Spike.Lib.X64.Abort.Disp.HPathW.and
    (W₁ := AbW L R ra (Spike.Lib.X64.PhRec.μ L))
    ⟨hP.de, hP.dt1, hP.dj1, hP.dt2, hP.dg2, hP.se, hP.sn1, hP.sn2, hP.ssvc, hP.sn5, hP.sex⟩
    (hpathW_noW (ra := ra) (F := F) hR hlo hhi hd hst) fun s c h₁ h₂ => And.intro h₁ h₂
  exact HPathW.map h fun s _ hw h' =>
    h'.liftX (cstOk_of hs ha hW (hcls s hw.1.1) (fun s' hs' => hcls s' (hw.1.2 s' hs'))
      (fun hns tree he => hw.2 hns tree he _))

/-- **The dispatcher's band below `wc_main`'s frame at the top is on the
pool**: the callee's `[-32, 8]` at the frame's `[-280, -240]`. -/
theorem bandIn_topAb (L : RuntimeLayout) :
    BandIn L ((wR (RS wcLsw (topS L 0#64)) wcD).callee (-240 - 8) (-24) 16) := by
  intro k h1 h2
  rw [Region.callee_addr]
  have h := Spike.Lib.X64.WakePh.WcWfR.top_addr L (k := -240 - 8 + k) (by omega) (by omega)
  obtain ⟨hs1, hs2⟩ := L.stacks_sub
  simp only at hs1 hs2
  omega

/-- The heap abort's return point (`.Lscc_rt_alloc.full` plus `12`) lies
below `.Lwc_main.x23` in wake's code at `lo`. -/
def raAbChk : Bool :=
  match codeLabel lo wakeCells ".Lscc_rt_alloc.full", codeLabel lo wakeCells ".Lwc_main.x23" with
  | some x, some y => decide (x + 12 < y ∧ y < 2 ^ 63)
  | _, _ => false

theorem raAbChk_true : raAbChk = true := by
  unfold raAbChk; simp only [← codeT_eq]; decide +kernel

/-- **The heap abort's return address is not `.Lwc_main.x23`'s.** -/
theorem raAb_ne_x23 {L : RuntimeLayout}
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    raAb L.lab ≠ (L.lab ".Lwc_main.x23").toBitVec := by
  have h := raAbChk_true
  unfold raAbChk at h
  split at h
  · next x y hx hy =>
    have hxy := of_decide_eq_true h
    rw [raAb, hlab _ _ hx, hlab _ _ hy]
    intro he
    have := congrArg BitVec.toNat he
    simp only [Int64.toBitVec_add, BitVec.toNat_add] at this
    have e1 : (Int64.ofNat x).toBitVec.toNat = x := by simp [Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)]
    have e2 : (Int64.ofNat y).toBitVec.toNat = y := by simp [Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega)]
    have e3 : BitVec.toNat (12 : Int64).toBitVec = 12 := rfl
    rw [e1, e2, e3, Nat.mod_eq_of_lt (by omega)] at this
    omega
  · cases h

/-- **Main's word only on the heap path** in a band on the pool, from a
caller other than `.x23`: `selfOwn` (on the pool, `scc_rt_abort` above
`.x1`), not `selfOwnW` (`scc_rt_abort` is past `scc_rt_stack_take` and
before `.Lwc_main.x21`, the return address not `.x23`). -/
theorem cst_abH {L : RuntimeLayout} (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    {R : Region} {ra : BitVec 64} (hb : BandIn L R) (h23 : ra ≠ (L.lab ".Lwc_main.x23").toBitVec) {s : State}
    (h : AbP L R ra s) : Cst L (tM L) [] s := by
  have hx1 := Spike.Lib.X64.WakeRefAbW.lab_lt hlab (l₁ := ".Lscc_rt_start.x1") (l₂ := "scc_rt_abort")
    (by unfold Spike.Lib.X64.WakeRefAbW.labLt; rw [← codeT_eq]; decide +kernel)
  have hst := Spike.Lib.X64.WakeRefAbW.lab_lt hlab (l₁ := "scc_rt_stack_take") (l₂ := "scc_rt_abort")
    (by unfold Spike.Lib.X64.WakeRefAbW.labLt; rw [← codeT_eq]; decide +kernel)
  have hw21 := Spike.Lib.X64.WakeRefAbW.lab_lt hlab (l₁ := "scc_rt_thr_worker") (l₂ := ".Lwc_main.x21")
    (by unfold Spike.Lib.X64.WakeRefAbW.labLt; rw [← codeT_eq]; decide +kernel)
  have hin := h.1
  unfold inPc at hin
  refine ⟨ownS_of_self (.inl ⟨spPool_of_band hb h.2.2.2, by omega⟩), ownSW_of_not ?_⟩
  rintro (⟨-, -, h'⟩ | h' | ⟨-, h'⟩)
  · omega
  · unfold inPc at h'; omega
  · exact h23 ((raAt_iff h _).1 h').symm

end Spike.Lib.X64.WakePh

namespace Spike.Lib.X64.WakeHabLft

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (lo)
open SccCode (wakeCells)
open Spike.Lib.X64.Flow.WakeM (wR)
open Spike.Lib.X64.Flow.WakeWc (raAb)
open Spike.Lib.X64.WakePh.MainGlue (RS topS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`HabLft` at `ofPlaceWX`**: `Lft2` at every node of the heap abort path
(`hpathW_lft2`) below `wc_main`'s frame at the first stack's top, main's
word only there (`cst_abH`, the band `bandIn_topAb`), `ownGXW`'s
separations from the layout and A13's data part (`hA13`). -/
theorem habLft_W {asm : Asm} (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = lo) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    Spike.Lib.X64.WakePh.StartH0C.HabLft (Ly) := by
  intro F c0
  have hprog := Spike.Lib.X64.WakeSrcCtl.prog_W hp i hpa hwp
  have hL : Scc.Cert.Rt.X64.Lays (Ly).exe wakeCells (Ly).pfx := hprog ▸ (Ly).lays
  have hab := SccCode.wake_abort
  have hdi : Scc.Cert.Rt.X64.Abort.dispIn wakeCells = true := by
    have h := hab; simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at h; exact h.2
  have hlab := Spike.Lib.X64WakeOAb.hlab_W hp i hpa hwp hlo0
  have hlo := Spike.Lib.X64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hsite := Spike.Lib.X64.WakePh.siteW hprog hlo hlab
  have hwf := Spike.Lib.PlaceWX.wf_link_of_placeWX i hp
  obtain ⟨hR0, -⟩ := Spike.Lib.X64.WakePh.WcWfR.top_ok (Ly) hwf ({} : MachineData)
    { regs := ({} : MachineData).regs, zmms := ({} : MachineData).zmms, status := ({} : MachineData).status,
      slot := fun _ => 0#64 }
  have hR : ((wR (RS wcLsw (topS (Ly) 0#64)) wcD).callee (-240 - 8) (-24) 16).OK :=
    Region.callee_ok hR0 (by show -wcD ≤ -240 - 8 + -24; decide) (by decide) (by show (-240 - 8 : Int) < 8; decide)
      (by show (-240 - 8 + 16 : Int) ≤ 8; decide)
  have hRlo : ((wR (RS wcLsw (topS (Ly) 0#64)) wcD).callee (-240 - 8) (-24) 16).lo ≤ -24 := by
    simp [Region.callee]
  have hRhi : 16 ≤ ((wR (RS wcLsw (topS (Ly) 0#64)) wcD).callee (-240 - 8) (-24) 16).hi := by
    simp [Region.callee]
  have hend : (Ly).endPc = Scc.Cert.Rt.X64.endOf (Ly).exe wakeCells (Ly).pfx := by
    show Scc.Cert.Rt.X64.endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  have hd := Scc.Cert.Rt.X64.Abort.code_disp hL hend hdi (c0 := c0)
  have hst := Scc.Cert.Rt.X64.Abort.code_stubs hL hend hab .heap (c0 := c0)
  exact Spike.Lib.X64.WakePh.hpathW_lft2 (Spike.Lib.X64.WakePh.tcbSep_W hp i)
    (Spike.Lib.X64.WakePh.tcbM_ne_ntA_W hp i hA13) (Spike.Lib.X64.WakePh.tcb2_notG_W hp i hA13) hR hRlo hRhi
    (Spike.Lib.X64.WakePh.abPH_wake (L := Ly) (μ' := Spike.Lib.X64.PhRec.μ (Ly)) (F := F) (c0 := c0)
      (ra := raAb (Ly).lab) hprog hlo hsite hlab hsite hR hRlo hRhi) hd hst
    fun _ h => Spike.Lib.X64.WakePh.cst_abH hlab (Spike.Lib.X64.WakePh.bandIn_topAb (Ly))
      (Spike.Lib.X64.WakePh.raAb_ne_x23 hlab) h

end Spike.Lib.X64.WakeHabLft

/-- info: 'Spike.Lib.X64.WakePh.hpathW_noW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.hpathW_noW

/-- info: 'Spike.Lib.X64.WakePh.hpathW_lft2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.hpathW_lft2

/-- info: 'Spike.Lib.X64.WakePh.bandIn_topAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.bandIn_topAb

/-- info: 'Spike.Lib.X64.WakePh.raAb_ne_x23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.raAb_ne_x23

/-- info: 'Spike.Lib.X64.WakePh.raAbChk_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.raAbChk_true

/-- info: 'Spike.Lib.X64.WakePh.cst_abH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.cst_abH

/-- info: 'Spike.Lib.X64.WakeHabLft.habLft_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeHabLft.habLft_W
