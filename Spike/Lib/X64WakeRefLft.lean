/-
**`RefLft`: `SFactsSt2` at `ownG` lifting to `ownGXW` on the threads abort
path** (x86-64, wake.w; no A64 counterpart): `Lft2` at every node of the
dispatcher at code `5` and the threads stub, below main's frame, entered
from `.Lwc_main.spawnfail5`'s `call` (the return address `.Lwc_main.x23`).
On that path main holds both TCB words: `tcbM` (on the pool from `.x1` on,
`selfOwn`) and `tcb2` (in `scc_rt_abort`'s code with the return address
`.x23`, `selfOwnW`), and no instruction of the path writes memory.

- `NoW`: the state's instruction writes nothing (any write condition);
  `blkW_noW` (a covered block, `exec_ai`), `nodeW_noW_si` (a `leaq`),
  `nodeW_noW_sys` (a `syscall`, at a system call).
- `tpathW_noW`: `NoW` at every node of the path.
- `tpathW_lft2`: `Lft2` at every node of the path from the class of its
  states (`hcls`: `Cst` at every `AbP` state), the separations of `ownGXW`'s
  words; shared with the heap abort's twin.
- `bandIn_pre`: the dispatcher's band `[-32, 8]` lies in the first stack,
  from `Pre` (`R.base + 64` 64 bytes below its top).
- `cst_x23`: `Cst L (tM L) (tW L)` on the path from `.x23` in a band on the
  pool.
- `refLft`: `RefLft` from the parses, the code base and A13's data part.
-/
import Spike.Lib.X64WakeRefAbW
import Spike.Lib.X64WakeOwnSW
import Spike.Lib.X64WakeOwnT2W
import Spike.Lib.X64WakeRefLay

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open SccCode (wakeCells)
open Spike.Lib (Region)
open Spike.Lib.X64 (BlkW NodeW ND CodeAt okBlk arun cellOff Abs At SI)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakeRefTP (TPathW)
open Kraken.Promising.Lower.X64 (CellAt)

/-! ## No writes on the path -/

/-- **The state's instruction writes nothing**: any write condition holds
off a system call. -/
def NoW : Spike.Lib.Frag isa :=
  fun s _ => abi.atSys s = false → ∀ tree, isa.exec s = some tree → ∀ G, WriteTree G tree

section Nodes

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A covered block writes nothing** (`exec_ai`). -/
theorem blkW_noW {n : ND} {blk : List (Directive × Nat)} {blo bhi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi) :
    BlkW NoW (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ _ k hk m hA' _
  refine ⟨fun _ tree hex G => ?_, fun _ h => h⟩
  obtain ⟨a, hca, haok, -⟩ :=
    Spike.Lib.X64.okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := Spike.Lib.X64.classify_sound hca
  have hd' : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hc : CellAt { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } a.toDir blk[k].2 :=
    (hcode s he hn).cell (j := k) (d := a.toDir) (z := blk[k].2) (by rw [hd', ← hdir]) rfl rfl rfl
  obtain ⟨m', hex', -⟩ := Spike.Lib.X64.exec_ai haok hR hlo hhi hc hreg hA'
  rw [hex'] at hex
  cases hex
  trivial

/-- **A `leaq` node writes nothing.** -/
theorem nodeW_noW_si {n : ND} {si : SI} {z : Nat}
    (hc : ∀ s c, At exe endPc R F n s c → CellAt s si.toDir z) :
    NodeW NoW (fun _ _ => False) exe endPc R F n := fun s c hAt =>
  ⟨fun _ tree he _ => by rw [Spike.Lib.X64.exec_si (hc s c hAt)] at he; cases he; trivial, fun _ h => h⟩

/-- **A `syscall` node writes nothing** off a system call: it is at one. -/
theorem nodeW_noW_sys {n : ND} {z : Nat}
    (hc : ∀ s c, At exe endPc R F n s c → CellAt s (Kraken.Promising.Lower.X64.op64 .syscall) z) :
    NodeW NoW (fun _ _ => False) exe endPc R F n := fun s c hAt =>
  ⟨fun hs => Bool.noConfusion ((Scc.Sem.X64.atSyscall_of_cellAt (hc s c hAt)).symm.trans hs), fun _ h => h⟩

end Nodes

/-- **`NoW` at every node of the threads abort path**, in a region covering
the dispatcher's and the stub's frames `[-24, 16)`. -/
theorem tpathW_noW {L : RuntimeLayout} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    {ra : BitVec 64} (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hd : Abort.Disp.Code c0 L.exe endPc) (hs : Abort.Code Abort.threads c0 Abort.x1Threads L.exe endPc) :
    TPathW NoW (fun _ _ => False) L.exe endPc R F c0 ra :=
  ⟨blkW_noW hd.e Abort.Disp.d0_ok hR (by omega) (by omega),
    blkW_noW hd.t1 Abort.Disp.t1_ok hR (by omega) (by omega),
    blkW_noW hd.j1 Abort.Disp.j1_ok hR (by omega) (by omega),
    blkW_noW hd.t2 Abort.Disp.t2_ok hR (by omega) (by omega),
    blkW_noW hd.j2 Abort.Disp.j2_ok hR (by omega) (by omega),
    blkW_noW hd.t3 Abort.Disp.t3_ok hR (by omega) (by omega),
    blkW_noW hd.j3 Abort.Disp.j3_ok hR (by omega) (by omega),
    blkW_noW hd.t4 Abort.Disp.t4_ok hR (by omega) (by omega),
    blkW_noW hd.j4 Abort.Disp.j4_ok hR (by omega) (by omega),
    blkW_noW hd.t5 Abort.Disp.t5_ok hR (by omega) (by omega),
    blkW_noW hd.g5 Abort.Disp.g5_ok hR (by omega) (by omega),
    blkW_noW hs.e Abort.x0_ok hR (by omega) (by omega),
    nodeW_noW_si fun s _ ⟨he, hn, _, hp, _⟩ => (hs.n1 s he hn).cell0 rfl rfl hp,
    blkW_noW hs.n2 Abort.x1Threads_ok hR (by omega) (by omega),
    nodeW_noW_sys fun s _ ⟨he, hn, _, hp, _⟩ => (hs.sys s he hn).cell0 rfl rfl hp,
    blkW_noW hs.n5 Abort.x2_ok hR (by omega) (by omega),
    nodeW_noW_sys fun s _ ⟨he, hn, _, hp, _⟩ => (hs.ex s he hn).cell0 rfl rfl hp⟩

/-- **`Lft2` at every node of the threads abort path**: `AbP` there and at
the successors (`abPT`), no write (`tpathW_noW`), the appended words `c1`,
`c2` at every `AbP` state (`hcls`), `tcbM` off `ownG`'s words (`hs`, `ha`)
and `tcb2` off `ownGX`'s (`hW`). -/
theorem tpathW_lft2 {Λ : Scc.Sem.Layout} {Dt : State → Prop} {L : RuntimeLayout} {a : BitVec 64}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    {c1 c2 : List (Loc × Val)}
    (hs : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hsite : ∀ a, (Spike.Lib.X64.PhRec.μ L).site .take = some a →
      a < (L.lab "scc_rt_abort").toBitVec.toNat ∨ (L.lab "scc_rt_thr_worker").toBitVec.toNat ≤ a)
    (hd : Abort.Disp.Code c0 L.exe endPc) (hst : Abort.Code Abort.threads c0 Abort.x1Threads L.exe endPc)
    (hcls : ∀ s, AbP L R ra s → Cst L c1 c2 s) :
    TPathW (Lft2 Λ L a Dt) (fun _ _ => False) L.exe endPc R F c0 ra := by
  have h := TPathW.and (TPathW.ofAbPT (abPT (μ := Spike.Lib.X64.PhRec.μ L) (F := F) hlab hR hlo hhi hsite hd hst))
    (tpathW_noW (ra := ra) (F := F) hR hlo hhi hd hst) fun s c h₁ h₂ => And.intro h₁ h₂
  exact TPathW.mapWK h fun s _ hw _ =>
    ⟨fun h' => h'.liftX (cstOk_of hs ha hW (hcls s hw.1.1) (fun s' hs' => hcls s' (hw.1.2 s' hs'))
      (fun hns tree he => hw.2 hns tree he _)), fun _ h => h⟩

/-! ## The class on the path from `.x23` -/

/-- **The dispatcher's band on the first stack** from `Pre`'s region:
`R.base + 64` at the first stack's top, the callee's `[-32, 8]` at `R`'s
`[-112, -72]`. -/
theorem bandIn_pre {L : RuntimeLayout} {R : Region} (hR : R.OK) (hlo : R.lo ≤ -320) (hhi : 16 ≤ R.hi)
    (hb : R.base.toNat + 64 = L.stacksA.toNat + 16384) : BandIn L (R.callee (-72 - 8) (-24) 16) := by
  intro k h1 h2
  obtain ⟨hs1, hs2⟩ := L.stacks_sub
  simp only at hs1 hs2
  have he : (R.callee (-72 - 8) (-24) 16).addr k = R.addr (-72 - 8 + k) := by
    simp only [Region.callee, Region.addr_add]; rfl
  rw [he]
  have e := Region.addr_toNat_of hR (k := -72 - 8 + k) (by omega) (by omega)
  omega

/-- **Both TCB words on the path from `.x23`** in a band on the pool:
`selfOwn` (on the pool, `scc_rt_abort` above `.x1`) and `selfOwnW` (in
`scc_rt_abort`'s code with the return address `.x23`). -/
theorem cst_x23 {L : RuntimeLayout} (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    {R : Region} (hb : BandIn L R) {s : State} (h : AbP L R (L.lab ".Lwc_main.x23").toBitVec s) :
    Cst L (tM L) (tW L) s := by
  have hx1 := Spike.Lib.X64.WakeRefAbW.lab_lt hlab (l₁ := ".Lscc_rt_start.x1") (l₂ := "scc_rt_abort")
    (by unfold Spike.Lib.X64.WakeRefAbW.labLt; rw [← codeT_eq]; decide +kernel)
  exact ⟨ownS_of_self (.inl ⟨spPool_of_band hb h.2.2.2, by have := h.1.1; omega⟩),
    ownSW_of_self (.inr (.inr ⟨h.1, (raAt_iff h _).2 rfl⟩))⟩

end Spike.Lib.X64.WakePh

namespace Spike.Lib.X64.WakeRefLft

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (lo)
open SccCode (wakeCells)
open Spike.Lib.X64.WakeRefStub (Pre RefLft callee_of_pre)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`RefLft`**: `Lft2` at every node of the threads abort path
(`tpathW_lft2`), both TCB words held there (`cst_x23`, the band from `Pre`),
`ownGXW`'s separations from the layout and A13's data part (`hA13`). -/
theorem refLft {asm : Asm} (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = lo) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (l : WeakMem.AllocLabel) (b : Nat) : RefLft hp i l b := by
  intro R m0 cP cA mT m1 σC c0 hpre _
  obtain ⟨hR', hlo', hhi'⟩ := callee_of_pre hp i hpre
  obtain ⟨-, -, -, hR, hRlo, hRhi, hbase⟩ := hpre
  have hprog := Spike.Lib.X64.WakeSrcCtl.prog_W hp i hpa hwp
  have hL : Scc.Cert.Rt.X64.Lays (Ly).exe wakeCells (Ly).pfx := hprog ▸ (Ly).lays
  have hab := SccCode.wake_abort
  have hdi : Scc.Cert.Rt.X64.Abort.dispIn wakeCells = true := by
    have h := hab; simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at h; exact h.2
  have hlab := Spike.Lib.X64WakeOAb.hlab_W hp i hpa hwp hlo0
  have hb := Spike.Lib.X64.WakePh.bandIn_pre (L := Ly) hR hRlo hRhi hbase
  have hra := Spike.Lib.X64.WakeRefStub.raT_x23 hlab
  show Spike.Lib.X64.WakeRefTP.TPathW _ _ _ _ _ _ _ (Spike.Lib.X64.ThreadsAb.raT (Ly).lab ".Lwc_main")
  rw [hra]
  exact Spike.Lib.X64.WakePh.tpathW_lft2 (Spike.Lib.X64.WakePh.tcbSep_W hp i)
    (Spike.Lib.X64.WakePh.tcbM_ne_ntA_W hp i hA13) (Spike.Lib.X64.WakePh.tcb2_notG_W hp i hA13) hlab
    hR' (by omega) (by omega)
    (Spike.Lib.X64.WakeRefAbW.site_out hp i hprog (Spike.Lib.X64.WakePh.StartPlaceLy.hlo_W hp i hlo0) hlab)
    (Scc.Cert.Rt.X64.Abort.code_disp hL rfl hdi) (Scc.Cert.Rt.X64.Abort.code_stubs hL rfl hab .threads)
    fun _ h => Spike.Lib.X64.WakePh.cst_x23 hlab hb h

end Spike.Lib.X64.WakeRefLft

/-- info: 'Spike.Lib.X64.WakePh.tpathW_noW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tpathW_noW

/-- info: 'Spike.Lib.X64.WakePh.tpathW_lft2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tpathW_lft2

/-- info: 'Spike.Lib.X64.WakePh.bandIn_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.bandIn_pre

/-- info: 'Spike.Lib.X64.WakePh.cst_x23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.cst_x23

/-- info: 'Spike.Lib.X64.WakeRefLft.refLft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefLft.refLft
