/-
**hello.w's `wc_main` second `scc_rt_alloc_tcb` call block inside the global owned-words map on x86-64** (the twin
of `Spike/Lib/A64HelloTcb2CallW.lean`; wake's x86-64 version is `Spike/Lib/X64WakeTcb2CallW.lean`): the block
`HelloWc.tcb2CallH` at `.Lwc_main.x23` (`Spike/Lib/X64HelloWcSp3.lean`, `wc_main`'s frame `oWH`) inside
`SFactsSt2` at `ownGH` (`tcb2Call_ownGH`), proved at the first instance's constant owned words `ownH L a 16`
(wake's generic `blk_switch2`) and moved to `ownGH`, which picks them at the block's pcs (`phH = 16`) and at the
callee's entry on a pool stack (`own2aH (ph2aH 4199029)`, `own1_own2aH_ph`); and the callee's node obligations
at the outside move of any range (`tcb2W_ownGKH`, wake's `tcbWG_takeK`).

- `BandSp3H`: main's frame at `.x23` on a pool stack, `BandAH` of the callee's region `R.callee (-136) (-184) 8`.
- `sp3_factsH`, `lab_sp3H`, `own_sp3H`, `own_fnH`: `ownGH` is `ownH L a 16` at the block's pcs (`.x23` at
  `4203726`) and at the callee's entry.
- `tcb2Call_ownGH`, `tcb2W_ownGKH`: the results.

## Differences from the AArch64 version

- As wake's x86-64 version: the names keep A64's `sp3` though the block is at `.Lwc_main.x23`; the block has 4
  cells (`movq`, `movq`, `movq`, `call`; A64's 5), its pcs `.x23 + cellOff`; the callee's region is
  `R.callee (-136) (-184) 8` (based at the pushed return address, `oCH`; A64's `R.callee (-144) (-192) 0`); the
  block's bounds are `hlo3 : R.lo ≤ -136`, `hhi : 16 ≤ R.hi` (A64's `-144`, `0`); no `hal`; `tcb2W_ownGKH` takes
  `tcb2W_ownGH`'s x86-64 premises (`hlo' : R.lo ≤ -184`, `hhi : 8 ≤ R.hi`, the return to `.Lwc_main.x24`).
- `HelloWc.wcSp3InH` checks the block with `blockAt`; `blk_switch2` and `code_field` take `blockAtB`, decided
  here on `helloCells` directly.
-/
import Spike.Lib.X64HelloTcb2W
import Spike.Lib.X64WakeTcb2CallW

namespace Spike.Lib.X64.HelloPh.Tcb2CallW

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq code_field okPcOf)
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk)
open Spike.Lib.X64Consumer (Lbl CFacts)
open Spike.Lib.X64ConsumerA (StSucc SpAt SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW AS SO cellOff okBlk)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0 (TakeK StackM)
open Spike.Lib.X64.HelloPh
open Spike.Lib.X64.HelloPh.WcSp6 (oWH)
open Spike.Lib.X64.Flow.HelloWc (tcb2QH tcb2CallH tcb2CallH_ok tcb2CallH_pc wcN3H x23L)
open Spike.Lib.X64.HelloPh.Tcb2W (BandAH PcAH good2aH_of tcb_labsH)
open Spike.Lib.X64.WakePh.Tcb2CallW (blk_switch2 tcbWG_takeK)
open Spike.Lib.X64.WakePh (inPc)

/-! ### `ownGH` at the block's pcs and at the callee's entry -/

/-- **Main's frame at `.x23` on a pool stack**: `scc_rt_alloc_tcb`'s frame
`[-184, 8]` around `%rsp = R.addr (-136)` at its entry (`wc_main`'s region
`R`, its 128-byte frame and the pushed return address) in the pool's band.
`WcMid` supplies it from main's frame facts. -/
abbrev BandSp3H (L : RuntimeLayout) (R : Region) : Prop := BandAH L (R.callee (-136) (-184) 8)

/-- The block's pcs at the canonical base: their values, the phase `16`,
off the sites, at most 18 bytes on. -/
theorem sp3_factsH : ∀ k < 4,
    (Int64.ofNat 4203726 + Int64.ofNat (cellOff tcb2CallH k)).toBitVec.toNat = 4203726 + cellOff tcb2CallH k ∧
    phC (4203726 + cellOff tcb2CallH k) = 16 ∧ okC (4203726 + cellOff tcb2CallH k) = true ∧
    cellOff tcb2CallH k ≤ 18 := by decide +kernel

variable {L : RuntimeLayout}

/-- `.x23` at the canonical base. -/
theorem lab_sp3H (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label ".Lwc_main.x23" = Int64.ofNat 4203726 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

/-- **`ownGH` at the block's pcs** is `ownH L a 16` (no range of `ownGH`'s
holds, `phH = 16`). -/
theorem own_sp3H (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {s : State} {k : Nat} (hk : k < 4)
    (hs : s.st.2 = (_root_.Executable.labels L.exe).label ".Lwc_main.x23" + Int64.ofNat (cellOff tcb2CallH k)) :
    ownGH L a s = ownH L a 16 := by
  have hp : pcOf s = 4203726 + cellOff tcb2CallH k := by
    unfold pcOf; rw [hs, lab_sp3H hlab]; exact (sp3_factsH k hk).1
  have hc := (sp3_factsH k hk).2.2.2
  obtain ⟨e1, e2, e3, e4, e5, -, e7, e8, e9⟩ := labs_eqH hlab (L := L)
  rw [ownGH_W hlab (.inr (.inr ⟨?_, ?_, ?_, ?_⟩)), hp, phH_eq, (sp3_factsH k hk).2.1] <;> unfold inPc <;> omega

/-- **`ownGH` at the callee's entry**, `%rsp` at `R.addr (-136)` on a pool
stack: `own2aH (ph2aH 4199029)`, the first instance's `ownH L a 16`. -/
theorem own_fnH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {R : Region} (hb : BandSp3H L R) {s : State}
    (hs : s.st.2 = (_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.AllocTcb.fnL)
    (hsp : s.st.1.regs.rsp.toBitVec = R.addr (-136)) : ownGH L a s = ownH L a 16 := by
  obtain ⟨eFn, -, -, -, -, -⟩ := tcb_labsH hlab (L := L)
  have hp : pcOf s = 4199029 := by unfold pcOf; rw [hs, eFn]; rfl
  have hg := good2aH_of hlab hb (s := s) (by rw [hs, eFn]; decide)
    ⟨0, by decide, by decide, by rw [hsp, Region.callee_addr]; rfl⟩
  rw [ownGH_2a hlab hg, hp, ← own1_own2aH_ph, phH_eq, allocTcb2H_ph.1]

/-! ### The block -/

/-- **The second call's block at `.x23` inside `SFactsSt2` at `ownGH`**,
after the take (`hsub`, `hSM` at main's range `rS`), at the outside move of
any range `rS'`: `blk_switch2` at the first instance (`instOkH`, constant
`ownH L a 16`), `ownGH` agreeing there at the block's pcs (`own_sp3H`) and at
the callee's entry (`own_fnH`, main's frame on a pool stack `hb`). -/
theorem tcb2Call_ownGH (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    {Λ : Scc.Sem.Layout} {lbl : Lbl} {c0 : Ctl} (hC0 : CFacts Λ lbl c0) 
    {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64}
    {R : Region} (hR : R.OK) (hlo3 : R.lo ≤ -136) (hhi : 16 ≤ R.hi)
    (hb : BandSp3H L R) {F : MachineData → Prop} {rS : Range} (rS' : Range)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.X64.FStable R (StackM rS)) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS')
      L.exe L.endPc R (fun m => F m ∧ StackM rS m) (wcN3H L.lab c0 sl me cA fr) tcb2CallH := by
  obtain ⟨-, -, -, -, -, eSite⟩ := tcb_labsH hlab (L := L)
  have e3 := lab_sp3H hlab (L := L)
  have hin : Scc.Cert.Rt.X64.blockAtB L.prog x23L 0 tcb2CallH = true := hp ▸ (by decide +kernel)
  have hlen : tcb2CallH.length = 4 := by decide
  refine blk_switch2 (instOkH hp hlo a (fun _ => True) hsite (rS := rS')) (ownH L a 16) hin
    (ofNat_zero' _) tcb2CallH_ok hR hlo3 hhi (fun _ _ hJ => hJ.1 ▸ hC0) (by decide +kernel)
    (by decide +kernel) (fun k hk => ?_) hsub hSM ?_
  · show okPcOf lo helloCells L.Λ
      ((_root_.Executable.labels L.exe).label ".Lwc_main.x23" + Int64.ofNat (cellOff tcb2CallH k)).toBitVec.toNat
        = true
    rw [okPc_eq hΛ, e3, (sp3_factsH k (hlen ▸ hk)).1]; exact (sp3_factsH k (hlen ▸ hk)).2.2.1
  refine Spike.Lib.X64ConsumerA.BlkW.leaf (code_field L.lays rfl hin (ofNat_zero' _)) tcb2CallH_ok hR hlo3 hhi
    ?_ ?_ ?_
  · intro x hx k hk
    rw [hsite, show L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200314 from eSite] at hx
    cases hx
    show ((_root_.Executable.labels L.exe).label ".Lwc_main.x23" + Int64.ofNat (cellOff tcb2CallH k)).toBitVec.toNat
      ≠ _
    rw [e3, (sp3_factsH k (hlen ▸ hk)).1]
    have : (Int64.ofNat 4200314).toBitVec.toNat = 4200314 := rfl
    omega
  · intro σ c hJ k hk s m hA he hn hs
    exact own_sp3H hlab (hlen ▸ hk) (by rw [hs]; rfl)
  · intro σ c hJ k hk s m hA he hn hs
    rcases Nat.lt_or_ge (k + 1) 4 with hk1 | hk1
    · rw [Spike.Lib.X64.arun_pc _ tcb2CallH_ok (by rw [hlen]; exact hk1)] at hs
      exact own_sp3H hlab hk1 (by rw [hs]; rfl)
    · have ht : tcb2CallH.take (k + 1) = tcb2CallH := List.take_of_length_le (by omega)
      rw [ht] at hA hs
      obtain ⟨h1, h2⟩ := tcb2CallH_pc (_root_.Executable.labels L.exe).label
        ((_root_.Executable.labels L.exe).label ".Lwc_main.x23") σ
      refine own_fnH hlab hb (by rw [hs]; exact h1) ?_
      have e := Spike.Lib.X64ConsumerA.rsp_of_abs hA
      rw [show (wcN3H L.lab c0 sl me cA fr).pc = (_root_.Executable.labels L.exe).label ".Lwc_main.x23" from rfl,
        show (wcN3H L.lab c0 sl me cA fr).o = oWH from rfl, h2] at e
      rw [hs]; exact e

/-- **`tcb2W_ownGH` at the outside move of any range `rS'`** (`tcbWG_takeK`):
the callee's node obligations at `PhRec.K L rS'`, its frame condition still
main's range `rS`. -/
theorem tcb2W_ownGKH (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (a : BitVec 64) {rS : Range}
    (rS' : Range)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 80#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    {Λ : Scc.Sem.Layout} {lbl : Lbl} {c0 : Ctl} (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hlo' : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hb : BandAH L R) (g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G) (hra : g.ra = (L.lab ".Lwc_main.x24").toBitVec)
    {F : MachineData → Prop}
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true
      ⟨Spike.Lib.X64.Rt.hdrA L.lab (tcb2QH g c0), 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Rt.hdrA L.lab (tcb2QH g c0)) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.X64.FStable R (StackM rS)) :
    ∀ i, Spike.Lib.X64.Rt.TcbWG (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s)
      (Spike.Lib.X64.PhRec.K L rS') L.exe L.endPc R (fun m => F m ∧ StackM rS m) (tcb2QH g c0) i :=
  tcbWG_takeK (Tcb2W.tcb2W_ownGH hp hlo a hsite hΛ hlab hsep hhdr hC0 hR hlo' hhi hb g hra hmP hmH hunP hunH
    hsub hSM)

end Spike.Lib.X64.HelloPh.Tcb2CallW

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2CallW.sp3_factsH' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2CallW.sp3_factsH

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2CallW.lab_sp3H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2CallW.lab_sp3H

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2CallW.own_sp3H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2CallW.own_sp3H

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2CallW.own_fnH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2CallW.own_fnH

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2CallW.tcb2Call_ownGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2CallW.tcb2Call_ownGH

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2CallW.tcb2W_ownGKH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2CallW.tcb2W_ownGKH
