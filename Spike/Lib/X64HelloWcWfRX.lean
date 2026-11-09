/-
**hello.w's `wc_main` before the box's landing inside `WSHX`, guarded by the thread pointer** (x86-64 only; the
`ownGHXW` counterpart of `X64HelloWcWfR`'s `Gen` section): `WcPreWH` and `WcSp0WH` at `tpG t WSHX`, the
counter's context (`hctx`) and the box store's writes' obligation (`hwr`) owed only at states with thread pointer
`t`. The prologue, the entry block and `.x22`'s block are `X64HelloWcWfSX`'s (`proW_WSHX`, `eW_WSHX`,
`blkW_WSHX`) taken inside `tpG t`; the allocator is `HelloWf.allocW_WSHX_tp`; the box's store is
`WcWfSX.nodeW_WSHX` at the node guarded by `t` (wake's `WcWfR.nT`).

- `allocW_wcWSgHX`: the allocator at `wc_main`'s call inside `tpG t WSHX`.
- `wcPreW_WSgHX`: `wc_main` up to the allocator's return.
- `wcSp0W_WSgHX`: `.x22`'s block and the box's store.

## Differences from the AArch64 version

AArch64 has no counterpart at this level: main owns no TCB word there (AArch64 `A64HelloWcWfR` works at `WSH`).
- The level is `WSHX`; the producers take `ownGHXW`'s separation premises (`hsep`, `ha`, `hW`), the frame's band
  on the pool (`hb`, `hbd`), and the allocator's words and the box cells off `tcbM` (`hnoM`, `hboxM`).
- The thread pointer is `fsBase` (`KeepTP.TP`, `WakeTP.tpG`; AArch64 `TPIDR_EL0`); the prologue is `XProW`.
- `call` pushes the return address: `8 ≤ R.hi`, the allocator's region `wARH R = R.callee (-144) (-160) 8`; the
  bounds are x86-64's frame (`R.lo ≤ -136` for `.x22`, `-304` for the call).
- The allocator returns to `.Lwc_main.x0` (AArch64 `.L22_wc_main.sp0`); the box's store is at `.x22 + 15`.
-/
import Spike.Lib.X64HelloWcWfSX
import Spike.Lib.X64HelloWcWfR

namespace Spike.Lib.X64.HelloPh.WcWfRX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (BlkW NodeW At mB eaddr_mB agrees_of_decls)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.WakeWf (RunWf NoWrC)
open Spike.Lib.X64.WakePh.WcWfR (nT nodeW_nT nT_of_at nodeW_unTp)
open Spike.Lib.X64.WakePh.WcWfS (cf_hold)
open Spike.Lib.X64.HelloPh (lo ownH instOkH WSHX)
open Spike.Lib.X64.HelloPh.WcW (freeNH BoxOkH)
open Spike.Lib.X64.WakePh (tcbM BandOnP)
open Spike.Lib.X64.WakePh.OwnMid (bandOnP_mono)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib.X64.Flow.HelloWc (sNH WcPreWH WcSp0WH wARH WcCtxH)
open Spike.Lib.X64.Flow.WakeWc (AGB)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Alloc (Call AllocW)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.WakeTP (tpG)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (CellAt eaddr exec_store_agrees)

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

include hp hlo hΛ hlab hsite hcl hX0

omit hX0 in
/-- **The allocator inside `tpG t WSHX`** at `wc_main`'s call (`WcWfR.allocW_wcWSgH` at `ownGHXW`):
`HelloWf.allocW_WSHX_tp` at the allocator's region `wARH R` (its band from `hb`, `WcWfSX.bandAH`), the
controls' facts from the call context's (`hc1J`). -/
theorem allocW_wcWSgHX (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a)
    (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) (hb : BandOnP L R (-304) 8)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -304) (hhi : 8 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isa}
    {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {q : Call} {t : UInt64} (hq : q.OKB ms L.lab)
    (hra : q.ra = (L.lab ".Lwc_main.x0").toBitVec)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j)
    (hnoM : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) → w ≠ tcbM L)
    (hc1J : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : AllocW ms q (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc (wARH R)
      (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧ WcCtxH ms L.lab R J0 J1 q m))
    (hX0a : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (wARH R)
      (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧ WcCtxH ms L.lab R J0 J1 q m))
    (hctx : ∀ s c, At L.exe L.endPc (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧
      WcCtxH ms L.lab R J0 J1 q m) (Spike.Lib.X64.Alloc.N L.lab ms q .rmw) s c → TP t s → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (tpG t (WSHX L a ar p Dt Cl Ctx lbl lsize frM X0)) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc
      (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧ WcCtxH ms L.lab R J0 J1 q m) := by
  obtain ⟨hR', hR8'⟩ := Spike.Lib.X64.HelloPh.WcW.wARH_ok hR hR8 hRlo hhi
  refine Spike.Lib.X64.HelloWf.allocW_WSHX_tp hp hlo hΛ hlab hsite a hsep ha hW
    (Spike.Lib.X64.HelloPh.WcWfSX.bandAH (bandOnP_mono hb (Int.le_refl _) (by decide))) hR' hR8'
    (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee])
    (by simp [Spike.Lib.Region.callee]) hpool (Or.inr rfl) hra (fun _ _ => hq.toS) hmp
    (fun w hw m hm => hmem w hw m hm.1) hno hnoM hcl hpl hX0a ?_ hctx hctr hheap hoff hnew hlt h64
  refine Spike.Lib.X64SetupPlaced.allocW_of_ctl fun m0 hF s c _ hc => ?_
  obtain ⟨-, -, mC, σC, c', -, ⟨⟨σe, hJe, -⟩, -⟩, hN, -⟩ := hF
  have hq0 : c' = q.c0 := hN.1
  have h0 := hc1J σe c' hJe
  rw [hq0] at h0
  rcases hc with rfl | ⟨o, rfl⟩
  · exact h0
  · exact cf_hold h0

/-- **`WcWfSX.wcPreW_WSHX` guarded by the thread pointer `t`** (AArch64 `WcWfR.wcPreW_WSgH`, here at `ownGHXW`): the
prologue and the entry block by `WcWfSX.proW_WSHX`/`eW_WSHX`, the allocator by `allocW_wcWSgHX` (the counter's context
`hctx` owed only at `t`). -/
theorem wcPreW_WSgHX (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a)
    (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) (hb : BandOnP L R (-304) 8)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -304) (hhi : 8 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isa}
    {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp t : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) false
      ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j)
    (hnoM : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) → w ≠ tcbM L)
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hc1J : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : WcPreWH (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms J0 J1)
    (hX0a : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".Lwc_main.x0").toBitVec →
      AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (wARH R)
        (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧ WcCtxH ms L.lab R J0 J1 q m))
    (hctx : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".Lwc_main.x0").toBitVec →
      ∀ s c, At L.exe L.endPc (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧
        WcCtxH ms L.lab R J0 J1 q m) (Spike.Lib.X64.Alloc.N L.lab ms q .rmw) s c → TP t s → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    WcPreWH (tpG t (WSHX L a ar p Dt Cl Ctx lbl lsize frM X0)) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F
      ms J0 J1 :=
  have hb1 : BandOnP L R (-144) 8 := bandOnP_mono hb (by decide) (Int.le_refl _)
  ⟨Spike.Lib.X64.Flow.XProW.imp
      (Spike.Lib.X64.HelloPh.WcWfSX.proW_WSHX (Dt := Dt) (frM := frM) (rS := rS) hp hlo hΛ hlab hsite hcl hX0
        hsep ha hW hb1 hR (by omega) (by omega) htp hmr hun hc0J hpl.pro)
      Spike.Lib.X64.Flow.XProW.triv fun _ _ h _ _ => h,
    Spike.Lib.X64.AllocG.BlkW.imp
      (Spike.Lib.X64.HelloPh.WcWfSX.eW_WSHX hp hlo hΛ hlab hsite hcl hX0 hsep ha hW hb1 hR hRlo hhi hc0J hpl.e)
      Spike.Lib.X64.BlkW.triv fun _ _ h _ _ => h,
    fun q hq hra => allocW_wcWSgHX hp hlo hΛ hlab hsite hcl hsep ha hW hb hR hR8 hRlo hhi hpool hq hra hmp
      (hmem q hq) (hno q hq) (hnoM q hq) hc1J (hpl.alloc q hq hra) (hX0a q hq hra) (hctx q hq hra) hctr hheap
      hoff hnew hlt h64⟩

/-- **`WcWfSX.wcSp0W_WSHX` guarded by the thread pointer `t`** (AArch64 `WcWfR.wcSp0W_WSgH`, here at `ownGHXW`): the
store's writes' obligation only at `t` (`hwr`), `WSHX` only at `t`. -/
theorem wcSp0W_WSgHX (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a)
    (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) (hbd : BandOnP L R (-144) 8) (hR : R.OK)
    (hRlo : R.lo ≤ -136) (hhi : 8 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {t : UInt64}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J1 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOkH L.Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)))
    (hboxM : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J1 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ) ≠ tcbM L)
    (hc1J : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : WcSp0WH (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms J1)
    (hwr : NodeW (tpG t (NoWrC ar p lbl lsize Ctx [])) (fun _ _ => False) L.exe L.endPc R F
      (sNH ms L.lab R J1 .st)) :
    WcSp0WH (tpG t (WSHX L a ar p Dt Cl Ctx lbl lsize frM X0)) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F
      ms J1 := by
  have hS := Spike.Lib.X64.HelloPh.OwnWc.wcSp0W_wcGHX (Λ := L.Λ) (rS := rS) hp hlo hΛ hlab hsite hsep ha hW hbd hR
    hRlo hhi hbox hboxM
  have hin := Spike.Lib.X64.Flow.HelloWc.hello_wcS0InH
  simp only [Spike.Lib.X64.Flow.HelloWc.wcS0InH, Bool.and_eq_true] at hin
  obtain ⟨h0, h3⟩ := hin
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hb : blockAtB L.prog ".Lwc_main.x0" 15 [(Spike.Lib.X64.stDir .rcx 0 .rax, 3)] = true := by
    rw [hp]; exact h3
  refine ⟨?_, ?_⟩
  · exact Spike.Lib.X64.AllocG.BlkW.imp
      (Spike.Lib.X64.HelloPh.WcWfSX.blkW_WSHX hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.x0") (k := 0) h0
        (ofNat_zero' _) Spike.Lib.X64.Flow.HelloWc.wcS0H_ok hR hRlo hhi hS.b (by decide)
        (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (by decide) (by wcfreeBH_dec)
        (fun _ _ ⟨q, ⟨σe, hJe, _⟩, _, o, hc, _⟩ => hc ▸ cf_hold (hc1J σe _ hJe)) hpl.b)
      Spike.Lib.X64.BlkW.triv fun _ _ h _ _ => h
  · have hT := Spike.Lib.X64.HelloPh.WcWfSX.nodeW_WSHX hp hlo hΛ hlab hsite hcl hX0 (Dt := Dt) (frM := frM)
      (n := nT (sNH ms L.lab R J1 .st) t) (l := ".Lwc_main.x0") (k := 15) (z := 3) rfl (nodeW_nT hS.st)
      (by wcfreeH_dec) (by decide) (by unfold Spike.Lib.X64.HelloWf.siOffW; decide +kernel)
      (by
        rintro s c ⟨h1, h2, h3', h4', σ, hA, hF, hJ, -⟩
        have hc := Spike.Lib.X64.Rt.cellOf hI hb rfl h1 h2 h4'
        obtain ⟨q, o, hj, hlo', hle, e⟩ := Spike.Lib.X64.HelloPh.WcW.slot_boxH hJ
        have ha' : eaddr s 3 (mB .rcx 0) = σ.slot (-56) :=
          (eaddr_mB s 3 .rcx 0).trans (by rw [hA.regs]; exact Spike.Lib.X64.HelloPh.WcW.bAddr_boxH hJ)
        refine ⟨_, _, hc, fun w w' h => (by cases h),
          exec_store_agrees hc ha' (by rw [e]; exact (hbox q o hj hlo' hle).2.1 _ hF) (agrees_of_decls h3' _ _),
          fun s' hu => ?_⟩
        simp only [TreeLeaf] at hu
        obtain ⟨_, rfl⟩ := hu; rfl)
      (fun _ _ ⟨⟨q, o, ⟨σe, hJe, _⟩, hc, _⟩, _⟩ => hc ▸ cf_hold (hc1J σe _ hJe))
      (nodeW_nT hpl.st) (nodeW_unTp hwr)
    exact fun s c hA => ⟨fun ht => (hT s c (nT_of_at hA ht)).1, (hS.st s c hA).2⟩

end Gen

end Spike.Lib.X64.HelloPh.WcWfRX

/-- info: 'Spike.Lib.X64.HelloPh.WcWfRX.allocW_wcWSgHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfRX.allocW_wcWSgHX

/-- info: 'Spike.Lib.X64.HelloPh.WcWfRX.wcPreW_WSgHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfRX.wcPreW_WSgHX

/-- info: 'Spike.Lib.X64.HelloPh.WcWfRX.wcSp0W_WSgHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfRX.wcSp0W_WSgHX
