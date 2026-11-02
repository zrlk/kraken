/-
**hello.w's `wc_main` before the box's landing, guarded by the thread pointer** (x86-64; the twin of
`Spike/Lib/A64HelloWcWfR.lean`'s live part, the root-independent half of the hello twin of
`Spike/Lib/X64WakeWcWfRT.lean` at `helloCells`, frame 128): the pieces of wake's `hWp`/`hWs` that do not name
the root instance, at the start's level `StartWf.WSH` generic in `Dt`, `Ctx`, `lsize`, `frM`.

- `freeNH_allocH`, `alloc_labsH`: `scc_rt_alloc`'s pcs are free; its labels at hello's canonical base.
- `blkW_freeH`, `nodeW_freeH`, `allocW_freeH`: every state of `scc_rt_alloc` is at a free pc (`freeNH`;
  `hX0a`'s source).
- `wcSp0W_WSgH`, `allocW_wcWSgH`, `wcPreW_WSgH`: `WcWfS.wcSp0W_WSH` / `allocW_wcWSH` / `wcPreW_WSH` with `WSH`
  owed only at the thread pointer `t` (`tpG t`), the store's writes' obligation (`hwr`) and the allocator's
  counter context (`hctx`) only at `t` (`HelloWf.allocW_WSH_tp`). The generic restriction
  `WcWfR.nT`/`nodeW_nT`/`nodeW_unTp` is reused.

No absolute address appears in the statements.

**Where this differs from AArch64** (forced by the x86-64 shape):
- The allocator's states are free by one range check (`freeNH_allocH`: `scc_rt_alloc` lies in
  `[4198666, 4199029)`, below every range `freeNH` excludes), as wake's `X64WakeWcTop.allocW_free` (AArch64: per
  node by `free_decH` at word offsets). `blkW_freeH`/`nodeW_freeH` take `freeAtH` at byte offsets.
- The thread pointer is `fsBase` (`KeepTP.TP`, `WakeTP.tpG`; AArch64 `TPIDR_EL0`); the prologue is `XProW`.
- `call` pushes the return address: `8 ≤ R.hi`, the allocator's region `wARH R = R.callee (-144) (-160) 8`
  (`CallerCells R (-144) (-160) 8`); the bases are 8-aligned where the allocator's region is formed (`hR8`;
  AArch64's `hal`, 16). The bounds are x86-64's frame (`R.lo ≤ -136` for `.x22`, `-304` for the call).
- The allocator returns to `.Lwc_main.x22` (AArch64 `.L22_wc_main.sp0`); the box's store is at `.x22 + 15`.
-/
import Spike.Lib.X64HelloWcWfS
import Spike.Lib.X64WakeWcWfRT
import Spike.Lib.X64WakeOwnAllocX

namespace Spike.Lib.X64.HelloPh.WcWfR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB codeT_eq)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW At cellOff mB eaddr_mB agrees_of_decls)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.WakeWf (RunWf NoWrC)
open Spike.Lib.X64.WakePh.WcWfR (nT nodeW_nT nT_of_at nodeW_unTp)
open Spike.Lib.X64.WakePh.WcWfS (cf_hold)
open Spike.Lib.X64.HelloPh (lo ownH instOkH)
open Spike.Lib.X64.HelloPh.WcW (freeNH freeAtH freeBlkH inCvH cvH freeAt_pcH BoxOkH)
open Spike.Lib.X64.HelloPh.StartWf (WSH)
open Spike.Lib.X64.Flow.HelloWc (sNH WcPreWH WcSp0WH wARH WcCtxH)
open Spike.Lib.X64.Flow.WakeWc (AGB)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Alloc (Call AllocW fnL entryL cntL slowL fullL okL)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.WakeTP (tpG)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (CellAt eaddr exec_store_agrees)

/-! ## The allocator's pcs free -/

/-- **A pc of `scc_rt_alloc` is free**: `[4198666, 4199029)` lies below every range `freeNH` excludes and the
take site. -/
theorem freeNH_allocH {x : Nat} (h : 4198666 ≤ x ∧ x < 4199029) : freeNH x = true := by
  have hc : 4199029 ≤ cvH "scc_rt_alloc_tcb" ∧ 4199029 ≤ cvH "scc_rt_thread_init" ∧
      4199029 ≤ cvH ".Lwc_main.x24" ∧ 4199029 ≤ cvH "scc_rt_abort" ∧
      4199029 ≤ cvH Spike.Lib.X64.Flow.Ret0.StackTake.siteL := by
    unfold cvH; rw [← codeT_eq]; decide +kernel
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  simp only [freeNH, inCvH, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    Nat.not_le, Nat.not_lt, bne_iff_ne, ne_eq]
  omega

section Free

variable {L : RuntimeLayout} {R : Spike.Lib.Region} {F : MachineData → Prop}
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
include hlab

/-- `scc_rt_alloc`'s labels at hello's canonical base. -/
theorem alloc_labsH :
    (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 4198666 ∧
    (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 4198689 ∧
    (_root_.Executable.labels L.exe).label cntL = Int64.ofNat 4198707 ∧
    (_root_.Executable.labels L.exe).label slowL = Int64.ofNat 4198768 ∧
    (_root_.Executable.labels L.exe).label fullL = Int64.ofNat 4198788 ∧
    (_root_.Executable.labels L.exe).label okL = Int64.ofNat 4198802 ∧
    (_root_.Executable.labels L.exe).label ".Lscc_rt_alloc.spin" = Int64.ofNat 4198786 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;>
    (rw [← codeT_eq]; decide +kernel)

/-- A block's states at free pcs, from `freeAtH` at its label's byte offsets. -/
theorem blkW_freeH {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat}
    (he : L.lab l + Int64.ofNat k = n.pc)
    (hf : freeAtH l ((List.range blk.length).map fun j => k + cellOff blk j) = true) :
    BlkW (fun s _ => freeNH (pcOf s) = true) (fun _ _ => False) L.exe L.endPc R F n blk :=
  Spike.Lib.X64.AllocG.blkW_pc (P := fun x => freeNH x = true) fun j hj => by
    have := freeAt_pcH hlab hf (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    rwa [Int64.ofNat_add, ← Int64.add_assoc, he] at this

/-- A node's states at a free pc, from `freeAtH` at its label. -/
theorem nodeW_freeH {n : ND} {l : Label} {k : Nat} (he : L.lab l + Int64.ofNat k = n.pc)
    (hf : freeAtH l [k] = true) :
    NodeW (fun s _ => freeNH (pcOf s) = true) (fun _ _ => False) L.exe L.endPc R F n :=
  Spike.Lib.X64.AllocG.nodeW_pc (P := fun x => freeNH x = true) (n := n)
    (he ▸ freeAt_pcH hlab hf (List.mem_singleton.mpr rfl))

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1600000 in
/-- **Every state of `scc_rt_alloc` is at a free pc** (`freeNH_allocH` at each node's pcs, decided from the
allocator's labels). -/
theorem allocW_freeH {ms : Spike.Lib.MemSide isa} {q : Call} :
    AllocW ms q (fun s _ => freeNH (pcOf s) = true) (fun _ _ => False) L.exe L.endPc R F := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := alloc_labsH hlab (L := L)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;>
  first
    | exact Spike.Lib.X64.AllocG.blkW_pc (P := fun p => freeNH p = true) fun k hk => freeNH_allocH (by
        revert k; dsimp only [Spike.Lib.X64.Alloc.N]; simp only [e0, e1, e2, e3, e4, e5, e6]; decide +kernel)
    | exact Spike.Lib.X64.AllocG.nodeW_pc (P := fun p => freeNH p = true) (freeNH_allocH (by
        dsimp only [Spike.Lib.X64.Alloc.N]; simp only [e0, e1, e2, e3, e4, e5, e6]; decide +kernel))

end Free

/-! ## Guarded by the thread pointer -/

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

/-- **`WcWfS.wcSp0W_WSH` guarded by the thread pointer `t`**: the store's writes' obligation only at `t`
(`hwr`), `WSH` only at `t`. -/
theorem wcSp0W_WSgH (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 8 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {t : UInt64}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J1 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOkH L.Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)))
    (hc1J : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : WcSp0WH (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms J1)
    (hwr : NodeW (tpG t (NoWrC ar p lbl lsize Ctx [])) (fun _ _ => False) L.exe L.endPc R F
      (sNH ms L.lab R J1 .st)) :
    WcSp0WH (tpG t (WSH L a ar p Dt Cl Ctx lbl lsize frM X0)) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F
      ms J1 := by
  have hS := Spike.Lib.X64.HelloPh.WcW.wcSp0W_wcGH (Λ := L.Λ) (rS := rS) hp hlo hΛ hlab hsite a hR hRlo hhi
    hbox
  have hin := Spike.Lib.X64.Flow.HelloWc.hello_wcS0InH
  simp only [Spike.Lib.X64.Flow.HelloWc.wcS0InH, Bool.and_eq_true] at hin
  obtain ⟨h0, h3⟩ := hin
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hb : blockAtB L.prog ".Lwc_main.x22" 15 [(Spike.Lib.X64.stDir .rcx 0 .rax, 3)] = true := by
    rw [hp]; exact h3
  refine ⟨?_, ?_⟩
  · exact Spike.Lib.X64.AllocG.BlkW.imp
      (Spike.Lib.X64.HelloPh.WcWfS.blkW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.x22") (k := 0) h0
        (ofNat_zero' _) Spike.Lib.X64.Flow.HelloWc.wcS0H_ok hR hRlo hhi hS.b (by decide)
        (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (by decide) (by wcfreeBH_dec)
        (fun _ _ ⟨q, ⟨σe, hJe, _⟩, _, o, hc, _⟩ => hc ▸ cf_hold (hc1J σe _ hJe)) hpl.b)
      Spike.Lib.X64.BlkW.triv fun _ _ h _ _ => h
  · have hT := Spike.Lib.X64.HelloPh.WcWfS.nodeW_WSH hp hlo hΛ hlab hsite hcl hX0 (Dt := Dt) (frM := frM)
      (n := nT (sNH ms L.lab R J1 .st) t) (l := ".Lwc_main.x22") (k := 15) (z := 3) rfl (nodeW_nT hS.st)
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

omit hX0 in
/-- **`WcWfS.allocW_wcWSH` guarded by the thread pointer `t`** (`HelloWf.allocW_WSH_tp`): the counter's context
owed only at `t`. -/
theorem allocW_wcWSgH (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -304) (hhi : 8 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isa}
    {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {q : Call} {t : UInt64} (hq : q.OKB ms L.lab)
    (hra : q.ra = (L.lab ".Lwc_main.x22").toBitVec)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j)
    (hc1J : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : AllocW ms q (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc (wARH R)
      (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧ WcCtxH ms L.lab R J0 J1 q m))
    (hX0a : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (wARH R)
      (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧ WcCtxH ms L.lab R J0 J1 q m))
    (hctx : ∀ s c, At L.exe L.endPc (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧
      WcCtxH ms L.lab R J0 J1 q m) (Spike.Lib.X64.Alloc.N L.lab ms q .rmw) s c → TP t s → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (tpG t (WSH L a ar p Dt Cl Ctx lbl lsize frM X0)) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc
      (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧ WcCtxH ms L.lab R J0 J1 q m) := by
  obtain ⟨hR', hR8'⟩ := Spike.Lib.X64.HelloPh.WcW.wARH_ok hR hR8 hRlo hhi
  refine Spike.Lib.X64.HelloWf.allocW_WSH_tp hp hlo hΛ hlab hsite a hR' hR8' (by simp [Spike.Lib.Region.callee])
    (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee])
    hpool (Or.inr rfl) hra (fun _ _ => hq.toS) hmp (fun w hw m hm => hmem w hw m hm.1) hno hcl hpl hX0a ?_ hctx
    hctr hheap hoff hnew hlt h64
  refine Spike.Lib.X64SetupPlaced.allocW_of_ctl fun m0 hF s c _ hc => ?_
  obtain ⟨-, -, mC, σC, c', -, ⟨⟨σe, hJe, -⟩, -⟩, hN, -⟩ := hF
  have hq0 : c' = q.c0 := hN.1
  have h0 := hc1J σe c' hJe
  rw [hq0] at h0
  rcases hc with rfl | ⟨o, rfl⟩
  · exact h0
  · exact cf_hold h0

/-- **`WcWfS.wcPreW_WSH` guarded by the thread pointer `t`**: the prologue and the entry block by
`WcWfS.proW_WSH`/`eW_WSH`, the allocator by `allocW_wcWSgH` (the counter's context `hctx` owed only at `t`). -/
theorem wcPreW_WSgH (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -304) (hhi : 8 ≤ R.hi)
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
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hc1J : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : WcPreWH (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms J0 J1)
    (hX0a : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".Lwc_main.x22").toBitVec →
      AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (wARH R)
        (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧ WcCtxH ms L.lab R J0 J1 q m))
    (hctx : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".Lwc_main.x22").toBitVec →
      ∀ s c, At L.exe L.endPc (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧
        WcCtxH ms L.lab R J0 J1 q m) (Spike.Lib.X64.Alloc.N L.lab ms q .rmw) s c → TP t s → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    WcPreWH (tpG t (WSH L a ar p Dt Cl Ctx lbl lsize frM X0)) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F
      ms J0 J1 :=
  ⟨Spike.Lib.X64.Flow.XProW.imp
      (Spike.Lib.X64.HelloPh.WcWfS.proW_WSH (Dt := Dt) (frM := frM) (rS := rS) hp hlo hΛ hlab hsite hcl hX0 hR
        (by omega) (by omega) htp hmr hun hc0J hpl.pro)
      Spike.Lib.X64.Flow.XProW.triv fun _ _ h _ _ => h,
    Spike.Lib.X64.AllocG.BlkW.imp
      (Spike.Lib.X64.HelloPh.WcWfS.eW_WSH hp hlo hΛ hlab hsite hcl hX0 hR hRlo hhi hc0J hpl.e)
      Spike.Lib.X64.BlkW.triv fun _ _ h _ _ => h,
    fun q hq hra => allocW_wcWSgH hp hlo hΛ hlab hsite hcl hR hR8 hRlo hhi hpool hq hra hmp (hmem q hq)
      (hno q hq) hc1J (hpl.alloc q hq hra) (hX0a q hq hra) (hctx q hq hra) hctr hheap hoff hnew hlt h64⟩

end Gen

end Spike.Lib.X64.HelloPh.WcWfR

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.WcWfR.allocW_freeH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfR.allocW_freeH

/-- info: 'Spike.Lib.X64.HelloPh.WcWfR.wcSp0W_WSgH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfR.wcSp0W_WSgH

/-- info: 'Spike.Lib.X64.HelloPh.WcWfR.allocW_wcWSgH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfR.allocW_wcWSgH

/-- info: 'Spike.Lib.X64.HelloPh.WcWfR.wcPreW_WSgH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfR.wcPreW_WSgH
