/-
**hello.w's `wc_main` before the box's landing, guarded by the thread
pointer** (AArch64, hTop; the root-independent
half of the twin of `Spike/Lib/A64WakeWcWfR.lean` at helloProg, frame 144):
the pieces of wake's `hWp`/`hWs` that do not name the root instance, at the
start's level `StartWf.WSH` generic in `Dt`, `Ctx`, `lsize`, `frM`.

- `blkW_freeH`, `nodeW_freeH`, `allocW_freeH`: every state of
  `scc_rt_alloc` is at a free pc (`freeNH`; `hX0a`'s source).
- `wcPreW_vacH`, `wcSp0W_vacH`: at a frame condition holding for no memory
  (the generic `WcWfR.blkW_vac`/`nodeW_vac`/`allocW_vac` reused).
- `wcSp0W_WSgH`, `allocW_wcWSgH`, `wcPreW_WSgH`: `WcWfS.wcSp0W_WSH` /
  `allocW_wcWSH` / `wcPreW_WSH` with `WSH` owed only at the thread pointer
  `t` (`tpG t`), the store's writes' obligation (`hwr`) and the allocator's
  counter context (`hctx`) only at `t` (`HelloWf.allocW_WSH_tp`). The
  generic restriction `WcWfR.nT`/`nodeW_nT`/`nodeW_unTp` is reused.

The root half (wake's `v_top`, `hWp_W`, `hWs_W`, `hTopP_Rpl`, `hTopS_Rpl`,
`hTopP_R`, `hTopS_R`) needs hello's root instance (its `PlaceW` layout,
immediates, `C0`, `L0T`) and the B8 tier's `StartH0R`/`Land3` twins, and
hello's `wc_main` frame condition after `wc_rodata`; it is not in this file.
No absolute address appears in this file.
-/
import Spike.Lib.A64HelloWcWfS
import Spike.Lib.A64HelloAllocWSTp
import Spike.Lib.A64WakeWcWfR

namespace Spike.Lib.A64.HelloPh.WcWfR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf)
open Scc.Cert.Rt.A64 (codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.WakeWf (NoWrC)
open Spike.Lib.A64.WakePh.WcWfR (blkW_vac nodeW_vac allocW_vac nT nodeW_nT nT_of_at nodeW_unTp)
open Spike.Lib.A64.HelloPh.WcW (freeNH freeAtH freeAt_pcH freeAt_pc0H BoxOkH)
open Spike.Lib.A64.HelloPh.StartWf (WSH)
open Spike.Lib.A64.Flow.HelloWc (sNH WcPreWH WcSp0WH wARH WcCtxH)
open Spike.Lib.A64.Flow.WakeWc (tpG)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call AllocW)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib (FragS)

/-! ## The allocator's pcs free -/

section Free

variable {L : RuntimeLayout} {R : Spike.Lib.Region} {F : MachineData → Prop}
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
include hlab

/-- A block's states at free pcs, from `freeAtH` at its label. -/
theorem blkW_freeH {n : ND} {blk : List Directive} {l : Label} {k : Nat}
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc) (hf : freeAtH l k blk.length = true) :
    BlkW (fun s _ => freeNH (pcOf s) = true) (fun _ _ => False) L.exe L.endPc R F n blk :=
  Spike.Lib.A64.AllocG.blkW_pc (P := fun x => freeNH x = true) fun _ hj => by
    rw [← he]; exact freeAt_pcH hlab hf hj

/-- A node's states at a free pc, from `freeAtH` at its label. -/
theorem nodeW_freeH {n : ND} {l : Label} {k : Nat} (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hf : freeAtH l k 1 = true) :
    NodeW (fun s _ => freeNH (pcOf s) = true) (fun _ _ => False) L.exe L.endPc R F n :=
  Spike.Lib.A64.AllocG.nodeW_pc (P := fun x => freeNH x = true) (n := n) (he ▸ freeAt_pc0H hlab hf)

set_option maxHeartbeats 800000 in
/-- **Every state of `scc_rt_alloc` is at a free pc** (`WcW.freeNH`, checked
by the kernel against helloProg's labels). -/
theorem allocW_freeH {ms : Spike.Lib.MemSide isaLSE2} {q : Call} :
    AllocW ms q (fun s _ => freeNH (pcOf s) = true) (fun _ _ => False) L.exe L.endPc R F :=
  ⟨blkW_freeH hlab (l := "scc_rt_alloc") (k := 0) (by pc_tac) (by free_decH),
    blkW_freeH hlab (l := ".L2_scc_rt_alloc.0_entry") (k := 0) (by pc_tac) (by free_decH),
    blkW_freeH hlab (l := ".L2_scc_rt_alloc.0_entry") (k := 4) (by pc_tac) (by free_decH),
    nodeW_freeH hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 0) (by pc_tac) (by free_decH),
    nodeW_freeH hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 1) (by pc_tac) (by free_decH),
    blkW_freeH hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 2) (by pc_tac) (by free_decH),
    nodeW_freeH hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 5) (by pc_tac) (by free_decH),
    blkW_freeH hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 6) (by pc_tac) (by free_decH),
    blkW_freeH hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 15) (by pc_tac) (by free_decH),
    blkW_freeH hlab (l := ".L2_scc_rt_alloc.2_slow") (k := 0) (by pc_tac) (by free_decH),
    blkW_freeH hlab (l := ".L2_scc_rt_alloc.2_slow") (k := 4) (by pc_tac) (by free_decH),
    blkW_freeH hlab (l := ".L2_scc_rt_alloc.4_full") (k := 0) (by pc_tac) (by free_decH),
    blkW_freeH hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 0) (by pc_tac) (by free_decH),
    nodeW_freeH hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 8) (by pc_tac) (by free_decH),
    nodeW_freeH hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 9) (by pc_tac) (by free_decH),
    blkW_freeH hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 10) (by pc_tac) (by free_decH),
    nodeW_freeH hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 41) (by pc_tac) (by free_decH),
    blkW_freeH hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 42) (by pc_tac) (by free_decH),
    nodeW_freeH hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 54) (by pc_tac) (by free_decH)⟩

end Free

/-! ## At a frame condition holding for no memory -/

section Vac

variable {W : Spike.Lib.Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {ms : Spike.Lib.MemSide isaLSE2}

/-- **`WcPreWH` at a frame condition holding for no memory.** -/
theorem wcPreW_vacH (hF : ∀ m, ¬ F m) {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} :
    WcPreWH W K exe endPc R F ms J0 J1 :=
  ⟨⟨blkW_vac hF, nodeW_vac hF, blkW_vac hF, blkW_vac hF⟩, blkW_vac hF,
    fun _ _ _ => allocW_vac fun m h => hF m h.1⟩

/-- **`WcSp0WH` at a frame condition holding for no memory.** -/
theorem wcSp0W_vacH (hF : ∀ m, ¬ F m) {J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} :
    WcSp0WH W K exe endPc R F ms J1 :=
  ⟨blkW_vac hF, nodeW_vac hF⟩

end Vac

/-! ## Guarded by the thread pointer -/

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Scc.Sem.Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Spike.Lib.Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → Scc.Sem.A64.abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

include hp hlo hΛ hlab hsite hcl hX0

/-- **`WcWfS.wcSp0W_WSH` guarded by the thread pointer `t`**: the store's
writes' obligation only at `t` (`hwr`), `WSH` only at `t`. -/
theorem wcSp0W_WSgH (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {t : UInt64}
    (hbox : ∀ (q : Spike.Lib.A64.Flow.WakeWc.AGB ms L.lab) (o : Nat), (∃ σ, J1 σ q.1.c0) → ms.lo o →
      o + ms.units 1 q.1.τ ≤ ms.cells → BoxOkH L.Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)))
    (hc1J : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf p c [])
    (hpl : WcSp0WH (fun s c => Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe
      L.endPc R F ms J1)
    (hwr : NodeW (tpG t (NoWrC ar p lbl lsize Ctx [])) (fun _ _ => False) L.exe L.endPc R F
      (sNH ms L.lab J1 .st)) :
    WcSp0WH (tpG t (WSH L a ar p Dt Cl Ctx lbl lsize frM X0)) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F
      ms J1 := by
  have hS := Spike.Lib.A64.HelloPh.WcW.wcSp0W_wcGH (Λ := L.Λ) (rS := rS) hp hlo hΛ hlab hsite a hR hal hRlo hhi
    hbox
  have hin := Spike.Lib.A64.Flow.HelloWc.hello_wcS0InH
  simp only [Spike.Lib.A64.Flow.HelloWc.wcS0InH, Bool.and_eq_true] at hin
  obtain ⟨h0, h3⟩ := hin
  rw [Spike.Lib.A64.Flow.WakeWc.boxSt_eq] at h3
  refine ⟨?_, ?_⟩
  · exact Spike.Lib.A64.AllocG.BlkW.imp
      (Spike.Lib.A64.HelloPh.WcWfS.blkW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".L22_wc_main.sp0") (k := 0) h0
        (Spike.Lib.A64.Flow.ofNat4_zero _) Spike.Lib.A64.Flow.HelloWc.wcS0H_ok hR hal hRlo hhi hS.b
        (by decide) (by decide +kernel) (by decide) (by free_decH)
        (fun _ _ ⟨q, ⟨σe, hJe, _⟩, o, hc, _⟩ => hc ▸ Spike.Lib.A64.WakePh.WcWfS.cf_hold (hc1J σe _ hJe)) hpl.b)
      Spike.Lib.A64.Flow.BlkW.triv fun _ _ h _ _ => h
  · have hI := instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
    have hT := Spike.Lib.A64.HelloPh.WcWfS.nodeW_WSH hp hlo hΛ hlab hsite hcl hX0 (Dt := Dt) (frM := frM)
      (n := nT (sNH ms L.lab J1 .st) t)
      (l := ".L22_wc_main.sp0") (k := 3) rfl (nodeW_nT hS.st) (by free_decH)
      (by decide) (by decide +kernel)
      (Spike.Lib.A64.WakeWf.st_step hI (by rw [hp]; exact h3) rfl fun σ c m hJ hF => by
        rw [Spike.Lib.A64.HelloPh.WcW.rAddr_boxH hJ.1]
        obtain ⟨q, o, hj, hlo', hle, e⟩ := Spike.Lib.A64.HelloPh.WcW.slot_boxH hJ.1
        rw [e]; exact (hbox q o hj hlo' hle).2.1 m hF)
      (fun _ _ ⟨⟨q, o, ⟨σe, hJe, _⟩, hc, _⟩, _⟩ => hc ▸ Spike.Lib.A64.WakePh.WcWfS.cf_hold (hc1J σe _ hJe))
      (nodeW_nT hpl.st) (nodeW_unTp hwr)
    exact fun s c hA => ⟨fun ht => (hT s c (nT_of_at hA ht)).1, (hS.st s c hA).2⟩

omit hX0 in
/-- **`WcWfS.allocW_wcWSH` guarded by the thread pointer `t`**
(`HelloWf.allocW_WSH_tp`): the counter's context owed only at `t`. -/
theorem allocW_wcWSgH (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isaLSE2}
    {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {q : Call} {t : UInt64} (hq : q.OKB ms L.lab)
    (hra : q.ra = (L.lab ".L22_wc_main.sp0").toBitVec)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j)
    (hc1J : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf p c [])
    (hpl : AllocW ms q (fun s c => Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe
      L.endPc (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧ WcCtxH ms L.lab R J0 J1 q m))
    (hX0a : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (wARH R)
      (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧ WcCtxH ms L.lab R J0 J1 q m))
    (hctx : ∀ s c, At L.exe L.endPc (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧
      WcCtxH ms L.lab R J0 J1 q m) (Spike.Lib.A64.Alloc.N L.lab ms q .rmw) s c → TP t s → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (tpG t (WSH L a ar p Dt Cl Ctx lbl lsize frM X0)) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc
      (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧ WcCtxH ms L.lab R J0 J1 q m) := by
  obtain ⟨hR', hal'⟩ := Spike.Lib.A64.HelloPh.WcW.wARH_ok hR hal hRlo hhi
  refine Spike.Lib.A64.HelloWf.allocW_WSH_tp hp hlo hΛ hlab hsite a hR' hal' (by simp [Spike.Lib.Region.callee])
    (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee])
    hpool (Or.inr rfl) hra (fun _ _ => hq.toS) hmp (fun w hw m hm => hmem w hw m hm.1) hno hcl hpl hX0a ?_ hctx
    hctr hheap hoff hnew hlt h64
  refine Spike.Lib.A64SetupPlaced.allocW_of_ctl fun m0 hF s c _ hc => ?_
  obtain ⟨-, -, mC, σC, c', -, ⟨⟨σe, hJe, -⟩, -⟩, hN, -⟩ := hF
  have hq0 : c' = q.c0 := hN.1
  have h0 := hc1J σe c' hJe
  rw [hq0] at h0
  rcases hc with rfl | ⟨o, rfl⟩
  · exact h0
  · exact Spike.Lib.A64.WakePh.WcWfS.cf_hold h0

/-- **`WcWfS.wcPreW_WSH` guarded by the thread pointer `t`**: the prologue
and the entry block by `WcWfS.proW_WSH`/`eW_WSH`, the allocator by
`allocW_wcWSgH` (the counter's context `hctx` owed only at `t`). -/
theorem wcPreW_WSgH (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isaLSE2}
    {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp t : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j)
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf p c [])
    (hc1J : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf p c [])
    (hpl : WcPreWH (fun s c => Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe
      L.endPc R F ms J0 J1)
    (hX0a : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".L22_wc_main.sp0").toBitVec →
      AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (wARH R)
        (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧ WcCtxH ms L.lab R J0 J1 q m))
    (hctx : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".L22_wc_main.sp0").toBitVec →
      ∀ s c, At L.exe L.endPc (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧
        WcCtxH ms L.lab R J0 J1 q m) (Spike.Lib.A64.Alloc.N L.lab ms q .rmw) s c → TP t s → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    WcPreWH (tpG t (WSH L a ar p Dt Cl Ctx lbl lsize frM X0)) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F
      ms J0 J1 :=
  have hP := Spike.Lib.A64.HelloPh.WcWfS.proW_WSH (Dt := Dt) (frM := frM) (rS := rS) hp hlo hΛ hlab hsite hcl
    hX0 hR hal (by omega) hhi htp hmr hun hc0J hpl.pro
  ⟨⟨Spike.Lib.A64.AllocG.BlkW.imp hP.w0 Spike.Lib.A64.Flow.BlkW.triv fun _ _ h _ _ => h,
      Spike.Lib.A64.AllocG.NodeW.imp hP.w1 Spike.Lib.A64.Flow.NodeW.triv fun _ _ h _ _ => h,
      Spike.Lib.A64.AllocG.BlkW.imp hP.w2 Spike.Lib.A64.Flow.BlkW.triv fun _ _ h _ _ => h,
      Spike.Lib.A64.AllocG.BlkW.imp hP.w3 Spike.Lib.A64.Flow.BlkW.triv fun _ _ h _ _ => h⟩,
    Spike.Lib.A64.AllocG.BlkW.imp
      (Spike.Lib.A64.HelloPh.WcWfS.eW_WSH hp hlo hΛ hlab hsite hcl hX0 hR hal hRlo hhi hc0J hpl.e)
      Spike.Lib.A64.Flow.BlkW.triv fun _ _ h _ _ => h,
    fun q hq hra => allocW_wcWSgH hp hlo hΛ hlab hsite hcl hR hal hRlo hhi hpool hq hra hmp (hmem q hq)
      (hno q hq) hc1J (hpl.alloc q hq hra) (hX0a q hq hra) (hctx q hq hra) hctr hheap hoff hnew hlt h64⟩

end Gen

end Spike.Lib.A64.HelloPh.WcWfR

/-! ## Axioms -/

/-- info: 'Spike.Lib.A64.HelloPh.WcWfR.allocW_freeH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcWfR.allocW_freeH

/-- info: 'Spike.Lib.A64.HelloPh.WcWfR.wcPreW_vacH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcWfR.wcPreW_vacH

/-- info: 'Spike.Lib.A64.HelloPh.WcWfR.wcSp0W_vacH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcWfR.wcSp0W_vacH

/-- info: 'Spike.Lib.A64.HelloPh.WcWfR.wcSp0W_WSgH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcWfR.wcSp0W_WSgH

/-- info: 'Spike.Lib.A64.HelloPh.WcWfR.allocW_wcWSgH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcWfR.allocW_wcWSgH

/-- info: 'Spike.Lib.A64.HelloPh.WcWfR.wcPreW_WSgH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcWfR.wcPreW_WSgH
