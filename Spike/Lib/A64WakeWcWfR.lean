/-
**`wc_main`'s `hWp`/`hWs` at the root's choices** (wake.w, AArch64): `StartH0R.hst0_ofW`'s / `StartH0G.wake_start_wc_h0W`'s premises on
`wc_main` before the box's landing, at the start's memory side
`tpXa (msOfA …) t` generic in its marks, reads, `G`, ownership, invariant,
labels and sizes, and the start's fragment `WS` generic in `Dt`, `Ctx`,
`lsize`, `frM`.

The frame condition `wF … (FS … v)` pins the switch's base `v` to the top
of the first stack (`swF`): at any other `v` no memory satisfies it and both
obligations hold vacuously (`wcPreW_vac`, `wcSp0W_vac`). At the top they are
`WcWfS.wcPreW_WS` / `wcSp0W_WS`.

- `blkW_free`, `nodeW_free`, `allocW_free`: every state of `scc_rt_alloc` is
  at a free pc (`hX0a`'s source).
- `wcPreW_vac`, `wcSp0W_vac`: at a frame condition holding for no memory.
- `v_top`: the frame condition at the base `v` pins `v` to the top.
- `hWp_W` (unguarded, after `.of_unguarded` the chain's `hWp`), `hWs_W`
  (guarded by the thread pointer): the statements. Their open premises
  are the allocator's counter context (`hctx`: `Land.hctx_R`)
  and the box store's writes' obligation at the thread pointer (`hwr`: `Land.hwr_R`).
- `not_ownW`, `offW_own`, `rw_top`, `tau_c0W`: the counter and header words
  owned at no phase, the switch's region at the top OK, the box at `c0W` an
  `int`.
- `hTopP_Rpl`, `hTopS_Rpl`: the top case (`hTop`) at the root's memory side
  and context `Land.CtxR`, all premises discharged (`hctx`/`hwr` by
  `Land.hctx_R`/`Land.hwr_R`) but the placement `hpl`; `hTopP_R`,
  `hTopS_R`: closed by `WcPl.hplP_W`/`hplS_W` (the root's `hTopP`/`hTopS`).
-/
import Spike.Lib.A64WakeWcWfS
import Spike.Lib.A64WakeStartH0R
import Spike.Lib.A64WakeWcPreWI
import Spike.Lib.A64AllocGSt
import Spike.Lib.A64WakeAllocWSTp
import Spike.Lib.A64WakeLand3
import Spike.Lib.A64WakeStartH0Ti
import Spike.Lib.A64WakeWfCalOff
import Spike.Lib.A64WakePlacedAlloc
import Spike.Lib.A64WakeMainL
import Spike.Lib.A64WakeHClW
import Spike.Lib.WakeImmsC0
import Spike.Lib.WakeAWSite
import Spike.Lib.A64WakeStartPlaceLy
import Spike.Lib.A64WakeWcPl

namespace Spike.Lib.A64.WakePh.WcWfR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (pcOf textProgram)
open Scc.Cert.Rt.A64 (codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Flow (ND BlkW NodeW At swR)
open Spike.Lib.A64.WakeWf (NoWrC X0W)
open Spike.Lib.A64.WakePh.WcW (freeN freeAt freeAt_pc freeAt_pc0)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Flow.Ret0 (pinA CallerCells)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (WcPreW WcSp0W sN wAR WcCtx tpG)
open Spike.Lib.A64.Alloc (Call AllocW)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib (FragS)
open Spike.Lib.WakeLoadT (L0T)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeC0 (c0W)

/-! ## The allocator's pcs free -/

section Free

variable {L : RuntimeLayout} {R : Spike.Lib.Region} {F : MachineData → Prop}
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
include hlab

/-- A block's states at free pcs, from `freeAt` at its label. -/
theorem blkW_free {n : ND} {blk : List Directive} {l : Label} {k : Nat}
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc) (hf : freeAt l k blk.length = true) :
    BlkW (fun s _ => freeN (pcOf s) = true) (fun _ _ => False) L.exe L.endPc R F n blk :=
  Spike.Lib.A64.AllocG.blkW_pc (P := fun x => freeN x = true) fun _ hj => by
    rw [← he]; exact freeAt_pc hlab hf hj

/-- A node's states at a free pc, from `freeAt` at its label. -/
theorem nodeW_free {n : ND} {l : Label} {k : Nat} (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hf : freeAt l k 1 = true) :
    NodeW (fun s _ => freeN (pcOf s) = true) (fun _ _ => False) L.exe L.endPc R F n :=
  Spike.Lib.A64.AllocG.nodeW_pc (P := fun x => freeN x = true) (n := n) (he ▸ freeAt_pc0 hlab hf)

set_option maxHeartbeats 800000 in
/-- **Every state of `scc_rt_alloc` is at a free pc** (`WcW.freeN`, checked
by the kernel against the certificate's labels). -/
theorem allocW_free {ms : Spike.Lib.MemSide isaLSE2} {q : Call} :
    AllocW ms q (fun s _ => freeN (pcOf s) = true) (fun _ _ => False) L.exe L.endPc R F :=
  ⟨blkW_free hlab (l := "scc_rt_alloc") (k := 0) (by pc_tac) (by free_dec),
    blkW_free hlab (l := ".L2_scc_rt_alloc.0_entry") (k := 0) (by pc_tac) (by free_dec),
    blkW_free hlab (l := ".L2_scc_rt_alloc.0_entry") (k := 4) (by pc_tac) (by free_dec),
    nodeW_free hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 0) (by pc_tac) (by free_dec),
    nodeW_free hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 1) (by pc_tac) (by free_dec),
    blkW_free hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 2) (by pc_tac) (by free_dec),
    nodeW_free hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 5) (by pc_tac) (by free_dec),
    blkW_free hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 6) (by pc_tac) (by free_dec),
    blkW_free hlab (l := ".L2_scc_rt_alloc.1_cnt") (k := 15) (by pc_tac) (by free_dec),
    blkW_free hlab (l := ".L2_scc_rt_alloc.2_slow") (k := 0) (by pc_tac) (by free_dec),
    blkW_free hlab (l := ".L2_scc_rt_alloc.2_slow") (k := 4) (by pc_tac) (by free_dec),
    blkW_free hlab (l := ".L2_scc_rt_alloc.4_full") (k := 0) (by pc_tac) (by free_dec),
    blkW_free hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 0) (by pc_tac) (by free_dec),
    nodeW_free hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 8) (by pc_tac) (by free_dec),
    nodeW_free hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 9) (by pc_tac) (by free_dec),
    blkW_free hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 10) (by pc_tac) (by free_dec),
    nodeW_free hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 41) (by pc_tac) (by free_dec),
    blkW_free hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 42) (by pc_tac) (by free_dec),
    nodeW_free hlab (l := ".L2_scc_rt_alloc.5_ok") (k := 54) (by pc_tac) (by free_dec)⟩

end Free

/-! ## At a frame condition holding for no memory -/

section Vac

variable {W : Spike.Lib.Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {ms : Spike.Lib.MemSide isaLSE2}

/-- A block at a frame condition holding for no memory. -/
theorem blkW_vac (hF : ∀ m, ¬ F m) {n : ND} {blk : List Directive} : BlkW W K exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ hF' => (hF _ hF').elim

/-- A node at a frame condition holding for no memory. -/
theorem nodeW_vac (hF : ∀ m, ¬ F m) {n : ND} : NodeW W K exe endPc R F n :=
  fun _ _ ⟨_, _, _, _, _, _, hF', _⟩ => (hF _ hF').elim

/-- `scc_rt_alloc` at a frame condition holding for no memory. -/
theorem allocW_vac (hF : ∀ m, ¬ F m) {q : Call} : AllocW ms q W K exe endPc R F :=
  ⟨blkW_vac hF, blkW_vac hF, blkW_vac hF, nodeW_vac hF, nodeW_vac hF, blkW_vac hF, nodeW_vac hF,
    blkW_vac hF, blkW_vac hF, blkW_vac hF, blkW_vac hF, blkW_vac hF, blkW_vac hF, nodeW_vac hF,
    nodeW_vac hF, blkW_vac hF, nodeW_vac hF, blkW_vac hF, nodeW_vac hF⟩

/-- **`WcPreW` at a frame condition holding for no memory.** -/
theorem wcPreW_vac (hF : ∀ m, ¬ F m) {J0 Jc : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} :
    WcPreW W K exe endPc R F ms J0 Jc :=
  ⟨⟨blkW_vac hF, nodeW_vac hF, blkW_vac hF, blkW_vac hF⟩, blkW_vac hF,
    fun _ _ _ => allocW_vac fun m h => hF m h.1⟩

/-- **`WcSp0W` at a frame condition holding for no memory.** -/
theorem wcSp0W_vac (hF : ∀ m, ¬ F m) {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} :
    WcSp0W W K exe endPc R F ms J0 :=
  ⟨blkW_vac hF, nodeW_vac hF⟩

end Vac

/-! ## A node restricted to a thread pointer -/

section Tp

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- `n` at the abstract states of thread pointer `t`. -/
def nT (n : ND) (t : UInt64) : ND := ⟨n.pc, n.o, fun σ c => n.J σ c ∧ σ.regs.TPIDR_EL0 = t⟩

/-- A state at the restricted node is at the node. -/
theorem at_of_nT {n : ND} {t : UInt64} {s : State} {c : Spike.Lib.Ctl} (h : At exe endPc R F (nT n t) s c) :
    At exe endPc R F n s c :=
  let ⟨he, hn, hd, hpc, σ, hA, hF, hJ, _⟩ := h
  ⟨he, hn, hd, hpc, σ, hA, hF, hJ⟩

/-- A state at the node with thread pointer `t` is at the restricted node. -/
theorem nT_of_at {n : ND} {t : UInt64} {s : State} {c : Spike.Lib.Ctl} (h : At exe endPc R F n s c)
    (ht : TP t s) : At exe endPc R F (nT n t) s c :=
  let ⟨he, hn, hd, hpc, σ, hA, hF, hJ⟩ := h
  ⟨he, hn, hd, hpc, σ, hA, hF, hJ, by rw [← hA.regs]; exact ht⟩

/-- A node obligation restricts to the thread pointer `t`. -/
theorem nodeW_nT {W : Spike.Lib.Frag isaLSE2} {K : State → State → Prop} {n : ND} {t : UInt64}
    (h : NodeW W K exe endPc R F n) : NodeW W K exe endPc R F (nT n t) :=
  fun s c hA => h s c (at_of_nT hA)

/-- A node obligation guarded by the thread pointer is one at the restricted node. -/
theorem nodeW_unTp {W : Spike.Lib.Frag isaLSE2} {n : ND} {t : UInt64}
    (h : NodeW (tpG t W) (fun _ _ => False) exe endPc R F n) :
    NodeW W (fun _ _ => False) exe endPc R F (nT n t) :=
  fun s c hA => ⟨(h s c (at_of_nT hA)).1 (Spike.Lib.A64.Flow.WakeWc.tp_of_at (n := nT n t)
    (fun _ _ (h : n.J _ _ ∧ _) => h.2) hA),
    fun _ h => h⟩

end Tp

/-! ## `.sp0` at the thread pointer -/

/-- The kernel's check of a block's abort phases (`phOffW`). -/
local macro "ph_dec" : tactic => `(tactic| (simp only [Spike.Lib.A64.WakeWf.phOffW, ← codeT_eq]; decide +kernel))
/-- The kernel's check of a node's abort phases (`siOffW`). -/
local macro "si_dec" : tactic => `(tactic| (simp only [Spike.Lib.A64.WakeWf.siOffW, ← codeT_eq]; decide +kernel))

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Scc.Sem.Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Spike.Lib.Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}
  (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → Scc.Sem.A64.abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.clone st tl))
  (hX0 : ∀ s, freeN (pcOf s) = true → X0 s)

include hp hlo hΛ hlab hsite hcl hX0

/-- **`WcWfS.wcSp0W_WS` guarded by the thread pointer `t`**: the store's
writes' obligation only at `t` (`hwr`), `WS` only at `t`. -/
theorem wcSp0W_WSg (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {t : UInt64}
    (hbox : ∀ (q : Spike.Lib.A64.Flow.WakeWc.AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o →
      o + ms.units 1 q.1.τ ≤ ms.cells →
      Spike.Lib.A64.WakePh.WcW.BoxOk L.Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)))
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf p c [])
    (hpl : WcSp0W (fun s c => Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F
      ms J0)
    (hwr : NodeW (tpG t (NoWrC ar p lbl lsize Ctx [])) (fun _ _ => False) L.exe L.endPc R F
      (sN ms L.lab J0 .st)) :
    WcSp0W (tpG t (WS L a ar p Dt Cl Ctx lbl lsize frM X0)) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F
      ms J0 := by
  have hS := Spike.Lib.A64.WakePh.WcW.wcSp0W_wcG (Λ := L.Λ) (rS := rS) hp hlo hΛ hlab hsite a hR hal hRlo hhi
    hbox
  have hin := Spike.Lib.A64.Flow.WakeWc.wake_wcS0In
  simp only [Spike.Lib.A64.Flow.WakeWc.wcS0In, Bool.and_eq_true] at hin
  obtain ⟨h0, h3⟩ := hin
  rw [Spike.Lib.A64.Flow.WakeWc.boxSt_eq] at h3
  refine ⟨?_, ?_⟩
  · exact Spike.Lib.A64.AllocG.BlkW.imp
      (Spike.Lib.A64.WakePh.WcWfS.blkW_WS hp hlo hΛ hlab hsite hcl hX0 (l := ".L21_wc_main.sp0") (k := 0) h0
        (Spike.Lib.A64.Flow.ofNat4_zero _) Spike.Lib.A64.Flow.WakeWc.wcS0_ok hR hal hRlo hhi hS.b
        (by simp [Spike.Lib.A64.WakePh.WcW.wcTabW]) (by ph_dec) (by decide) (by free_dec)
        (fun _ _ ⟨q, ⟨σe, hJe, _⟩, o, hc, _⟩ => hc ▸ Spike.Lib.A64.WakePh.WcWfS.cf_hold (hc0J σe _ hJe)) hpl.b)
      Spike.Lib.A64.Flow.BlkW.triv fun _ _ h _ _ => h
  · have hI := Spike.Lib.A64.WakePh.instOkW hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
    have hT := Spike.Lib.A64.WakePh.WcWfS.nodeW_WS hp hlo hΛ hlab hsite hcl hX0 (Dt := Dt) (frM := frM)
      (n := nT (sN ms L.lab J0 .st) t)
      (l := ".L21_wc_main.sp0") (k := 3) rfl (nodeW_nT hS.st) (by free_dec)
      (by simp [Spike.Lib.A64.WakePh.WcW.wcTabW]) (by si_dec)
      (Spike.Lib.A64.WakeWf.st_step hI (by rw [hp]; exact h3) rfl fun σ c m hJ hF => by
        rw [Spike.Lib.A64.WakePh.WcW.rAddr_box hJ.1]
        obtain ⟨q, o, hj, hlo', hle, e⟩ := Spike.Lib.A64.WakePh.WcW.slot_box hJ.1
        rw [e]; exact (hbox q o hj hlo' hle).2.1 m hF)
      (fun _ _ ⟨⟨q, o, ⟨σe, hJe, _⟩, hc, _⟩, _⟩ => hc ▸ Spike.Lib.A64.WakePh.WcWfS.cf_hold (hc0J σe _ hJe))
      (nodeW_nT hpl.st) (nodeW_unTp hwr)
    exact fun s c hA => ⟨fun ht => (hT s c (nT_of_at hA ht)).1, (hS.st s c hA).2⟩

omit hX0 in
/-- **`WcWfS.allocW_wcWS` guarded by the thread pointer `t`**
(`WakeWf.allocW_WS_tp`): the counter's context owed only at `t`. -/
theorem allocW_wcWSg (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isaLSE2}
    {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {q : Call} {t : UInt64} (hq : q.OKB ms L.lab)
    (hra : q.ra = (L.lab ".L21_wc_main.sp0").toBitVec)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ Spike.Lib.A64.WakePh.ownW L a j)
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf p c [])
    (hpl : AllocW ms q (fun s c => Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe
      L.endPc (wAR R) (fun m => F m ∧ CallerCells R (-80) (-160) 0 m ∧ WcCtx ms L.lab R J0 q m))
    (hX0a : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (wAR R)
      (fun m => F m ∧ CallerCells R (-80) (-160) 0 m ∧ WcCtx ms L.lab R J0 q m))
    (hctx : ∀ s c, At L.exe L.endPc (wAR R) (fun m => F m ∧ CallerCells R (-80) (-160) 0 m ∧
      WcCtx ms L.lab R J0 q m) (Spike.Lib.A64.Alloc.N L.lab ms q .rmw) s c → TP t s → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (tpG t (WS L a ar p Dt Cl Ctx lbl lsize frM X0)) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc
      (wAR R) (fun m => F m ∧ CallerCells R (-80) (-160) 0 m ∧ WcCtx ms L.lab R J0 q m) := by
  obtain ⟨hR', hal'⟩ := Spike.Lib.A64.WakePh.WcW.wAR_ok hR hal hRlo hhi
  refine Spike.Lib.A64.WakeWf.allocW_WS_tp hp hlo hΛ hlab hsite a hR' hal' (by simp [Spike.Lib.Region.callee])
    (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee])
    hpool hra (fun _ _ => hq.toS) hmp (fun w hw m hm => hmem w hw m hm.1) hno hcl hpl hX0a ?_ hctx
    hctr hheap hoff hnew hlt h64
  refine Spike.Lib.A64SetupPlaced.allocW_of_ctl fun m0 hF s c _ hc => ?_
  obtain ⟨-, -, mC, σC, c', -, ⟨⟨σe, hJe, -⟩, -⟩, hN, -⟩ := hF
  have hq0 : c' = q.c0 := hN.1
  have h0 := hc0J σe c' hJe
  rw [hq0] at h0
  rcases hc with rfl | ⟨o, rfl⟩
  · exact h0
  · exact Spike.Lib.A64.WakePh.WcWfS.cf_hold h0

/-- **`WcWfS.wcPreW_WS` guarded by the thread pointer `t`**: the prologue and
the entry block by `wcPreW_WS`'s, the allocator by `allocW_wcWSg` (the
counter's context `hctx` owed only at `t`). -/
theorem wcPreW_WSg (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isaLSE2}
    {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp t : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ Spike.Lib.A64.WakePh.ownW L a j)
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf p c [])
    (hpl : WcPreW (fun s c => Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F
      ms J0 J0)
    (hX0a : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".L21_wc_main.sp0").toBitVec →
      AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (wAR R)
        (fun m => F m ∧ CallerCells R (-80) (-160) 0 m ∧ WcCtx ms L.lab R J0 q m))
    (hctx : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".L21_wc_main.sp0").toBitVec →
      ∀ s c, At L.exe L.endPc (wAR R) (fun m => F m ∧ CallerCells R (-80) (-160) 0 m ∧
        WcCtx ms L.lab R J0 q m) (Spike.Lib.A64.Alloc.N L.lab ms q .rmw) s c → TP t s → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    WcPreW (tpG t (WS L a ar p Dt Cl Ctx lbl lsize frM X0)) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F
      ms J0 J0 :=
  have hP := Spike.Lib.A64.WakePh.WcWfS.proW_WS (Dt := Dt) (frM := frM) (rS := rS) hp hlo hΛ hlab hsite hcl hX0
    hR hal (by omega) hhi htp hmr hun hc0J hpl.pro
  ⟨⟨Spike.Lib.A64.AllocG.BlkW.imp hP.w0 Spike.Lib.A64.Flow.BlkW.triv fun _ _ h _ _ => h,
      Spike.Lib.A64.AllocG.NodeW.imp hP.w1 Spike.Lib.A64.Flow.NodeW.triv fun _ _ h _ _ => h,
      Spike.Lib.A64.AllocG.BlkW.imp hP.w2 Spike.Lib.A64.Flow.BlkW.triv fun _ _ h _ _ => h,
      Spike.Lib.A64.AllocG.BlkW.imp hP.w3 Spike.Lib.A64.Flow.BlkW.triv fun _ _ h _ _ => h⟩,
    Spike.Lib.A64.AllocG.BlkW.imp
      (Spike.Lib.A64.WakePh.WcWfS.eW_WS hp hlo hΛ hlab hsite hcl hX0 hR hal hRlo hhi hc0J hpl.e)
      Spike.Lib.A64.Flow.BlkW.triv fun _ _ h _ _ => h,
    fun q hq hra => allocW_wcWSg hp hlo hΛ hlab hsite hcl hR hal hRlo hhi hpool hq hra hmp (hmem q hq)
      (hno q hq) hc0J (hpl.alloc q hq hra) (hX0a q hq hra) (hctx q hq hra) hctr hheap hoff hnew hlt h64⟩

end Gen

/-! ## The root's choices -/

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o)

set_option hygiene false in
/-- The root's immediate table (`WakeFinalCAW.iW`). -/
local notation "IW" => Spike.Lib.WakeImmsC0.immsW2 Λ0 SccCode.wakeImms

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hp IW

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The take (`PhRec.K`). -/
local notation "KW" => Spike.Lib.A64.PhRec.K (Ly) RS

set_option hygiene false in
/-- The first TCB's thread pointer. -/
local notation "TW" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The top of the first stack. -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The start's memory side, generic in all but the arena. -/
local notation "MSG" => tpXa (Spike.Lib.A64ConsumerA.msOfA (Ly).Λ μ rd G own (Spike.Lib.WakeOD.arW hp IW) I lbl'
  ls' []) (TW)

set_option hygiene false in
/-- The start's fragment, generic in `Dt`, `Ctx`, `lsize`, `frM`. -/
local notation "WSE" => WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.WakeOD.arW hp IW) wakeSrc Dt
  (Spike.Lib.WakeOD.ClW hp IW) Ctx (L0T (Ly).Λ) lsize frM (X0W (Ly) (Spike.Lib.WakeOSide.aW hp IW E))

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0W)).J σC

set_option hygiene false in
local notation "RW" => fun v => wR (swR v (-384) 0) 336

set_option hygiene false in
local notation "FW" => fun v m0 σC => wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC

/-- **The frame condition pins the switch's base to the top of the first
stack** (`swF`). -/
theorem v_top {v : BitVec 64} {m0 : MachineData} {σC : Spike.Lib.A64.Flow.AS} {m : MachineData}
    (h : (FW) v m0 σC m) : v = TOP :=
  h.1.2.1.1

/-- At a base other than the top no memory satisfies the frame condition. -/
theorem fw_vac {v : BitVec 64} (hv : v ≠ TOP) (m0 : MachineData) (σC : Spike.Lib.A64.Flow.AS) :
    ∀ m, ¬ (FW) v m0 σC m :=
  fun _ h => hv (v_top hp h)

/-- **`hWp` at the root's choices, unguarded** (kept; the guarded form is
`hWp_W`). Open premises: the allocator's counter context
(`hctx`, `Land.hctx_R`) and, until the top's discharge lands, the top
case (`hTop`). -/
theorem hWp_Wu (E : Entry)
    {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.A64ConsumerS.OwnS} {I : Spike.Lib.A64ConsumerS.InvS} {lbl' : Lbl} {ls' : Lsize}
    {Dt : State → Prop} {Ctx : FragS isaLSE2} {lsize : Lsize} {frM : TermRun.Frame}
    /- named premise (commit 2): the top's case -/
    (hTop : ∀ m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (WSE) (KW)) (KW) (Ly).exe (Ly).endPc ((RW) (TOP))
      ((FW) (TOP) m0 σC) (MSG) ((JW) σC) ((JW) σC)) :
    ∀ v m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (WSE) (KW)) (KW) (Ly).exe (Ly).endPc ((RW) v)
      ((FW) v m0 σC) (MSG) ((JW) σC) ((JW) σC) := by
  intro v m0 σC
  by_cases hv : v = TOP
  · subst hv; exact hTop m0 σC
  · exact wcPreW_vac (fw_vac hp hv m0 σC)

/-- **`hWp` at the root's choices** (guarded by the thread pointer, as the chain
consumes it: no `WcPreW.of_unguarded` needed). Open premises: the allocator's counter context
(`hctx`, `Land.hctx_R`) and, until the top's discharge lands, the top
case (`hTop`). -/
theorem hWp_W (E : Entry)
    {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.A64ConsumerS.OwnS} {I : Spike.Lib.A64ConsumerS.InvS} {lbl' : Lbl} {ls' : Lsize}
    {Dt : State → Prop} {Ctx : FragS isaLSE2} {lsize : Lsize} {frM : TermRun.Frame}
    /- named premise (commit 2): the top's case -/
    (hTop : ∀ m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (tpG (TW) (WSE)) (KW)) (KW) (Ly).exe (Ly).endPc ((RW) (TOP))
      ((FW) (TOP) m0 σC) (MSG) ((JW) σC) ((JW) σC)) :
    ∀ v m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (tpG (TW) (WSE)) (KW)) (KW) (Ly).exe (Ly).endPc ((RW) v)
      ((FW) v m0 σC) (MSG) ((JW) σC) ((JW) σC) := by
  intro v m0 σC
  by_cases hv : v = TOP
  · subst hv; exact hTop m0 σC
  · exact wcPreW_vac (fw_vac hp hv m0 σC)

/-- **`hWs` at the root's choices** (guarded by the thread pointer). Open
premises: the box store's writes' obligation at the thread pointer (`hwr`,
`Land.hwr_R`) and, until the top's discharge lands, the top case
(`hTop`). -/
theorem hWs_W (E : Entry)
    {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.A64ConsumerS.OwnS} {I : Spike.Lib.A64ConsumerS.InvS} {lbl' : Lbl} {ls' : Lsize}
    {Dt : State → Prop} {Ctx : FragS isaLSE2} {lsize : Lsize} {frM : TermRun.Frame}
    /- named premise (commit 2): the top's case -/
    (hTop : ∀ m0 σC, WcSp0W (Spike.Lib.A64.Flow.NoMsrW (tpG (TW) (WSE)) (KW)) (KW) (Ly).exe (Ly).endPc
      ((RW) (TOP)) ((FW) (TOP) m0 σC) (MSG) ((JW) σC)) :
    ∀ v m0 σC, WcSp0W (Spike.Lib.A64.Flow.NoMsrW (tpG (TW) (WSE)) (KW)) (KW) (Ly).exe (Ly).endPc
      ((RW) v) ((FW) v m0 σC) (MSG) ((JW) σC) := by
  intro v m0 σC
  by_cases hv : v = TOP
  · subst hv; exact hTop m0 σC
  · exact wcSp0W_vac (fw_vac hp hv m0 σC)

/-! ## The top case -/

set_option hygiene false in
/-- The root's memory side at entry `E`, invariant `I` (`Land.refW` at `I`). -/
local notation "MI" => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks SccCertificate.asm (Ly).Λ) (fun _ => True)
  (Spike.Lib.WakeOG.gW hp IW (Spike.Lib.WakeHG.cTW hp IW))
  (fun s _ => Spike.Lib.A64.WakePh.ownG (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (Spike.Lib.WakeOD.arW hp IW)
  I (L0T (Ly).Λ) (Spike.Lib.WakeLoadT.ls0T (ls0 E)) []

set_option hygiene false in
/-- The start's fragment at the root's context `Land.CtxR`. -/
local notation "WSR" => WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.WakeOD.arW hp IW) wakeSrc
  Spike.Lib.A64.WakeWf.DtW (Spike.Lib.WakeOD.ClW hp IW) (Land.CtxR hp IW ls0 E) (L0T (Ly).Λ)
  (Spike.Lib.WakeLoadT.ls0T (ls0 E)) frM (X0W (Ly) (Spike.Lib.WakeOSide.aW hp IW E))

/-- **A word off the arena's cells and its counter is owned at no phase**
of `ownW`: given the four counters and `a` off them, neither the counter
word nor a word in the cells is owned. -/
theorem not_ownW {L : RuntimeLayout} {a : BitVec 64} {heap cells ctr : Nat}
    (hoff : ∀ w', (w' = L.pnA ∨ w' = L.lockA ∨ w' = L.freeNA ∨ w' = L.nextA ∨ w' = a) →
      ¬ (heap ≤ w'.toNat ∧ w'.toNat < heap + 16 * cells) ∧ w' ≠ BitVec.ofNat 64 ctr)
    {w : BitVec 64} (hw : w = BitVec.ofNat 64 ctr ∨ (heap ≤ w.toNat ∧ w.toNat < heap + 16 * cells)) :
    ∀ j v, (⟨w, 8⟩, v) ∉ Spike.Lib.A64.WakePh.ownW L a j := by
  intro j v hm
  simp only [Spike.Lib.A64.WakePh.ownW, Spike.Lib.A64.PhRec.ownOf, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq, Loc.mk.injEq, and_true] at hm
  have key : ∀ w', (w' = L.pnA ∨ w' = L.lockA ∨ w' = L.freeNA ∨ w' = L.nextA ∨ w' = a) → w = w' → False :=
    fun w' hw' he => by
      subst he
      obtain ⟨h1, h2⟩ := hoff _ hw'
      rcases hw with h | h
      · exact h2 h
      · exact h1 h
  rcases hm with (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩
  · exact key _ (.inl rfl) h
  · exact key _ (.inr (.inl rfl)) h
  · exact key _ (.inr (.inr (.inl rfl))) h
  · exact key _ (.inr (.inr (.inr (.inl rfl)))) h
  · exact key _ (.inr (.inr (.inr (.inr rfl)))) h

/-- **The owned words are off `arW`'s cells and its counter**: the four
counters (`StartH0Ti.offW_arW`) and `scc_rt_nthreads` (`CalWf.hoffN_W`). -/
theorem offW_own (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ w', (w' = (Ly).pnA ∨ w' = (Ly).lockA ∨ w' = (Ly).freeNA ∨ w' = (Ly).nextA ∨
        w' = Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) →
      ¬ ((Spike.Lib.WakeOD.arW hp IW).heap ≤ w'.toNat ∧
        w'.toNat < (Spike.Lib.WakeOD.arW hp IW).heap + 16 * (Spike.Lib.WakeOD.arW hp IW).cells) ∧
      w' ≠ BitVec.ofNat 64 (Spike.Lib.WakeOD.arW hp IW).ctr := fun w' hw' => by
  have hof : ¬ ((Spike.Lib.WakeOD.arW hp IW).heap ≤ w'.toNat ∧
        w'.toNat < (Spike.Lib.WakeOD.arW hp IW).heap + 16 * (Spike.Lib.WakeOD.arW hp IW).cells) ∧
      (⟨w', 8⟩ : Loc) ≠ (Spike.Lib.WakeOD.arW hp IW).ctrLoc := by
    rcases hw' with rfl | rfl | rfl | rfl | rfl
    · exact Spike.Lib.A64.WakePh.StartH0Ti.offW_arW hp IW _ (Ly).pn_mem
    · exact Spike.Lib.A64.WakePh.StartH0Ti.offW_arW hp IW _ (Ly).lock_mem
    · exact Spike.Lib.A64.WakePh.StartH0Ti.offW_arW hp IW _ (Ly).freeN_mem
    · exact Spike.Lib.A64.WakePh.StartH0Ti.offW_arW hp IW _ (Ly).next_mem
    · exact Spike.Lib.A64.WakePh.CalWf.hoffN_W hp IW hA13
  exact ⟨hof.1, fun h => hof.2 (by rw [h]; rfl)⟩

/-- **The switch's region at the top of the first stack** is OK and 16-aligned. -/
theorem rw_top (m0 : MachineData) (σC : Spike.Lib.A64.Flow.AS) :
    ((RW) (TOP)).OK ∧ ((RW) (TOP)).base.toNat % 16 = 0 := by
  have hwf := Spike.Lib.PlaceW.wf_link_of_placeW IW hp
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hok : (swR (TOP) (-384) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ (by decide) (by decide)
  have hF0 := Spike.Lib.A64.Rt.wordsNoneP_swFSL_fstable (a := Spike.Lib.A64.Flow.Ret0.limA (TW))
    (v := TOP) hwf hsub hok (by decide) (by decide)
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ (by decide) (by decide))
    (by rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _)
    (by rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]
        exact Spike.Lib.A64.Rt.rt_houtD _ (by decide) (by decide))
    (Spike.Lib.A64.Rt.fitS_of_sub _ hsub)
  obtain ⟨hR, hal, -⟩ := Spike.Lib.A64.Flow.WakeM.wR_ok (D := 336) (by decide) (by decide) hok
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _) hF0
    (by show (-384 : Int) ≤ -48 - 336; decide) (by show (0 : Int) ≤ 0; decide) m0 σC
  exact ⟨hR, hal⟩

/-- **`hWp_W`'s top case at the root's memory side `MI`** (any invariant
`I`, any `frM`, context `Land.CtxR`): `wcPreW_WSg` at the first stack's top,
inside `NoMsrW`. Every premise is discharged here (the region by `rw_top`,
the counter's context by `Land.hctx_R`, the counter/header words by
`WordsNoneP` and `offW_own`) but the placement `hpl` (`WcPl.hplP_W`). -/
theorem hTopP_Rpl (ls0 : Entry → Lsize) (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.A64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (E : Entry) (I : Spike.Lib.A64ConsumerS.InvS) {frM : TermRun.Frame} (m0 : MachineData)
    (σC : Spike.Lib.A64.Flow.AS)
    (hpl : WcPreW (fun s c => Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ (L0T (Ly).Λ) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc ((RW) (TOP)) ((FW) (TOP) m0 σC) (tpXa (MI) (TW)) ((JW) σC) ((JW) σC)) :
    WcPreW (Spike.Lib.A64.Flow.NoMsrW (tpG (TW) (WSR)) (KW)) (KW) (Ly).exe (Ly).endPc ((RW) (TOP))
      ((FW) (TOP) m0 σC) (tpXa (MI) (TW)) ((JW) σC) ((JW) σC) := by
  have hp' := Spike.Lib.A64.WakePh.StartPlaceLy.hp_W hpa hwp
  have hlo := Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hp IW hlo0
  have hprog := Spike.Lib.WakeSrcCtl.prog_W hp IW hpa hwp
  have hpL : textProgram SccCertificate.asm = .ok (Ly).prog := by rw [hprog]; exact hwp
  have hlab : ∀ l x, codeOf lo wakeProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hp IW l x (by rw [hlo, hp']; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link IW hp)
  have hsite := Spike.Lib.PlaceW.site_ofPlaceW hp IW
  have hax : (Spike.Lib.WakeOSide.aW hp IW E).toBitVec.toNat =
      ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
    rw [Spike.Lib.WakeOSide.aW_site hp IW hpa hwp hpL hsite E]
  have hX0 := Spike.Lib.A64.WakePh.StartGlue.x0W_of_freeN hlab hax
  obtain ⟨hR, hal⟩ := rw_top hp m0 σC
  have hwf := Spike.Lib.PlaceW.wf_link_of_placeW IW hp
  -- the arena
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 :=
    Spike.Lib.A64.Rt.ArenaW.data_below_of_placeW (Spike.Lib.PlaceW.link IW hp)
  obtain ⟨hc1, hc2, -⟩ : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ ∧
      Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size ∧ _ :=
    Spike.Lib.A64.Rt.ArenaW.ctr_item_of_placeW (Spike.Lib.PlaceW.link IW hp) hc
  have hoffQ : ∀ q : Call, q.OKB (tpXa (MI) (TW)) (Ly).lab →
      (tpXa (MI) (TW)).off q.n q.τ ≤ 16 * (tpXa (MI) (TW)).units q.n q.τ := fun q hq => by
    have hu := Spike.Lib.LowerA64.arOf_units_pos (Λ := (Ly).Λ) (n := 1) hq.toS.accs
    have hf := Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) (n := 1) hq.toS.accs
    rw [hq.one]
    show (Spike.Lib.A64.Rt.arOf (Ly).Λ).off 1 q.τ ≤ 16 * (Spike.Lib.A64.Rt.arOf (Ly).Λ).units 1 q.τ
    rw [hf]; omega
  refine Spike.Lib.A64.WakePh.WcWfS.wcPreW_nm hprog
    (wcPreW_WSg hprog hlo hΛ hlab hsite (fun _ h => h.2) hX0 hR hal (by show (-336 : Int) ≤ -240; decide)
      (by show (0 : Int) ≤ 0; decide) ?hpool Spike.Lib.A64.WakePh.WcWfS.tp_wJ0 ?hmr ?hun (fun _ h => h.1)
      ?hmem ?hno (Spike.Lib.A64.WakePh.WcWfS.cf_wJ0 Spike.Lib.WakeC0.c0W_ctl) hpl
      (fun _ _ _ => Spike.Lib.A64.AllocG.AllocW.imp (allocW_free hlab) (Spike.Lib.A64.Alloc.AllocW.triv _ _)
        (fun s _ h _ => hX0 s h))
      (Land.hctx_R hp ls0 hc E (ms := tpXa (MI) (TW)) rfl (TOP) m0 σC) rfl rfl (fun _ _ => rfl) id
      (Land.hlt_R hp IW ls0 hc E) (by show Scc.Cert.PlaceOK.heapUseOf (Ly).Λ < 2 ^ 64; omega))
  case hpool => have := (Ly).pool_fit; omega
  case hmr =>
    rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  case hun =>
    intro m hm
    rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
    exact hm.1.1 _ fun j hj => (((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.2 j hj).elim
      (fun h => .inr (.inl h)) (fun h => .inr (.inr h))
  case hmem =>
    have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
      Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW (Spike.Lib.PlaceW.link IW hp)
    have hwf' : (Ly).Λ.WF := hwf
    have hh : (tpXa (MI) (TW)).heap = (Ly).Λ.heap.lo := rfl
    have hcl : (tpXa (MI) (TW)).cells = Scc.Cert.PlaceOK.allocCells := rfl
    have hct : (tpXa (MI) (TW)).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
    refine Spike.Lib.A64.WakePh.StartGlue.hmemB_of_wordsNone hwf' (fun m h => h.1.1.wn)
      (by rw [hh]; exact Nat.le_refl _) (by rw [hh, hcl]; omega)
      (.inr ⟨by rw [hct]; exact ⟨hc1, by omega⟩, by rw [hct]; exact ⟨by omega, by omega⟩⟩) fun q hq => ?_
    exact hoffQ q hq
  case hno =>
    intro q hq w hw
    refine not_ownW (heap := (tpXa (MI) (TW)).heap) (cells := (tpXa (MI) (TW)).cells)
      (ctr := (tpXa (MI) (TW)).ctr) (fun w' hw' => ?_) ?_
    · exact offW_own hp hA13 w' hw'
    · rcases hw with h | ⟨o', ho, h⟩
      · exact .inl h
      · refine .inr ?_
        have h1 := hoffQ q hq
        have hroom := hq.toS.room
        rw [hq.toS.off] at h1
        rw [Spike.Lib.A64.Alloc.Call.hdrAt] at h
        generalize q.n * (Spike.Lib.A64.Alloc.mOf q.h).toNat = k at h1 h
        omega

/-- **The box at `c0W`** (`WakeC0.c0W_box`): an allocator ghost at `c0W`
boxes an `int` word. -/
theorem tau_c0W {ms : Spike.Lib.MemSide isaLSE2} {lab : Label → Int64} (q : Spike.Lib.A64.Flow.WakeWc.AGB ms lab)
    (hc0 : q.1.c0 = c0W) : q.1.τ = .int := by
  obtain ⟨e0, he0⟩ := Spike.Lib.WakeC0.c0W_box.term
  obtain ⟨w, hw, -⟩ := Spike.Lib.WakeC0.c0W_box.ev
  obtain ⟨_, ht⟩ := q.2.term; rw [hc0, he0] at ht
  obtain ⟨-, ha, -⟩ := Expr.let_.inj ht
  have ha' := (Op.new.inj ha).1
  have hev := q.2.ev; rw [hc0, ← ha', hw] at hev
  exact (Prod.mk.inj (Option.some.inj hev)).1.symm

/-- **`hWs_W`'s top case at the root's memory side `MI`**: `wcSp0W_WSg` at
the first stack's top, inside `NoMsrW`; the box's cell by `WordsNoneP`
(`hcellB_of_wordsNone`, `StartH0.mp_cellW`) and `offW_own`, the store's
obligation by `Land.hwr_R`. Open: the placement `hpl` (`WcPl.hplS_W`). -/
theorem hTopS_Rpl (ls0 : Entry → Lsize) (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.A64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (E : Entry) (I : Spike.Lib.A64ConsumerS.InvS) {frM : TermRun.Frame} (m0 : MachineData)
    (σC : Spike.Lib.A64.Flow.AS)
    (hpl : WcSp0W (fun s c => Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ (L0T (Ly).Λ) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc ((RW) (TOP)) ((FW) (TOP) m0 σC) (tpXa (MI) (TW)) ((JW) σC)) :
    WcSp0W (Spike.Lib.A64.Flow.NoMsrW (tpG (TW) (WSR)) (KW)) (KW) (Ly).exe (Ly).endPc ((RW) (TOP))
      ((FW) (TOP) m0 σC) (tpXa (MI) (TW)) ((JW) σC) := by
  have hp' := Spike.Lib.A64.WakePh.StartPlaceLy.hp_W hpa hwp
  have hlo := Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hp IW hlo0
  have hprog := Spike.Lib.WakeSrcCtl.prog_W hp IW hpa hwp
  have hpL : textProgram SccCertificate.asm = .ok (Ly).prog := by rw [hprog]; exact hwp
  have hlab : ∀ l x, codeOf lo wakeProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hp IW l x (by rw [hlo, hp']; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link IW hp)
  have hsite := Spike.Lib.PlaceW.site_ofPlaceW hp IW
  have hax : (Spike.Lib.WakeOSide.aW hp IW E).toBitVec.toNat =
      ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
    rw [Spike.Lib.WakeOSide.aW_site hp IW hpa hwp hpL hsite E]
  have hX0 := Spike.Lib.A64.WakePh.StartGlue.x0W_of_freeN hlab hax
  obtain ⟨hR, hal⟩ := rw_top hp m0 σC
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW (Spike.Lib.PlaceW.link IW hp)
  have hb : (Ly).Λ.heap.lo + (Ly).Λ.heap.size ≤ 2 ^ 32 :=
    Spike.Lib.A64.Rt.ArenaW.heap_below_of_placeW (Spike.Lib.PlaceW.link IW hp)
  have hh : (tpXa (MI) (TW)).heap = (Ly).Λ.heap.lo := rfl
  have hcl : (tpXa (MI) (TW)).cells = 4194304 := rfl
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hu2 : (tpXa (MI) (TW)).units 1 .int = 2 := rfl
  have hf1 : (tpXa (MI) (TW)).off 1 .int = 8 :=
    Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) (n := 1) (τ := .int) ⟨_, rfl⟩
  refine Spike.Lib.A64.WakePh.WcWfS.wcSp0W_nm hprog
    (wcSp0W_WSg hprog hlo hΛ hlab hsite (fun _ h => h.2) hX0 hR hal (by show (-336 : Int) ≤ -80; decide)
      (by show (0 : Int) ≤ 0; decide) ?hbox (Spike.Lib.A64.WakePh.WcWfS.cf_wJ0 Spike.Lib.WakeC0.c0W_ctl) hpl
      (Land.hwr_R hp ls0 hpa hwp hc E (ms := tpXa (MI) (TW)) rfl (TOP) m0 σC))
  case hbox =>
    intro q o' ⟨σ, hJ⟩ hlo' hle
    have hc0 : q.1.c0 = c0W := (Spike.Lib.A64.WakePh.WcWfS.wJ0_wNC_JS hJ).1
    have hτ := tau_c0W q hc0
    obtain ⟨hmp, hun⟩ := Spike.Lib.A64.WakePh.StartGlue.hcellB_of_wordsNone
      (F := (FW) (TOP) m0 σC) (P := fun q => q.c0 = c0W) (ms := tpXa (MI) (TW))
      (fun _ h => h.1.1.wn) (by rw [hh]; exact Nat.le_refl _) (by rw [hh, hcl]; omega) (by rw [hh, hcl]; omega)
      (fun q hq => by rw [tau_c0W q hq, hf1, hu2]; omega)
      (fun q _ o h1 h2 => Spike.Lib.A64.WakePh.StartH0.mp_cellW hp IW
        (⟨q.1, { q.2 with toS := { q.2.toS with } }⟩ : Spike.Lib.A64.Flow.WakeWc.AGB (MI) (Ly).lab) o h1 h2)
      q hc0 o' hlo' hle
    refine ⟨hmp.1, hun, not_ownW (heap := (tpXa (MI) (TW)).heap) (cells := (tpXa (MI) (TW)).cells)
      (ctr := (tpXa (MI) (TW)).ctr) (fun w' hw' => ?_) (.inr ?_)⟩
    · exact offW_own hp hA13 w' hw'
    · rw [hτ, hu2, hcl] at hle
      rw [hτ, hf1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [hh]; omega), hh, hcl]
      omega

/-- **`hWp_W`'s top case at the root's memory side, closed**: `hTopP_Rpl`
with the placement by `WcPl.hplP_W`. -/
theorem hTopP_R (ls0 : Entry → Lsize) (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.A64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (E : Entry) (I : Spike.Lib.A64ConsumerS.InvS) {frM : TermRun.Frame} (m0 : MachineData)
    (σC : Spike.Lib.A64.Flow.AS) :
    WcPreW (Spike.Lib.A64.Flow.NoMsrW (tpG (TW) (WSR)) (KW)) (KW) (Ly).exe (Ly).endPc ((RW) (TOP))
      ((FW) (TOP) m0 σC) (tpXa (MI) (TW)) ((JW) σC) ((JW) σC) :=
  hTopP_Rpl hp ls0 hpa hwp hlo0 hc hA13 E I m0 σC
    (Spike.Lib.A64.WakePh.WcPl.hplP_W hp (rw_top hp m0 σC).1 (by show (-336 : Int) ≤ -80; decide)
      (by show (0 : Int) ≤ 0; decide) σC)

/-- **`hWs_W`'s top case at the root's memory side, closed**: `hTopS_Rpl`
with the placement by `WcPl.hplS_W`. -/
theorem hTopS_R (ls0 : Entry → Lsize) (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.A64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (E : Entry) (I : Spike.Lib.A64ConsumerS.InvS) {frM : TermRun.Frame} (m0 : MachineData)
    (σC : Spike.Lib.A64.Flow.AS) :
    WcSp0W (Spike.Lib.A64.Flow.NoMsrW (tpG (TW) (WSR)) (KW)) (KW) (Ly).exe (Ly).endPc ((RW) (TOP))
      ((FW) (TOP) m0 σC) (tpXa (MI) (TW)) ((JW) σC) :=
  hTopS_Rpl hp ls0 hpa hwp hlo0 hc hA13 E I m0 σC (Spike.Lib.A64.WakePh.WcPl.hplS_W hp σC)

/-- **Fit at the root, closed**: `hWp_W` and `hWs_W` at
`msBot … (Land.CtxR …) E []` from `hTopP_R`/`hTopS_R`, at every base `v`,
from the layout's facts alone. -/
example (ls0 : Entry → Lsize) (frM : Entry → TermRun.Frame) (E : Entry)
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    (∀ v m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (tpG (TW) (WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab)
        (Spike.Lib.WakeOD.arW hp IW) wakeSrc Spike.Lib.A64.WakeWf.DtW (Spike.Lib.WakeOD.ClW hp IW)
        (Land.CtxR hp IW ls0 E) (L0T (Ly).Λ) (Spike.Lib.WakeLoadT.ls0T (ls0 E)) (frM E)
        (X0W (Ly) (Spike.Lib.WakeOSide.aW hp IW E)))) (KW)) (KW) (Ly).exe (Ly).endPc ((RW) v) ((FW) v m0 σC)
      (tpXa (Spike.Lib.WakeRoot.msBot hp IW ls0 (Land.CtxR hp IW ls0) E []) (TW)) ((JW) σC) ((JW) σC)) ∧
    (∀ v m0 σC, WcSp0W (Spike.Lib.A64.Flow.NoMsrW (tpG (TW) (WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab)
        (Spike.Lib.WakeOD.arW hp IW) wakeSrc Spike.Lib.A64.WakeWf.DtW (Spike.Lib.WakeOD.ClW hp IW)
        (Land.CtxR hp IW ls0 E) (L0T (Ly).Λ) (Spike.Lib.WakeLoadT.ls0T (ls0 E)) (frM E)
        (X0W (Ly) (Spike.Lib.WakeOSide.aW hp IW E)))) (KW)) (KW) (Ly).exe (Ly).endPc ((RW) v) ((FW) v m0 σC)
      (tpXa (Spike.Lib.WakeRoot.msBot hp IW ls0 (Land.CtxR hp IW ls0) E []) (TW)) ((JW) σC)) :=
  ⟨hWp_W hp E fun m0 σC => hTopP_R hp ls0 hpa hwp hlo0 hc hA13 E _ m0 σC,
    hWs_W hp E fun m0 σC => hTopS_R hp ls0 hpa hwp hlo0 hc hA13 E _ m0 σC⟩

/-- **Fit**: `hTopP_Rpl` is `hWp_W`'s `hTop` at the root's memory side
`msBot … (Land.CtxR …) E []`, by unification; with `hWp_W` it gives `hWp`
at every base (the top the only one a memory satisfies: `v_top`). -/
example (ls0 : Entry → Lsize) (frM : Entry → TermRun.Frame) (E : Entry)
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hpl : ∀ m0 σC, WcPreW (fun s c => Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ (L0T (Ly).Λ) s c [])
      (fun _ _ => False) (Ly).exe (Ly).endPc ((RW) (TOP)) ((FW) (TOP) m0 σC)
      (tpXa (Spike.Lib.WakeRoot.msBot hp IW ls0 (Land.CtxR hp IW ls0) E []) (TW)) ((JW) σC) ((JW) σC)) :
    ∀ v m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (tpG (TW) (WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab)
        (Spike.Lib.WakeOD.arW hp IW) wakeSrc Spike.Lib.A64.WakeWf.DtW (Spike.Lib.WakeOD.ClW hp IW)
        (Land.CtxR hp IW ls0 E) (L0T (Ly).Λ) (Spike.Lib.WakeLoadT.ls0T (ls0 E)) (frM E)
        (X0W (Ly) (Spike.Lib.WakeOSide.aW hp IW E)))) (KW)) (KW) (Ly).exe (Ly).endPc ((RW) v) ((FW) v m0 σC)
      (tpXa (Spike.Lib.WakeRoot.msBot hp IW ls0 (Land.CtxR hp IW ls0) E []) (TW)) ((JW) σC) ((JW) σC) :=
  hWp_W hp E fun m0 σC => hTopP_Rpl hp ls0 hpa hwp hlo0 hc hA13 E _ m0 σC (hpl m0 σC)

/-- **Fit**: `hWp_W` and `hWs_W` are `StartH0R.hst0_ofW`'s
`hWp`/`hWs` at the root's memory side `msBot E []`, by unification. -/
example (ls0 : Entry → Lsize) (Ctx : Entry → FragS isaLSE2) (frM : Entry → TermRun.Frame) (E : Entry)
    (hTp : ∀ m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (tpG (TW) (WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab)
        (Spike.Lib.WakeOD.arW hp IW) wakeSrc Spike.Lib.A64.WakeWf.DtW (Spike.Lib.WakeOD.ClW hp IW) (Ctx E)
        (L0T (Ly).Λ) (Spike.Lib.WakeLoadT.ls0T (ls0 E)) (frM E) (X0W (Ly) (Spike.Lib.WakeOSide.aW hp IW E))))
        (KW)) (KW) (Ly).exe (Ly).endPc ((RW) (TOP)) ((FW) (TOP) m0 σC)
      (tpXa (Spike.Lib.WakeRoot.msBot hp IW ls0 Ctx E []) (TW)) ((JW) σC) ((JW) σC))
    (hTs : ∀ m0 σC, WcSp0W (Spike.Lib.A64.Flow.NoMsrW (tpG (TW) (WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab)
        (Spike.Lib.WakeOD.arW hp IW) wakeSrc Spike.Lib.A64.WakeWf.DtW (Spike.Lib.WakeOD.ClW hp IW) (Ctx E)
        (L0T (Ly).Λ) (Spike.Lib.WakeLoadT.ls0T (ls0 E)) (frM E) (X0W (Ly) (Spike.Lib.WakeOSide.aW hp IW E))))
        (KW)) (KW) (Ly).exe (Ly).endPc ((RW) (TOP)) ((FW) (TOP) m0 σC)
      (tpXa (Spike.Lib.WakeRoot.msBot hp IW ls0 Ctx E []) (TW)) ((JW) σC)) :
    (∀ v m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (tpG (TW) (WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab)
        (Spike.Lib.WakeOD.arW hp IW) wakeSrc Spike.Lib.A64.WakeWf.DtW (Spike.Lib.WakeOD.ClW hp IW) (Ctx E)
        (L0T (Ly).Λ) (Spike.Lib.WakeLoadT.ls0T (ls0 E)) (frM E) (X0W (Ly) (Spike.Lib.WakeOSide.aW hp IW E))))
        (KW)) (KW) (Ly).exe (Ly).endPc ((RW) v) ((FW) v m0 σC)
      (tpXa (Spike.Lib.WakeRoot.msBot hp IW ls0 Ctx E []) (TW)) ((JW) σC) ((JW) σC)) ∧
    (∀ v m0 σC, WcSp0W (Spike.Lib.A64.Flow.NoMsrW (tpG (TW) (WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab)
        (Spike.Lib.WakeOD.arW hp IW) wakeSrc Spike.Lib.A64.WakeWf.DtW (Spike.Lib.WakeOD.ClW hp IW) (Ctx E)
        (L0T (Ly).Λ) (Spike.Lib.WakeLoadT.ls0T (ls0 E)) (frM E) (X0W (Ly) (Spike.Lib.WakeOSide.aW hp IW E))))
        (KW)) (KW) (Ly).exe (Ly).endPc ((RW) v) ((FW) v m0 σC)
      (tpXa (Spike.Lib.WakeRoot.msBot hp IW ls0 Ctx E []) (TW)) ((JW) σC)) :=
  ⟨fun v m0 σC => hWp_W hp E hTp v m0 σC, hWs_W hp E hTs⟩

end Spike.Lib.A64.WakePh.WcWfR

/-- info: 'Spike.Lib.A64.WakePh.WcWfR.allocW_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcWfR.allocW_free

/-- info: 'Spike.Lib.A64.WakePh.WcWfR.hWp_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcWfR.hWp_W

/-- info: 'Spike.Lib.A64.WakePh.WcWfR.hWp_Wu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcWfR.hWp_Wu

/-- info: 'Spike.Lib.A64.WakePh.WcWfR.hWs_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcWfR.hWs_W

/-- info: 'Spike.Lib.A64.WakePh.WcWfR.hTopP_Rpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcWfR.hTopP_Rpl

/-- info: 'Spike.Lib.A64.WakePh.WcWfR.hTopS_Rpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcWfR.hTopS_Rpl

/-- info: 'Spike.Lib.A64.WakePh.WcWfR.hTopP_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcWfR.hTopP_R

/-- info: 'Spike.Lib.A64.WakePh.WcWfR.hTopS_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcWfR.hTopS_R
