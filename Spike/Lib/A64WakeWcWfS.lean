/-
**wake.w's `wc_main` before the box's landing inside the start's level
`WS`** (AArch64): `WcPreW` and `WcSp0W` at `StartWf.WS` (`W0`
at the frames `[]` at `ownG`), moved only by the take (`PhRec.K L rS`), the
form `MainGlue.wake_start_wc_segW`'s `hWp`/`hWs` ask (after `.noMsr`).
Each node is `WcWf.blkW_wfC`/`nodeW_wfC` at its `SFactsSt2` (`WcW.*_wcG`),
`X0` from its free pcs (`hX0`); the allocator is `WakeWf.allocW_WS`.
Generic in the layout `L`, the region `R`, the source, the arena and the
level. No absolute address appears in this file.

- `blkW_WS`, `nodeW_WS`: a block, a single instruction inside `WS`.
- `proW_WS`, `eW_WS`, `allocW_wcWS`, `wcPreW_WS`: `wc_main` up to the
  allocator's return. Per node the frames placed come bundled
  (`hpl : WcPreW (PlacedSE · · []) …`); at the allocator also `X0`
  (`hX0a`) and the counter's context (`hctx`).
- `wcSp0W_WS`: `.sp0`'s block and the box's store, whose writes'
  obligation is a premise (`hwr`).
- `wcPreW_WS_nm`, `wcSp0W_WS_nm`: inside `NoMsrW`.
- `wJ0_wNC_JS`, `cf_wJ0`, `tp_wJ0`: `wc_main`'s entry invariant at the
  start's (`JS`) pins the control to `c0`, the thread pointer and `x0` to
  the first TCB.
-/
import Spike.Lib.A64WakeWcWf
import Spike.Lib.A64WakeWcPreG
import Spike.Lib.A64WakeWcNoMsr
import Spike.Lib.A64WakeAllocWS
import Spike.Lib.A64SetupPlaced
import Spike.Lib.A64WakeMainGlue

namespace Spike.Lib.A64.WakePh.WcWfS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (PhFact blockAt okPcOf codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND BlkW NodeW At holdCtr)
open Spike.Lib.A64.WakeWf (RunWf NoWrC)
open Spike.Lib.A64.WakePh.WcW (freeN freeAt freeAt_pc freeAt_pc0 freeAt_lab freeK wcTabW wcW_fact BoxOk)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.Flow.WakeWc (wN sN wcE wcS0 wcJ WcPreW WcSp0W wAR WcCtx AGB boxSt_eq)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call AllocW)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib (Arena FragS)

/-- The kernel's check of a block's abort phases (`phOffW`). -/
local macro "ph_dec" : tactic => `(tactic| (simp only [Spike.Lib.A64.WakeWf.phOffW, ← codeT_eq]; decide +kernel))
/-- The kernel's check of a node's abort phases (`siOffW`). -/
local macro "si_dec" : tactic => `(tactic| (simp only [Spike.Lib.A64.WakeWf.siOffW, ← codeT_eq]; decide +kernel))

/-- **A held control's facts**: not `main`'s `ret`, its runs well formed at
no frames (the hold read by neither). -/
theorem cf_hold {p : Prog} {ms : Spike.Lib.MemSide isaLSE2} {c : Spike.Lib.Ctl} {o : BitVec 64}
    (h : (∀ a, c.term ≠ .ret a) ∧ RunWf p c []) :
    (∀ a, (holdCtr ms c o).term ≠ .ret a) ∧ RunWf p (holdCtr ms c o) [] :=
  ⟨h.1, Spike.Lib.A64.WakePh.WcWf.RunWf.hold h.2⟩

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {K : State → State → Prop}
  (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeN (pcOf s) = true → X0 s)

include hp hlo hΛ hlab hsite hcl hX0

/-! ## A block and a node inside `WS` -/

/-- **A covered `ret`-free block of `wc_main` inside `WS`**: its
`SFactsSt2` at `ownG` (`hst`), its phase fact in `wcTabW` (`hf`, giving its
pcs off the sites), its abort phases' check (`hph`), its pcs free (`hfree`,
giving `X0`), its controls not `main`'s `ret` with their runs well formed
(`hJ`), its frames placed (`hpl`). -/
theorem blkW_WS {n : ND} {blk : List Directive} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt wakeProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) K L.exe L.endPc R F n blk)
    (hf : PhFact.blk l k blk none none ∈ wcTabW) (hph : Spike.Lib.A64.WakeWf.phOffW pfxM l k l blk = true)
    (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true) (hfree : freeAt l k blk.length = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n blk := by
  have hph' := Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab (rapc := 0) (dset := fun _ => false)
    (fun _ h => by cases h) (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h) (wcW_fact hΛ hf)
  have hokpc : ∀ j < blk.length,
      okPcOf lo wakeProg L.Λ (n.pc + Int64.ofNat (4 * j)).toBitVec.toNat = true := fun j hj => by
    have := List.all_eq_true.mp hph' j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true] at this
    rw [← he]; exact this.1.1
  refine Spike.Lib.A64.WakeWf.blkW_w0 (.inl rfl) ?_
    (Spike.Lib.A64.WakePh.WcWf.blkW_wfC (Dt := Dt) (ar := ar) (Cl := Cl) (Ctx := Ctx) (lsize := lsize)
      hp hlo hlab hsite hb he hok hR hal hlo' hhi hst hokpc hph hnr hcl
      (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl)
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  refine ⟨hX0 _ ?_, fun _ h => h⟩
  have := freeAt_pc hlab hfree hj
  rw [he] at this
  exact this

/-- **A single instruction of `wc_main` without an event inside `WS`**:
its `SFactsSt2` at `ownG` (`hst`), its pc free (`hfree`, giving `X0` and
off the take site), its phase fact in `wcTabW` (`hf`), its next pc off the
abort phases' (`hph`), its step to `pc + 4` (`hstep`), its controls' facts
(`hJ`), its frames placed (`hpl`), its writes' obligations (`hwr`). -/
theorem nodeW_WS {n : ND} {l : Label} {k : Nat} (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) K L.exe L.endPc R F n)
    (hfree : freeAt l k 1 = true) (hf : PhFact.step l k ∈ wcTabW)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, Kraken.Promising.Lower.A64.CellAt s d 4 ∧
      (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧ isaLSE2.exec s = some tree ∧
      ∀ s' : State, Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n)
    (hwr : NodeW (NoWrC ar p lbl lsize Ctx []) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  have hf0 : freeN n.pc.toBitVec.toNat = true := by rw [← he]; exact freeAt_pc0 hlab hfree
  have hok := (Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab (wcW_fact hΛ hf)).1
  rw [he] at hok
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_
    (Spike.Lib.A64.WakePh.WcWf.nodeW_wfC (Dt := Dt) (Cl := Cl) hp hlo hlab he hst
      (Spike.Lib.A64.WakePh.WcWf.htk_of_freeN hlab hsite hf0) hok hph hstep hcl
      (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl hwr)
  rintro s c ⟨_, _, _, hpc, _⟩
  exact ⟨hX0 _ (by unfold pcOf; rw [hpc]; exact hf0), fun _ h => h⟩

/-! ## Up to the allocator's return -/

set_option maxHeartbeats 1600000 in
/-- **`wc_main`'s prologue inside `WS`** (`proW_wcG`'s premises: the thread
pointer `tp` at every entry state, `htp`; its limit word mapped and
unmapped, `hmr`, `hun`), its controls' facts at the entry (`hc0J`), its
frames placed (`hpl`). -/
theorem proW_WS (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none)
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : Spike.Lib.A64.Flow.ProW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms
      (L.lab "wc_main") 80 8 ".L21_wc_main.stack_grow" [(.X0, 0)] J0) :
    Spike.Lib.A64.Flow.ProW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc
      R F ms (L.lab "wc_main") 80 8 ".L21_wc_main.stack_grow" [(.X0, 0)] J0 := by
  have hS := Spike.Lib.A64.WakePh.WcW.proW_wcG (Λ := L.Λ) (rS := rS) (ms := ms) hp hlo hΛ hlab hsite a hR hal hRlo hhi
    htp hmr hun
  have h := Spike.Lib.A64.Flow.WakeWc.wake_wcPro
  simp only [Spike.Lib.A64.Flow.WakeWc.wcPro, Spike.Lib.A64.Flow.prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hgap, bHd⟩, bLd⟩, bBr⟩, bFr⟩, -⟩ := h
  have esc : L.lab ".L21_wc_main.stack_check" = L.lab "wc_main" + Int64.ofNat (4 * 0) :=
    Scc.Cert.Rt.A64.label_labelGap L.lays (by rw [hp]; exact hgap)
  rw [Spike.Lib.A64.Flow.ofNat4_zero] at esc
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact blkW_WS hp hlo hΛ hlab hsite hcl hX0 (l := ".L21_wc_main.stack_check") (k := 0) bHd
      (by rw [Spike.Lib.A64.Flow.ofNat4_zero, esc]) (Spike.Lib.A64.Flow.chkHead_ok (-80) 0 80) hR hal hRlo hhi
      hS.w0 (by simp [wcTabW]) (by ph_dec) (Spike.Lib.A64.Rt.MainU.chkHead_noRet 80) (by free_dec) hc0J hpl.w0
  · have hpc : L.lab ".L21_wc_main.stack_check" + Int64.ofNat (4 * 2) = L.lab "wc_main" + 4 + 4 := by
      rw [Spike.Lib.A64.Rt.MainU.pc2, esc]
    have key : ∀ s c, At L.exe L.endPc R F (Spike.Lib.A64.Flow.proN1 (L.lab "wc_main") 80 J0) s c →
        Kraken.Promising.Lower.A64.CellAt s (Spike.Lib.A64.Flow.ldrDir .X10 .X10 8) 4 ∧
        Spike.Lib.A64.Flow.rAddr s.st.1.regs .X10 8 = Spike.Lib.A64.Flow.Ret0.limA tp ∧
        Mem.loadInt s.st.1.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none ∧ s.decls = {} := by
      rintro s c ⟨h1, h2, h3', h4', σ1, hAb, hF, σ0, hJ0, he⟩
      refine ⟨Spike.Lib.A64.WakePh.WcW.cell1 hp bLd h1 h2 (by rw [h4']; exact hpc.symm), ?_, hun _ hF, h3'⟩
      rw [hAb.regs, he, Spike.Lib.A64.Flow.rAddr_chkRegs]; exact Spike.Lib.A64.Flow.Ret0.tcbA_limA (htp _ _ hJ0)
    refine nodeW_WS hp hlo hΛ hlab hsite hcl hX0 (l := ".L21_wc_main.stack_check") (k := 2) hpc hS.w1
      (by free_dec) (by simp [wcTabW]) (by si_dec) ?_ (fun _ _ ⟨σ, hJ0, _⟩ => hc0J σ _ hJ0) hpl.w1
      (Spike.Lib.A64.WakeWf.nodeW_noWrC fun s c hA =>
        let ⟨hc, ha', hdm, hdc⟩ := key s c hA
        ⟨Spike.Lib.A64ConsumerA.noWr_load (Kraken.Promising.Lower.A64.exec_ldr_agrees hc ha' hdm
          (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)), fun _ h => h⟩)
    intro s c hA
    obtain ⟨hc, ha', hdm, hdc⟩ := key s c hA
    refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_ldr_agrees hc ha' hdm
      (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _), fun s' hu => ?_⟩
    · cases h
    · obtain ⟨_, hu⟩ := hu
      simp only [Scc.Sem.TreeLeaf] at hu
      subst hu; rfl
  · exact blkW_WS hp hlo hΛ hlab hsite hcl hX0 (l := ".L21_wc_main.stack_check") (k := 3) bBr
      (by rw [Spike.Lib.A64.Rt.MainU.pc3, esc]; rfl) (Spike.Lib.A64.Flow.chkBr_ok (-80) 0 80 _) hR hal hRlo hhi
      hS.w2 (by simp [wcTabW]) (by ph_dec) (Spike.Lib.A64.Rt.MainU.chkBr_noRet _) (by free_dec)
      (fun _ _ ⟨σ, _, hJ0, _⟩ => hc0J σ _ hJ0) hpl.w2
  · exact blkW_WS hp hlo hΛ hlab hsite hcl hX0 (l := ".L21_wc_main.stack_check") (k := 5) bFr
      (by rw [Spike.Lib.A64.Rt.MainU.pc5, esc]; rfl)
      (Spike.Lib.A64.Flow.frameSet_ok (lo := -80) (hi := 0) (by decide) (by decide) (by decide) (Int.le_refl _)
        (by decide)) hR hal hRlo hhi hS.w3 (by simp [wcTabW]) (by ph_dec)
      (by simp [Spike.Lib.A64Consumer.noRetBlk, Spike.Lib.A64.Flow.frameSet, Spike.Lib.A64.Flow.frSetup,
        Spike.Lib.A64.Flow.spStr, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly]) (by free_dec)
      (fun _ _ ⟨σ, _, hJ0, _⟩ => hc0J σ _ hJ0) hpl.w3

/-- **`wc_main`'s entry block inside `WS`.** -/
theorem eW_WS (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi)
    {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F (wN L.lab J0 .e) wcE) :
    BlkW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F
      (wN L.lab J0 .e) wcE :=
  blkW_WS hp hlo hΛ hlab hsite hcl hX0 (l := ".L21_wc_main.0_entry") (k := 0)
    (by have := Spike.Lib.A64.Flow.WakeWc.wake_wcEIn
        simp only [Spike.Lib.A64.Flow.WakeWc.wcEIn, Bool.and_eq_true] at this; exact this.1)
    (Spike.Lib.A64.Flow.ofNat4_zero _) Spike.Lib.A64.Flow.WakeWc.wcE_ok hR hal hRlo hhi
    (Spike.Lib.A64.WakePh.WcW.eW_wcG hp hlo hΛ hlab hsite a hR hal hRlo hhi) (by simp [wcTabW]) (by ph_dec)
    (by decide) (by free_dec) (fun _ _ ⟨σe, hJe, _⟩ => hc0J σe _ hJe) hpl

omit hX0 in
/-- **The allocator inside `WS`** at `wc_main`'s call (`WakeWf.allocW_WS`
at the allocator's region `wAR R`), its controls' facts from the call
context's (`hc0J`, through `WcCtx`). -/
theorem allocW_wcWS (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isaLSE2}
    {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {q : Call} (hq : q.OKB ms L.lab)
    (hra : q.ra = (L.lab ".L21_wc_main.sp0").toBitVec)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownW L a j)
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : AllocW ms q (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc (wAR R)
      (fun m => F m ∧ CallerCells R (-80) (-160) 0 m ∧ WcCtx ms L.lab R J0 q m))
    (hX0a : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (wAR R)
      (fun m => F m ∧ CallerCells R (-80) (-160) 0 m ∧ WcCtx ms L.lab R J0 q m))
    (hctx : ∀ s c, At L.exe L.endPc (wAR R) (fun m => F m ∧ CallerCells R (-80) (-160) 0 m ∧
      WcCtx ms L.lab R J0 q m) (Spike.Lib.A64.Alloc.N L.lab ms q .rmw) s c → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc (wAR R)
      (fun m => F m ∧ CallerCells R (-80) (-160) 0 m ∧ WcCtx ms L.lab R J0 q m) := by
  obtain ⟨hR', hal'⟩ := Spike.Lib.A64.WakePh.WcW.wAR_ok hR hal hRlo hhi
  refine Spike.Lib.A64.WakeWf.allocW_WS hp hlo hΛ hlab hsite a hR' hal' (by simp [Spike.Lib.Region.callee])
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
  · exact cf_hold h0

/-- **`wc_main` up to the allocator's return inside `WS`** (`WcPreW` at
`J0 = Jc`), moved only by the take: `wcPreW_wcG`'s premises (`htp`, `hmr`,
`hun`, `hpool`, `hmp`, `hmem`, `hno`), the entry's controls' facts
(`hc0J`), the frames placed per node (`hpl`), and at every box allocation
returning to `.sp0` the allocator's `X0` (`hX0a`) and counter context
(`hctx`); the memory side's arena the arena's (`hctr` … `h64`). -/
theorem wcPreW_WS (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isaLSE2}
    {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownW L a j)
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : WcPreW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms J0 J0)
    (hX0a : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".L21_wc_main.sp0").toBitVec →
      AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (wAR R)
        (fun m => F m ∧ CallerCells R (-80) (-160) 0 m ∧ WcCtx ms L.lab R J0 q m))
    (hctx : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".L21_wc_main.sp0").toBitVec →
      ∀ s c, At L.exe L.endPc (wAR R) (fun m => F m ∧ CallerCells R (-80) (-160) 0 m ∧
        WcCtx ms L.lab R J0 q m) (Spike.Lib.A64.Alloc.N L.lab ms q .rmw) s c → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    WcPreW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F ms J0 J0 :=
  ⟨proW_WS hp hlo hΛ hlab hsite hcl hX0 hR hal (by omega) hhi htp hmr hun hc0J hpl.pro,
    eW_WS hp hlo hΛ hlab hsite hcl hX0 hR hal hRlo hhi hc0J hpl.e,
    fun q hq hra => allocW_wcWS hp hlo hΛ hlab hsite hcl hR hal hRlo hhi hpool hq hra hmp (hmem q hq)
      (hno q hq) hc0J (hpl.alloc q hq hra) (hX0a q hq hra) (hctx q hq hra) hctr hheap hoff hnew hlt h64⟩

/-! ## `.sp0` -/

/-- **`.sp0`'s block and the box's store inside `WS`**: `wcSp0W_wcG`'s
premise (every cell the allocator may return `BoxOk`, `hbox`), the entry's
controls' facts (`hc0J`, held at `.sp0`), the frames placed per node
(`hpl`), the store's writes' obligation (`hwr`). -/
theorem wcSp0W_WS (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOk L.Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)))
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : WcSp0W (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms J0)
    (hwr : NodeW (NoWrC ar p lbl lsize Ctx []) (fun _ _ => False) L.exe L.endPc R F (sN ms L.lab J0 .st)) :
    WcSp0W (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F ms J0 := by
  have hS := Spike.Lib.A64.WakePh.WcW.wcSp0W_wcG (Λ := L.Λ) (rS := rS) hp hlo hΛ hlab hsite a hR hal hRlo hhi
    hbox
  have hin := Spike.Lib.A64.Flow.WakeWc.wake_wcS0In
  simp only [Spike.Lib.A64.Flow.WakeWc.wcS0In, Bool.and_eq_true] at hin
  obtain ⟨h0, h3⟩ := hin
  rw [boxSt_eq] at h3
  refine ⟨?_, ?_⟩
  · exact blkW_WS hp hlo hΛ hlab hsite hcl hX0 (l := ".L21_wc_main.sp0") (k := 0) h0
      (Spike.Lib.A64.Flow.ofNat4_zero _) Spike.Lib.A64.Flow.WakeWc.wcS0_ok hR hal hRlo hhi hS.b
      (by simp [wcTabW]) (by ph_dec) (by decide) (by free_dec)
      (fun _ _ ⟨q, ⟨σe, hJe, _⟩, o, hc, _⟩ => hc ▸ cf_hold (hc0J σe _ hJe)) hpl.b
  · have hI := Spike.Lib.A64.WakePh.instOkW hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
    exact nodeW_WS hp hlo hΛ hlab hsite hcl hX0 (l := ".L21_wc_main.sp0") (k := 3) rfl hS.st (by free_dec)
      (by simp [wcTabW]) (by si_dec)
      (Spike.Lib.A64.WakeWf.st_step hI (by rw [hp]; exact h3) rfl fun σ c m hJ hF => by
        rw [Spike.Lib.A64.WakePh.WcW.rAddr_box hJ]
        obtain ⟨q, o, hj, hlo', hle, e⟩ := Spike.Lib.A64.WakePh.WcW.slot_box hJ
        rw [e]; exact (hbox q o hj hlo' hle).2.1 m hF)
      (fun _ _ ⟨q, o, ⟨σe, hJe, _⟩, hc, _⟩ => hc ▸ cf_hold (hc0J σe _ hJe)) hpl.st hwr

end Gen

/-! ## Inside `NoMsrW` -/

section NoMsr

variable {L : RuntimeLayout} {W : Spike.Lib.Frag isaLSE2} {K : State → State → Prop} {R : Spike.Lib.Region}
  {F : MachineData → Prop} {ms : Spike.Lib.MemSide isaLSE2}

/-- `WcPreW` in `L`'s layout of `wakeProg` is inside `NoMsrW`. -/
theorem wcPreW_nm (hp : L.prog = wakeProg) {J0 Jc : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (h : WcPreW W K L.exe L.endPc R F ms J0 Jc) :
    WcPreW (Spike.Lib.A64.Flow.NoMsrW W K) K L.exe L.endPc R F ms J0 Jc := by
  have e : SccCode.wakeProg = wakeProg := by decide +kernel
  have hpS : Scc.Cert.Rt.A64.Lays L.exe SccCode.wakeProg L.pfx := e ▸ (hp ▸ L.lays)
  have hendS : L.endPc = Scc.Cert.Rt.A64.endOf L.exe SccCode.wakeProg L.pfx := by
    show Scc.Cert.Rt.A64.endOf L.exe L.prog L.pfx = _; rw [hp, e]
  exact Spike.Lib.A64.Flow.WakeWc.WcPreW.noMsr hpS hendS h

/-- `WcSp0W` in `L`'s layout of `wakeProg` is inside `NoMsrW`. -/
theorem wcSp0W_nm (hp : L.prog = wakeProg) {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (h : WcSp0W W K L.exe L.endPc R F ms J0) :
    WcSp0W (Spike.Lib.A64.Flow.NoMsrW W K) K L.exe L.endPc R F ms J0 := by
  have e : SccCode.wakeProg = wakeProg := by decide +kernel
  have hpS : Scc.Cert.Rt.A64.Lays L.exe SccCode.wakeProg L.pfx := e ▸ (hp ▸ L.lays)
  have hendS : L.endPc = Scc.Cert.Rt.A64.endOf L.exe SccCode.wakeProg L.pfx := by
    show Scc.Cert.Rt.A64.endOf L.exe L.prog L.pfx = _; rw [hp, e]
  exact Spike.Lib.A64.Flow.WakeWc.WcSp0W.noMsr hpS hendS h

end NoMsr

/-! ## `wc_main`'s entry at the start's invariant -/

section Entry

open Spike.Lib.A64.WakePh.MainGlue (JS)
open Spike.Lib.A64.Flow.WakeM (wJ0 wNC)

/-- **`wc_main`'s entry invariant at `scc_rt_main`'s after the switch**
(`MainGlue`'s `wJ0 (wNC L.lab (JS L k0 c0)).J σC`): the control is `c0`,
the thread pointer and `x0` (main's `ThreadId`) the first TCB. -/
theorem wJ0_wNC_JS {L : RuntimeLayout} {k0 : BitVec 64} {c0 : Spike.Lib.Ctl} {σC σ : Spike.Lib.A64.Flow.AS}
    {c : Spike.Lib.Ctl} (h : wJ0 (wNC L.lab (JS L k0 c0)).J σC σ c) :
    c = c0 ∧ σ.regs.TPIDR_EL0 = UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA L.lab + 0#64 + 8#64) ∧
      σ.regs.X0.toBitVec = Spike.Lib.A64.Flow.Ret0.pinA L.lab + 0#64 + 8#64 := by
  obtain ⟨rfl, ⟨σe, ⟨⟨hc, -, htp⟩, hx0⟩, -, -, h48, -, htpC⟩, hX0C, -⟩ := h
  refine ⟨hc, htpC.trans htp, ?_⟩
  show σC.regs.X0.toBitVec = _
  rw [hX0C, h48, hx0]

/-- **The controls' facts at `wc_main`'s entry** (`hc0J`) from `c0`'s. -/
theorem cf_wJ0 {L : RuntimeLayout} {k0 : BitVec 64} {c0 : Spike.Lib.Ctl} {σC : Spike.Lib.A64.Flow.AS} {p : Prog}
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) :
    ∀ σ c, wJ0 (wNC L.lab (JS L k0 c0)).J σC σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [] :=
  fun _ _ h => (wJ0_wNC_JS h).1 ▸ hc0

/-- **The thread pointer at `wc_main`'s entry** (`htp`): the first TCB. -/
theorem tp_wJ0 {L : RuntimeLayout} {k0 : BitVec 64} {c0 : Spike.Lib.Ctl} {σC : Spike.Lib.A64.Flow.AS} :
    ∀ σ c, wJ0 (wNC L.lab (JS L k0 c0)).J σC σ c →
      σ.regs.TPIDR_EL0 = UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA L.lab + 0#64 + 8#64) :=
  fun _ _ h => (wJ0_wNC_JS h).2.1

end Entry

end Spike.Lib.A64.WakePh.WcWfS

/-! ## Axioms -/

/-- info: 'Spike.Lib.A64.WakePh.WcWfS.blkW_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcWfS.blkW_WS

/-- info: 'Spike.Lib.A64.WakePh.WcWfS.nodeW_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcWfS.nodeW_WS

/-- info: 'Spike.Lib.A64.WakePh.WcWfS.wcPreW_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcWfS.wcPreW_WS

/-- info: 'Spike.Lib.A64.WakePh.WcWfS.wcSp0W_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcWfS.wcSp0W_WS

/-- info: 'Spike.Lib.A64.WakePh.WcWfS.wcPreW_nm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcWfS.wcPreW_nm

/-- info: 'Spike.Lib.A64.WakePh.WcWfS.wcSp0W_nm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcWfS.wcSp0W_nm

/-- info: 'Spike.Lib.A64.WakePh.WcWfS.wJ0_wNC_JS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcWfS.wJ0_wNC_JS
