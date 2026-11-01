/-
**hello.w's `wc_main` before the box's landing inside the start's level
`WSH`** (AArch64, hTop; the twin of
`Spike/Lib/A64WakeWcWfS.lean` at helloProg, frame 144): `WcPreWH` and
`WcSp0WH` at `StartWf.WSH` (`W0` at the frames `[]` at `ownGH`), moved only
by the take (`PhRec.K L rS`). Each node is `WcWf.blkW_wfCH`/`nodeW_wfCH` at
its `SFactsSt2` (`WcW.*_wcGH`), `X0` from its free pcs (`hX0`, over
`freeNH`); the allocator is `HelloWf.allocW_WSH`. Generic in the layout `L`, the region `R`, the source, the arena
and the level. No absolute address appears in this file.

- `blkW_WSH`, `nodeW_WSH`: a block, a single instruction inside `WSH`.
- `proW_WSH`, `eW_WSH`, `allocW_wcWSH`, `wcPreW_WSH`: `wc_main` up to the
  allocator's return. Per node the frames placed come bundled (`hpl :
  WcPreWH (PlacedSE · · []) …`); at the allocator also `X0` (`hX0a`) and the
  counter's context (`hctx`). The allocator is `HelloWf.allocW_WSH` at the
  return label `.L22_wc_main.sp0`.
- `wcSp0W_WSH`: `.sp0`'s block and the box's store, whose writes'
  obligation is a premise (`hwr`).
- `wcPreW_nmH`, `wcSp0W_nmH`: inside `NoMsrW`.

Wake's entry section (`wJ0_wNC_JS`, `cf_wJ0`, `tp_wJ0`: `wc_main` entered
straight from `scc_rt_main` after the switch) has no twin here: hello's
`scc_rt_main` calls `wc_rodata` before `wc_main` (`A64HelloMainGlue`), so
`wc_main`'s entry invariant comes from `wc_rodata`'s exit, whose glue does
not exist yet.
-/
import Spike.Lib.A64HelloWcWf
import Spike.Lib.A64HelloWcPreG
import Spike.Lib.A64HelloWcNoMsr
import Spike.Lib.A64HelloStartWf
import Spike.Lib.A64HelloAllocWS
import Spike.Lib.A64SetupPlaced
import Spike.Lib.A64WakeWcWfS

namespace Spike.Lib.A64.HelloPh.WcWfS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (PhFact blockAt okPcOf codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.WakeWf (RunWf NoWrC)
open Spike.Lib.A64.WakePh.WcWfS (cf_hold)
open Spike.Lib.A64.HelloPh.WcW (freeNH freeAtH freeAt_pcH freeAt_pc0H wcTabWH wcW_factH BoxOkH)
open Spike.Lib.A64.HelloPh.StartWf (WSH)
open Spike.Lib.A64.Flow.HelloWc (wNH sNH wcEH wcS0H WcPreWH WcSp0WH wARH WcCtxH)
open Spike.Lib.A64.Flow.WakeWc (AGB boxSt_eq)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call AllocW)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib (Arena FragS)

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {K : State → State → Prop}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

include hp hlo hΛ hlab hsite hcl hX0

/-! ## A block and a node inside `WSH` -/

/-- **A covered `ret`-free block of `wc_main` inside `WSH`**: its
`SFactsSt2` at `ownGH` (`hst`), its phase fact in `wcTabWH` (`hf`, giving
its pcs off the sites), its abort phases' check (`hph`), its pcs free
(`hfree`, giving `X0`), its controls not `main`'s `ret` with their runs well
formed (`hJ`), its frames placed (`hpl`). -/
theorem blkW_WSH {n : ND} {blk : List Directive} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt SccCode.helloProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n blk)
    (hf : PhFact.blk l k blk none none ∈ wcTabWH) (hph : Spike.Lib.A64.HelloWf.phOffHC pfxM l k l blk = true)
    (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true) (hfree : freeAtH l k blk.length = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n blk := by
  have hph' := Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab (rapc := 0) (dset := fun _ => false)
    (fun _ h => by cases h) (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h) (wcW_factH hΛ hf)
  have hokpc : ∀ j < blk.length,
      okPcOf lo SccCode.helloProg L.Λ (n.pc + Int64.ofNat (4 * j)).toBitVec.toNat = true := fun j hj => by
    have := List.all_eq_true.mp hph' j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true] at this
    rw [← he]; exact this.1.1
  refine Spike.Lib.A64.WakeWf.blkW_w0 (.inl rfl) ?_
    (Spike.Lib.A64.HelloPh.WcWf.blkW_wfCH (Dt := Dt) (ar := ar) (Cl := Cl) (Ctx := Ctx) (lsize := lsize)
      hp hlo hlab hsite hb he hok hR hal hlo' hhi hst hokpc hph hnr hcl
      (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl)
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  refine ⟨hX0 _ ?_, fun _ h => h⟩
  have := freeAt_pcH hlab hfree hj
  rw [he] at this
  exact this

/-- **A single instruction of `wc_main` without an event inside `WSH`**:
its `SFactsSt2` at `ownGH` (`hst`), its pc free (`hfree`, giving `X0` and
off the take site), its phase fact in `wcTabWH` (`hf`), its next pc off the
abort phases' (`hph`), its step to `pc + 4` (`hstep`), its controls' facts
(`hJ`), its frames placed (`hpl`), its writes' obligations (`hwr`). -/
theorem nodeW_WSH {n : ND} {l : Label} {k : Nat} (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n)
    (hfree : freeAtH l k 1 = true) (hf : PhFact.step l k ∈ wcTabWH)
    (hph : Spike.Lib.A64.HelloWf.siOffHC pfxM l k = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, Kraken.Promising.Lower.A64.CellAt s d 4 ∧
      (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧ isaLSE2.exec s = some tree ∧
      ∀ s' : State, Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n)
    (hwr : NodeW (NoWrC ar p lbl lsize Ctx []) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  have hf0 : freeNH n.pc.toBitVec.toNat = true := by rw [← he]; exact freeAt_pc0H hlab hfree
  have hok := (Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab (wcW_factH hΛ hf)).1
  rw [he] at hok
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_
    (Spike.Lib.A64.HelloPh.WcWf.nodeW_wfCH (Dt := Dt) (Cl := Cl) hp hlo hlab he hst
      (Spike.Lib.A64.HelloPh.WcWf.htk_of_freeNH hlab hsite hf0) hok hph hstep hcl
      (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl hwr)
  rintro s c ⟨_, _, _, hpc, _⟩
  exact ⟨hX0 _ (by unfold pcOf; rw [hpc]; exact hf0), fun _ h => h⟩

/-! ## Up to the allocator's return -/

set_option maxHeartbeats 1600000 in
/-- **`wc_main`'s prologue inside `WSH`** (`proW_wcGH`'s premises: the
thread pointer `tp` at every entry state, `htp`; its limit word mapped and
unmapped, `hmr`, `hun`), its controls' facts at the entry (`hc0J`), its
frames placed (`hpl`). -/
theorem proW_WSH (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none)
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : Spike.Lib.A64.Flow.ProW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms
      (L.lab "wc_main") 144 8 ".L22_wc_main.stack_grow" [(.X0, 0), (.X1, 8), (.X2, 16), (.X3, 24), (.X4, 32)]
      J0) :
    Spike.Lib.A64.Flow.ProW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc
      R F ms (L.lab "wc_main") 144 8 ".L22_wc_main.stack_grow"
      [(.X0, 0), (.X1, 8), (.X2, 16), (.X3, 24), (.X4, 32)] J0 := by
  have hS := Spike.Lib.A64.HelloPh.WcW.proW_wcGH (Λ := L.Λ) (rS := rS) (ms := ms) hp hlo hΛ hlab hsite a hR hal
    hRlo hhi htp hmr hun
  have h := Spike.Lib.A64.Flow.HelloWc.hello_wcPro
  simp only [Spike.Lib.A64.Flow.HelloWc.hWcPro, Spike.Lib.A64.Flow.prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hgap, bHd⟩, bLd⟩, bBr⟩, bFr⟩, -⟩ := h
  have esc : L.lab ".L22_wc_main.stack_check" = L.lab "wc_main" + Int64.ofNat (4 * 0) :=
    Scc.Cert.Rt.A64.label_labelGap L.lays (by rw [hp]; exact hgap)
  rw [Spike.Lib.A64.Flow.ofNat4_zero] at esc
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact blkW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".L22_wc_main.stack_check") (k := 0) bHd
      (by rw [Spike.Lib.A64.Flow.ofNat4_zero, esc]) (Spike.Lib.A64.Flow.chkHead_ok (-144) 0 144) hR hal hRlo hhi
      hS.w0 (by decide) (by decide +kernel) (Spike.Lib.A64.Rt.MainU.chkHead_noRet 144) (by free_decH) hc0J
      hpl.w0
  · have hpc : L.lab ".L22_wc_main.stack_check" + Int64.ofNat (4 * 2) = L.lab "wc_main" + 4 + 4 := by
      rw [Spike.Lib.A64.Rt.MainU.pc2, esc]
    have key : ∀ s c, At L.exe L.endPc R F (Spike.Lib.A64.Flow.proN1 (L.lab "wc_main") 144 J0) s c →
        Kraken.Promising.Lower.A64.CellAt s (Spike.Lib.A64.Flow.ldrDir .X10 .X10 8) 4 ∧
        Spike.Lib.A64.Flow.rAddr s.st.1.regs .X10 8 = Spike.Lib.A64.Flow.Ret0.limA tp ∧
        Mem.loadInt s.st.1.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none ∧ s.decls = {} := by
      rintro s c ⟨h1, h2, h3', h4', σ1, hAb, hF, σ0, hJ0, he⟩
      refine ⟨Spike.Lib.A64.HelloPh.WcW.cell1H hp bLd h1 h2 (by rw [h4']; exact hpc.symm), ?_, hun _ hF, h3'⟩
      rw [hAb.regs, he, Spike.Lib.A64.Flow.rAddr_chkRegs]; exact Spike.Lib.A64.Flow.Ret0.tcbA_limA (htp _ _ hJ0)
    refine nodeW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".L22_wc_main.stack_check") (k := 2) hpc hS.w1
      (by free_decH) (by decide) (by decide +kernel) ?_ (fun _ _ ⟨σ, hJ0, _⟩ => hc0J σ _ hJ0) hpl.w1
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
  · exact blkW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".L22_wc_main.stack_check") (k := 3) bBr
      (by rw [Spike.Lib.A64.Rt.MainU.pc3, esc]; rfl) (Spike.Lib.A64.Flow.chkBr_ok (-144) 0 144 _) hR hal hRlo hhi
      hS.w2 (by decide) (by decide +kernel) (Spike.Lib.A64.Rt.MainU.chkBr_noRet _) (by free_decH)
      (fun _ _ ⟨σ, _, hJ0, _⟩ => hc0J σ _ hJ0) hpl.w2
  · exact blkW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".L22_wc_main.stack_check") (k := 5) bFr
      (by rw [Spike.Lib.A64.Rt.MainU.pc5, esc]; rfl)
      (Spike.Lib.A64.Flow.frameSet_ok (lo := -144) (hi := 0) (by decide) (by decide) (by decide) (Int.le_refl _)
        (by decide)) hR hal hRlo hhi hS.w3 (by decide) (by decide +kernel)
      (by simp [Spike.Lib.A64Consumer.noRetBlk, Spike.Lib.A64.Flow.frameSet, Spike.Lib.A64.Flow.frSetup,
        Spike.Lib.A64.Flow.spStr, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly]) (by free_decH)
      (fun _ _ ⟨σ, _, hJ0, _⟩ => hc0J σ _ hJ0) hpl.w3

/-- **`wc_main`'s entry block inside `WSH`.** -/
theorem eW_WSH (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F
      (wNH L.lab J0 J1 .e) wcEH) :
    BlkW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F
      (wNH L.lab J0 J1 .e) wcEH :=
  blkW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".L22_wc_main.0_entry") (k := 0)
    (by have := Spike.Lib.A64.Flow.HelloWc.hello_wcEInH
        simp only [Spike.Lib.A64.Flow.HelloWc.wcEInH, Bool.and_eq_true] at this; exact this.1)
    (Spike.Lib.A64.Flow.ofNat4_zero _) Spike.Lib.A64.Flow.HelloWc.wcEH_ok hR hal hRlo hhi
    (Spike.Lib.A64.HelloPh.WcW.eW_wcGH hp hlo hΛ hlab hsite a hR hal hRlo hhi) (by decide) (by decide +kernel)
    (by decide) (by free_decH) (fun _ _ ⟨σe, hJe, _⟩ => hc0J σe _ hJe) hpl

omit hX0 in
/-- **The allocator inside `WSH`** at `wc_main`'s call (`HelloWf.allocW_WSH`
at the allocator's region `wARH R`, return label `.L22_wc_main.sp0`), its
controls' facts from the call context's (`hc1J`, through `WcCtxH`: the
allocator's `c0` that of a `J1` state). -/
theorem allocW_wcWSH (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isaLSE2}
    {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {q : Call} (hq : q.OKB ms L.lab)
    (hra : q.ra = (L.lab ".L22_wc_main.sp0").toBitVec)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j)
    (hc1J : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : AllocW ms q (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc (wARH R)
      (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧ WcCtxH ms L.lab R J0 J1 q m))
    (hX0a : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (wARH R)
      (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧ WcCtxH ms L.lab R J0 J1 q m))
    (hctx : ∀ s c, At L.exe L.endPc (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧
      WcCtxH ms L.lab R J0 J1 q m) (Spike.Lib.A64.Alloc.N L.lab ms q .rmw) s c → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc (wARH R)
      (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧ WcCtxH ms L.lab R J0 J1 q m) := by
  obtain ⟨hR', hal'⟩ := Spike.Lib.A64.HelloPh.WcW.wARH_ok hR hal hRlo hhi
  refine Spike.Lib.A64.HelloWf.allocW_WSH hp hlo hΛ hlab hsite a hR' hal' (by simp [Spike.Lib.Region.callee])
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
  · exact cf_hold h0

/-- **`wc_main` up to the allocator's return inside `WSH`** (`WcPreWH`),
moved only by the take: `wcPreW_wcGH`'s premises (`htp`, `hmr`, `hun`,
`hpool`, `hmp`, `hmem`, `hno`), the controls' facts at the entry (`hc0J`)
and at the source advanced (`hc1J`, the allocator's caller), the frames
placed per node (`hpl`), and at every box allocation returning to `.sp0` the
allocator's `X0` (`hX0a`) and counter context (`hctx`); the memory side's
arena the arena's (`hctr` … `h64`). -/
theorem wcPreW_WSH (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isaLSE2}
    {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
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
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hc1J : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : WcPreWH (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms J0 J1)
    (hX0a : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".L22_wc_main.sp0").toBitVec →
      AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (wARH R)
        (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧ WcCtxH ms L.lab R J0 J1 q m))
    (hctx : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".L22_wc_main.sp0").toBitVec →
      ∀ s c, At L.exe L.endPc (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧
        WcCtxH ms L.lab R J0 J1 q m) (Spike.Lib.A64.Alloc.N L.lab ms q .rmw) s c → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    WcPreWH (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F ms J0 J1 :=
  ⟨proW_WSH hp hlo hΛ hlab hsite hcl hX0 hR hal (by omega) hhi htp hmr hun hc0J hpl.pro,
    eW_WSH hp hlo hΛ hlab hsite hcl hX0 hR hal hRlo hhi hc0J hpl.e,
    fun q hq hra => allocW_wcWSH hp hlo hΛ hlab hsite hcl hR hal hRlo hhi hpool hq hra hmp (hmem q hq)
      (hno q hq) hc1J (hpl.alloc q hq hra) (hX0a q hq hra) (hctx q hq hra) hctr hheap hoff hnew hlt h64⟩

/-! ## `.sp0` -/

/-- **`.sp0`'s block and the box's store inside `WSH`**: `wcSp0W_wcGH`'s
premise (every cell the allocator may return `BoxOkH`, `hbox`), the
controls' facts at the source advanced (`hc1J`, held at `.sp0`), the frames
placed per node (`hpl`), the store's writes' obligation (`hwr`). -/
theorem wcSp0W_WSH (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J1 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOkH L.Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)))
    (hc1J : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : WcSp0WH (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms J1)
    (hwr : NodeW (NoWrC ar p lbl lsize Ctx []) (fun _ _ => False) L.exe L.endPc R F (sNH ms L.lab J1 .st)) :
    WcSp0WH (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F ms J1 := by
  have hS := Spike.Lib.A64.HelloPh.WcW.wcSp0W_wcGH (Λ := L.Λ) (rS := rS) hp hlo hΛ hlab hsite a hR hal hRlo hhi
    hbox
  have hin := Spike.Lib.A64.Flow.HelloWc.hello_wcS0InH
  simp only [Spike.Lib.A64.Flow.HelloWc.wcS0InH, Bool.and_eq_true] at hin
  obtain ⟨h0, h3⟩ := hin
  rw [boxSt_eq] at h3
  refine ⟨?_, ?_⟩
  · exact blkW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".L22_wc_main.sp0") (k := 0) h0
      (Spike.Lib.A64.Flow.ofNat4_zero _) Spike.Lib.A64.Flow.HelloWc.wcS0H_ok hR hal hRlo hhi hS.b
      (by decide) (by decide +kernel) (by decide) (by free_decH)
      (fun _ _ ⟨q, ⟨σe, hJe, _⟩, o, hc, _⟩ => hc ▸ cf_hold (hc1J σe _ hJe)) hpl.b
  · have hI := instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
    exact nodeW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".L22_wc_main.sp0") (k := 3) rfl hS.st (by free_decH)
      (by decide) (by decide +kernel)
      (Spike.Lib.A64.WakeWf.st_step hI (by rw [hp]; exact h3) rfl fun σ c m hJ hF => by
        rw [Spike.Lib.A64.HelloPh.WcW.rAddr_boxH hJ]
        obtain ⟨q, o, hj, hlo', hle, e⟩ := Spike.Lib.A64.HelloPh.WcW.slot_boxH hJ
        rw [e]; exact (hbox q o hj hlo' hle).2.1 m hF)
      (fun _ _ ⟨q, o, ⟨σe, hJe, _⟩, hc, _⟩ => hc ▸ cf_hold (hc1J σe _ hJe)) hpl.st hwr

end Gen

/-! ## Inside `NoMsrW` -/

section NoMsr

variable {L : RuntimeLayout} {W : Spike.Lib.Frag isaLSE2} {K : State → State → Prop} {R : Spike.Lib.Region}
  {F : MachineData → Prop} {ms : Spike.Lib.MemSide isaLSE2}

/-- `WcPreWH` in `L`'s layout of helloProg is inside `NoMsrW`. -/
theorem wcPreW_nmH (hp : L.prog = SccCode.helloProg) {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (h : WcPreWH W K L.exe L.endPc R F ms J0 J1) :
    WcPreWH (Spike.Lib.A64.Flow.NoMsrW W K) K L.exe L.endPc R F ms J0 J1 := by
  have hpS : Scc.Cert.Rt.A64.Lays L.exe SccCode.helloProg L.pfx := hp ▸ L.lays
  have hendS : L.endPc = Scc.Cert.Rt.A64.endOf L.exe SccCode.helloProg L.pfx := by
    show Scc.Cert.Rt.A64.endOf L.exe L.prog L.pfx = _; rw [hp]
  exact Spike.Lib.A64.Flow.HelloWc.WcPreWH.noMsr hpS hendS h

/-- `WcSp0WH` in `L`'s layout of helloProg is inside `NoMsrW`. -/
theorem wcSp0W_nmH (hp : L.prog = SccCode.helloProg) {J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (h : WcSp0WH W K L.exe L.endPc R F ms J1) :
    WcSp0WH (Spike.Lib.A64.Flow.NoMsrW W K) K L.exe L.endPc R F ms J1 := by
  have hpS : Scc.Cert.Rt.A64.Lays L.exe SccCode.helloProg L.pfx := hp ▸ L.lays
  have hendS : L.endPc = Scc.Cert.Rt.A64.endOf L.exe SccCode.helloProg L.pfx := by
    show Scc.Cert.Rt.A64.endOf L.exe L.prog L.pfx = _; rw [hp]
  exact Spike.Lib.A64.Flow.HelloWc.WcSp0WH.noMsr hpS hendS h

end NoMsr

end Spike.Lib.A64.HelloPh.WcWfS

/-! ## Axioms -/

/-- info: 'Spike.Lib.A64.HelloPh.WcWfS.blkW_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcWfS.blkW_WSH

/-- info: 'Spike.Lib.A64.HelloPh.WcWfS.nodeW_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcWfS.nodeW_WSH

/-- info: 'Spike.Lib.A64.HelloPh.WcWfS.proW_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcWfS.proW_WSH

/-- info: 'Spike.Lib.A64.HelloPh.WcWfS.eW_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcWfS.eW_WSH

/-- info: 'Spike.Lib.A64.HelloPh.WcWfS.allocW_wcWSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcWfS.allocW_wcWSH

/-- info: 'Spike.Lib.A64.HelloPh.WcWfS.wcPreW_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcWfS.wcPreW_WSH

/-- info: 'Spike.Lib.A64.HelloPh.WcWfS.wcSp0W_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcWfS.wcSp0W_WSH

/-- info: 'Spike.Lib.A64.HelloPh.WcWfS.wcPreW_nmH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcWfS.wcPreW_nmH

/-- info: 'Spike.Lib.A64.HelloPh.WcWfS.wcSp0W_nmH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcWfS.wcSp0W_nmH
