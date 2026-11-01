/-
**hello.w's `wc_rodata` up to the allocator's return inside the start's level at
any frames** (AArch64, Option A; the `WSHF` twin of
`A64HelloRdWfS`): `HelloRd.RdPreW` at `HelloWf.WSHF … fs` (`W0` at the frames `fs`,
one of `[]` and `[frM]`, `hfs`), moved only by the take (`PhRec.K L rS`). rodata runs
under the setup block's frame `HelloRdCf.frH env`, so its states are at `[frH env]`
(`fs := [frH env]`, `frM := frH env`), where `RdWfS` (fixed at `[]`) is vacuous.
Every lemma is `RdWfS`'s at `fs`: the controls' facts (`hJ`, `hc0J`, `hc1J`: no `ret`
of `main` only at no frame, the runs well formed at `fs`), the frames placed (`hpl`),
the writes' obligations (`hwr`) and the counter's context (`hctx`) at `fs`; the
allocator is `HelloWf.allocW_WSHF`.

- `blkW_rdWSHF`, `nodeW_rdWSHF`: a block, a single instruction of `wc_rodata`.
- `proW_rdWSHF`, `eW_rdWSHF`, `allocW_rdWSHF`, `rdPreW_WSHF`: `wc_rodata` up to the
  allocator's return.
-/
import Spike.Lib.A64HelloRdWfS
import Spike.Lib.A64HelloAllocWSF

namespace Spike.Lib.A64.HelloPh.RdWfSF

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
open Spike.Lib.A64.HelloPh.WcW (freeNH freeAtH freeAt_pcH freeAt_pc0H rdTabH rdW_factH)
open Spike.Lib.A64.HelloWf (WSHF)
open Spike.Lib.A64.Flow.HelloRd (rN RdPreW RdCtx hello_rdPro hello_rdEIn rdEIn)
open Spike.Lib.A64.Flow.Hello1 (rdE rdE_ok aR)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call AllocW)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib (Arena FragS)

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {K : State → State → Prop} {fs : List TermRun.Frame}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s) (hfs : fs = [] ∨ fs = [frM])

include hp hlo hΛ hlab hsite hcl hX0 hfs

/-! ## A block and a node inside `WSHF` -/

/-- **A covered `ret`-free block of `wc_rodata` inside `WSHF`** (`WcWfS.blkW_WSH`
at `rdTabH`): its `SFactsSt2` at `ownGH` (`hst`), its phase fact in `rdTabH`
(`hf`), its abort phases' check (`hph`), its pcs free (`hfree`), its controls'
facts (`hJ`), its frames placed (`hpl`). -/
theorem blkW_rdWSHF {n : ND} {blk : List Directive} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt SccCode.helloProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n blk)
    (hf : PhFact.blk l k blk none none ∈ rdTabH) (hph : Spike.Lib.A64.HelloWf.phOffHC pfxM l k l blk = true)
    (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true) (hfree : freeAtH l k blk.length = true)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (WSHF L a ar p Dt Cl Ctx lbl lsize frM X0 fs) K L.exe L.endPc R F n blk := by
  have hph' := Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab (rapc := 0) (dset := fun _ => false)
    (fun _ h => by cases h) (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h) (rdW_factH hΛ hf)
  have hokpc : ∀ j < blk.length,
      okPcOf lo SccCode.helloProg L.Λ (n.pc + Int64.ofNat (4 * j)).toBitVec.toNat = true := fun j hj => by
    have := List.all_eq_true.mp hph' j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true] at this
    rw [← he]; exact this.1.1
  refine Spike.Lib.A64.WakeWf.blkW_w0 hfs ?_
    (Spike.Lib.A64.HelloPh.WcWf.blkW_wfCH (Dt := Dt) (ar := ar) (Cl := Cl) (Ctx := Ctx) (lsize := lsize)
      hp hlo hlab hsite hb he hok hR hal hlo' hhi hst hokpc hph hnr hcl
      hJ hpl)
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  refine ⟨hX0 _ ?_, fun _ h => h⟩
  have := freeAt_pcH hlab hfree hj
  rw [he] at this
  exact this

/-- **A single instruction of `wc_rodata` without an event inside `WSHF`**
(`WcWfS.nodeW_WSH` at `rdTabH`). -/
theorem nodeW_rdWSHF {n : ND} {l : Label} {k : Nat} (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n)
    (hfree : freeAtH l k 1 = true) (hf : PhFact.step l k ∈ rdTabH)
    (hph : Spike.Lib.A64.HelloWf.siOffHC pfxM l k = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, Kraken.Promising.Lower.A64.CellAt s d 4 ∧
      (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧ isaLSE2.exec s = some tree ∧
      ∀ s' : State, Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n)
    (hwr : NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (WSHF L a ar p Dt Cl Ctx lbl lsize frM X0 fs) K L.exe L.endPc R F n := by
  have hf0 : freeNH n.pc.toBitVec.toNat = true := by rw [← he]; exact freeAt_pc0H hlab hfree
  have hok := (Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab (rdW_factH hΛ hf)).1
  rw [he] at hok
  refine Spike.Lib.A64.WakeWf.nodeW_w0 hfs ?_
    (Spike.Lib.A64.HelloPh.WcWf.nodeW_wfCH (Dt := Dt) (Cl := Cl) hp hlo hlab he hst
      (Spike.Lib.A64.HelloPh.WcWf.htk_of_freeNH hlab hsite hf0) hok hph hstep hcl
      hJ hpl hwr)
  rintro s c ⟨_, _, _, hpc, _⟩
  exact ⟨hX0 _ (by unfold pcOf; rw [hpc]; exact hf0), fun _ h => h⟩

/-! ## Up to the allocator's return -/

set_option maxHeartbeats 1600000 in
/-- **`wc_rodata`'s prologue inside `WSHF`** (`proW_rdGH`'s premises: the thread
pointer `tp` at every entry state, `htp`; its limit word mapped and unmapped,
`hmr`, `hun`), its controls' facts at the entry (`hc0J`), its frames placed
(`hpl`). -/
theorem proW_rdWSHF (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} {J0 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none)
    (hc0J : ∀ σ c, J0 σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : Spike.Lib.A64.Flow.ProW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F ms
      (L.lab "wc_rodata") 48 8 ".L19_wc_rodata.stack_grow" [] J0) :
    Spike.Lib.A64.Flow.ProW (WSHF L a ar p Dt Cl Ctx lbl lsize frM X0 fs) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc
      R F ms (L.lab "wc_rodata") 48 8 ".L19_wc_rodata.stack_grow" [] J0 := by
  have hS := Spike.Lib.A64.HelloPh.WcW.proW_rdGH (Λ := L.Λ) (rS := rS) (ms := ms) hp hlo hΛ hlab hsite a hR hal
    hRlo hhi htp hmr hun
  have h := hello_rdPro
  simp only [Spike.Lib.A64.Flow.HelloRd.rdPro, Spike.Lib.A64.Flow.prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hgap, bHd⟩, bLd⟩, bBr⟩, bFr⟩, -⟩ := h
  have esc : L.lab ".L19_wc_rodata.stack_check" = L.lab "wc_rodata" + Int64.ofNat (4 * 0) :=
    Scc.Cert.Rt.A64.label_labelGap L.lays (by rw [hp]; exact hgap)
  rw [Spike.Lib.A64.Flow.ofNat4_zero] at esc
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact blkW_rdWSHF hp hlo hΛ hlab hsite hcl hX0 hfs (l := ".L19_wc_rodata.stack_check") (k := 0) bHd
      (by rw [Spike.Lib.A64.Flow.ofNat4_zero, esc]) (Spike.Lib.A64.Flow.chkHead_ok (-48) 0 48) hR hal hRlo hhi
      hS.w0 (by decide) (by decide +kernel) (Spike.Lib.A64.Rt.MainU.chkHead_noRet 48) (by free_decH) hc0J
      hpl.w0
  · have hpc : L.lab ".L19_wc_rodata.stack_check" + Int64.ofNat (4 * 2) = L.lab "wc_rodata" + 4 + 4 := by
      rw [Spike.Lib.A64.Rt.MainU.pc2, esc]
    have key : ∀ s c, At L.exe L.endPc R F (Spike.Lib.A64.Flow.proN1 (L.lab "wc_rodata") 48 J0) s c →
        Kraken.Promising.Lower.A64.CellAt s (Spike.Lib.A64.Flow.ldrDir .X10 .X10 8) 4 ∧
        Spike.Lib.A64.Flow.rAddr s.st.1.regs .X10 8 = Spike.Lib.A64.Flow.Ret0.limA tp ∧
        Mem.loadInt s.st.1.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none ∧ s.decls = {} := by
      rintro s c ⟨h1, h2, h3', h4', σ1, hAb, hF, σ0, hJ0, he⟩
      refine ⟨Spike.Lib.A64.HelloPh.WcW.cell1H hp bLd h1 h2 (by rw [h4']; exact hpc.symm), ?_, hun _ hF, h3'⟩
      rw [hAb.regs, he, Spike.Lib.A64.Flow.rAddr_chkRegs]; exact Spike.Lib.A64.Flow.Ret0.tcbA_limA (htp _ _ hJ0)
    refine nodeW_rdWSHF hp hlo hΛ hlab hsite hcl hX0 hfs (l := ".L19_wc_rodata.stack_check") (k := 2) hpc hS.w1
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
  · exact blkW_rdWSHF hp hlo hΛ hlab hsite hcl hX0 hfs (l := ".L19_wc_rodata.stack_check") (k := 3) bBr
      (by rw [Spike.Lib.A64.Rt.MainU.pc3, esc]; rfl) (Spike.Lib.A64.Flow.chkBr_ok (-48) 0 48 _) hR hal hRlo hhi
      hS.w2 (by decide) (by decide +kernel) (Spike.Lib.A64.Rt.MainU.chkBr_noRet _) (by free_decH)
      (fun _ _ ⟨σ, _, hJ0, _⟩ => hc0J σ _ hJ0) hpl.w2
  · exact blkW_rdWSHF hp hlo hΛ hlab hsite hcl hX0 hfs (l := ".L19_wc_rodata.stack_check") (k := 5) bFr
      (by rw [Spike.Lib.A64.Rt.MainU.pc5, esc]; rfl)
      (Spike.Lib.A64.Flow.frameSet_ok (lo := -48) (hi := 0) (by decide) (by decide) (by decide) (Int.le_refl _)
        (by decide)) hR hal hRlo hhi hS.w3 (by decide) (by decide +kernel)
      (by simp [Spike.Lib.A64Consumer.noRetBlk, Spike.Lib.A64.Flow.frameSet, Spike.Lib.A64.Flow.frSetup,
        Spike.Lib.A64.Flow.spStr, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly]) (by free_decH)
      (fun _ _ ⟨σ, _, hJ0, _⟩ => hc0J σ _ hJ0) hpl.w3

/-- **`wc_rodata`'s entry block inside `WSHF`.** -/
theorem eW_rdWSHF (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hc0J : ∀ σ c, J0 σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F
      (rN L.lab J0 J1 .e) rdE) :
    BlkW (WSHF L a ar p Dt Cl Ctx lbl lsize frM X0 fs) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F
      (rN L.lab J0 J1 .e) rdE :=
  blkW_rdWSHF hp hlo hΛ hlab hsite hcl hX0 hfs (l := ".L19_wc_rodata.0_entry") (k := 0)
    (by have := hello_rdEIn; simp only [rdEIn, Bool.and_eq_true] at this; exact this.1)
    (Spike.Lib.A64.Flow.ofNat4_zero _) rdE_ok hR hal hRlo hhi
    (Spike.Lib.A64.HelloPh.WcW.eW_rdGH hp hlo hΛ hlab hsite a hR hal hRlo hhi) (by decide) (by decide +kernel)
    (by decide) (by free_decH) (fun _ _ ⟨σe, hJe, _⟩ => hc0J σe _ hJe) hpl

omit hX0 in
/-- **The allocator inside `WSHF`** at `wc_rodata`'s call (`HelloWf.allocW_WSHF`
at the allocator's region `aR R`, return label `.L19_wc_rodata.sp0`), its
controls' facts from the call context's (`hc1J`, through `RdCtx`: the
allocator's `c0` that of a `J1` state). -/
theorem allocW_rdWSHF (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isaLSE2}
    {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {q : Call} (hq : q.OK ms L.lab)
    (hra : q.ra = (L.lab ".L19_wc_rodata.sp0").toBitVec)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j)
    (hc1J : ∀ σ c, J1 σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : AllocW ms q (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc (aR R)
      (fun m => F m ∧ CallerCells R (-48) (-160) 0 m ∧ RdCtx ms L.lab R J0 J1 q m))
    (hX0a : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (aR R)
      (fun m => F m ∧ CallerCells R (-48) (-160) 0 m ∧ RdCtx ms L.lab R J0 J1 q m))
    (hctx : ∀ s c, At L.exe L.endPc (aR R) (fun m => F m ∧ CallerCells R (-48) (-160) 0 m ∧
      RdCtx ms L.lab R J0 J1 q m) (Spike.Lib.A64.Alloc.N L.lab ms q .rmw) s c → Ctx s c fs)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (WSHF L a ar p Dt Cl Ctx lbl lsize frM X0 fs) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc (aR R)
      (fun m => F m ∧ CallerCells R (-48) (-160) 0 m ∧ RdCtx ms L.lab R J0 J1 q m) := by
  obtain ⟨hR', hal'⟩ := Spike.Lib.A64.HelloPh.WcW.aRH_ok hR hal hRlo hhi
  refine Spike.Lib.A64.HelloWf.allocW_WSHF hp hlo hΛ hlab hsite a hR' hal'
    (by simp [aR, Spike.Lib.Region.callee]) (by simp [aR, Spike.Lib.Region.callee])
    (by simp [aR, Spike.Lib.Region.callee]) (by simp [aR, Spike.Lib.Region.callee])
    hpool hfs (Or.inl rfl) hra (fun _ _ => hq.toS) hmp (fun w hw m hm => hmem w hw m hm.1) hno hcl hpl hX0a ?_ hctx
    hctr hheap hoff hnew hlt h64
  refine Spike.Lib.A64SetupPlaced.allocW_of_ctl fun m0 hF s c _ hc => ?_
  obtain ⟨-, -, mC, σC, c', -, ⟨⟨σe, hJe, -⟩, -⟩, hN, -⟩ := hF
  have hq0 : c' = q.c0 := hN.1
  have h0 := hc1J σe c' hJe
  rw [hq0] at h0
  rcases hc with rfl | ⟨o, rfl⟩
  · exact h0
  · exact ⟨h0.1, Spike.Lib.A64.WakePh.WcWf.RunWf.hold h0.2⟩

/-- **`wc_rodata` up to the allocator's return inside `WSHF`** (`RdPreW`), moved
only by the take: `rdPreW_wcGH`'s premises (`htp`, `hmr`, `hun`, `hpool`,
`hmp`, `hmem`, `hno`), the controls' facts at the entry (`hc0J`) and at the
source advanced (`hc1J`, the allocator's caller), the frames placed per node
(`hpl`), and at every buffer allocation returning to `.sp0` the allocator's
`X0` (`hX0a`) and counter context (`hctx`); the memory side's arena the
arena's (`hctr` … `h64`). -/
theorem rdPreW_WSHF (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isaLSE2}
    {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ q : Call, q.OK ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ q : Call, q.OK ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j)
    (hc0J : ∀ σ c, J0 σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hc1J : ∀ σ c, J1 σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : RdPreW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F ms J0 J1)
    (hX0a : ∀ q : Call, q.OK ms L.lab → q.ra = (L.lab ".L19_wc_rodata.sp0").toBitVec →
      AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (aR R)
        (fun m => F m ∧ CallerCells R (-48) (-160) 0 m ∧ RdCtx ms L.lab R J0 J1 q m))
    (hctx : ∀ q : Call, q.OK ms L.lab → q.ra = (L.lab ".L19_wc_rodata.sp0").toBitVec →
      ∀ s c, At L.exe L.endPc (aR R) (fun m => F m ∧ CallerCells R (-48) (-160) 0 m ∧
        RdCtx ms L.lab R J0 J1 q m) (Spike.Lib.A64.Alloc.N L.lab ms q .rmw) s c → Ctx s c fs)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    RdPreW (WSHF L a ar p Dt Cl Ctx lbl lsize frM X0 fs) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F ms J0 J1 :=
  ⟨proW_rdWSHF hp hlo hΛ hlab hsite hcl hX0 hfs hR hal (by omega) hhi htp hmr hun hc0J hpl.pro,
    eW_rdWSHF hp hlo hΛ hlab hsite hcl hX0 hfs hR hal hRlo hhi hc0J hpl.e,
    fun q hq hra => allocW_rdWSHF hp hlo hΛ hlab hsite hcl hfs hR hal hRlo hhi hpool hq hra hmp (hmem q hq)
      (hno q hq) hc1J (hpl.alloc q hq hra) (hX0a q hq hra) (hctx q hq hra) hctr hheap hoff hnew hlt h64⟩

end Gen

end Spike.Lib.A64.HelloPh.RdWfSF

/-! ## Axioms -/

/-- info: 'Spike.Lib.A64.HelloPh.RdWfSF.proW_rdWSHF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdWfSF.proW_rdWSHF

/-- info: 'Spike.Lib.A64.HelloPh.RdWfSF.eW_rdWSHF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdWfSF.eW_rdWSHF

/-- info: 'Spike.Lib.A64.HelloPh.RdWfSF.allocW_rdWSHF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdWfSF.allocW_rdWSHF

/-- info: 'Spike.Lib.A64.HelloPh.RdWfSF.rdPreW_WSHF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdWfSF.rdPreW_WSHF
