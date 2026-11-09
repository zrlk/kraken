/-
**wake.w's `wc_main` before the box's landing inside the start's level
at any owned words** (x86-64): `WcPreW` and `WcSp0W` at `W0 … own … []`
(the start's level `StartWf.WS` at `ownG`, `OwnImp.WSX` at `ownGXW`), moved
only by `K`, from the nodes' `SFactsSt2` at `own` (`hS`, e.g.
`WcW.proW_wcG` at `ownG`, `OwnWc.proW_wcGX` at `ownGXW`). Each node is
`CalWf.blkCn` / this file's `nodeW_wfO` at its `SFactsSt2`, `X0` from its
free pcs (`hX0`); the allocator is `allocW_WSO` (`WakeWf.allocW_WS`'s
proof at the allocator's `SFactsSt2` given). Generic in the layout `L`,
the owned words, the region `R`, the source, the arena and the level.

- `blkW_WSO`, `nodeW_WSO`: a block, a single instruction inside the level.
- `proW_WSO`, `eW_WSO`, `allocW_WSO`, `wcPreW_WSO`: `wc_main` up to the
  allocator's return; per node the frames placed come bundled
  (`hpl : WcPreW (PlacedSE · · []) …`); at the allocator also `X0`
  (`hX0a`) and the counter's context (`hctx`).
- `wcSp0W_WSO`: `.x18`'s block and the box's store, whose writes'
  obligation is a premise (`hwr`).

x86-64 twin of `Spike/Lib/A64WakeWcWfS.lean`'s generic part (namespace
`Spike.Lib.X64.WakePh.WcWfS`; names suffixed `O`). **Where this differs
from AArch64**: the owned words are any `own` with the nodes' `SFactsSt2`
premises (`hS`; A64 builds them at `ownG` in place by `WcW.*_wcG`), so the
same lemmas serve the start's level at `ownG` and at `ownGXW`; the allocator
takes its `SFactsSt2` (`hSa`) instead of `allocW_wcG`'s premises (`hmp`,
`hno`); a node's pcs off the sites are decided by `okC` at the labels
(`hokpc`, as `CalWf`; A64 by `wcTabW`'s facts) and its free pcs by
`freeBlk`/`freeAt` (byte offsets; A64 `freeAt l k n` words); the
prologue is x86-64's five-node `XProW` (A64's four-node `ProW`), its
limit's load a `%fs` load (A64 `ldr`); the entry block's call returns to
`.Lwc_main.x0` (A64 `.L21_wc_main.sp0`); the box's store is one
`movq %rax, (%rcx)` at `.x18 + 15` (A64 at `.sp0 + 3` words); no `hal`.
-/
import Spike.Lib.X64WakeWfCal
import Spike.Lib.X64WakeAllocPh
import Spike.Lib.X64WakeWcAllocWI
import Spike.Lib.X64SetupPlaced
import Spike.Lib.X64WakeOwnWcPreX
import Spike.Lib.X64WakeWcPreG

namespace Spike.Lib.X64.WakePh.WcWfS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB codeT_eq label_labelGapB)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW At cellOff okBlk arun fsDir bAddr mB eaddr_mB agrees_of_decls)
open Spike.Lib.X64.Flow (XProW xProN1 xProN2 xProN3 xProN4 xHead xLea xCmp xFr xHead_ok xLea_ok xCmp_ok xFr_ok
  xHead_run xLea_run xCmp_run xFr_run xS1 xS2 hdRegs prologueIn ofNat_add' ofNat_zero')
open Spike.Lib.X64.Rt.MainU (xHead_noRet xLea_noRet xCmp_noRet xFr_noRet)
open Spike.Lib.X64.WakeWf (W0 Wf RunWf NoWrC)
open Spike.Lib.X64.WakePh.WcW (freeN freeAt freeBlk freeAt_pc freeAt_lab freeBlk_pc)
open Spike.Lib.X64.WakePh (instOkW)
open Spike.Lib.X64.WakePh.StartWf (pfxM)
open Spike.Lib.X64.Flow.WakeWc
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Alloc (Call AllocW)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (CellAt fsAddr eaddr exec_movfs_load_agrees exec_store_agrees)

/-- **A held control's facts**: not `main`'s `ret`, its runs well formed at
no frames (the hold read by neither). -/
theorem cf_hold {p : Prog} {ms : Spike.Lib.MemSide isa} {c : Ctl} {o : BitVec 64}
    (h : (∀ a, c.term ≠ .ret a) ∧ RunWf p c []) :
    (∀ a, (holdCtr ms c o).term ≠ .ret a) ∧ RunWf p (holdCtr ms c o) [] :=
  ⟨h.1, Spike.Lib.X64.WakePh.WcWf.RunWf.hold h.2⟩

section Gen

variable {L : RuntimeLayout} {own : Spike.Lib.X64Consumer.Own} {K : State → State → Prop} {rS : Range}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}
  (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeN (pcOf s) = true → X0 s)

set_option hygiene false in
/-- The start's level at the owned words `own`. -/
local notation "WO" => fun s c => W0 L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
  (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize frM X0 s c []

include hp hlo hΛ hlab hsite hcl hX0

/-! ## A block and a node inside the level -/

/-- **A covered `ret`-free block of `wc_main` inside the level**: its
`SFactsSt2` at `own` (`hst`), its pcs off the sites (`hokpc`, `okC`), its
abort phases' check (`hph`), its pcs free (`hfree`, giving `X0`), its
controls not `main`'s `ret` with their runs well formed (`hJ`), its frames
placed (`hpl`). -/
theorem blkW_WSO {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB wakeCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length,
      Spike.Lib.X64.WakePh.okC (L.lab l + Int64.ofNat k + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (hph : Spike.Lib.X64.WakeWf.phOffW pfxM l k l blk = true)
    (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true) (hfree : freeBlk l k blk = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (WO) K L.exe L.endPc R F n blk := by
  refine Spike.Lib.X64.WakeWf.blkW_w0 (.inl rfl) ?_
    (Spike.Lib.X64.WakePh.CalWf.blkCn (Dt := Dt) (ar := ar) (Ctx := Ctx) (lsize := lsize) hp hlo hΛ hlab hsite
      hcl hb he hok hR hlo' hhi hst (fun j hj => by rw [← he]; exact hokpc j hj) hph hnr
      (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl)
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  refine ⟨hX0 _ ?_, fun _ h => h⟩
  show freeN (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true
  rw [← he]; exact freeBlk_pc hlab hfree hj

/-- **A single instruction of `wc_main` without an event inside the
level**: its `SFactsSt2` at `own` (`hst`), its pc off the sites (`hokpc`)
and free (`hfree`, giving `X0`), its next pc off the abort phases' (`hph`),
its step to `pc + z` (`hstep`), its controls' facts (`hJ`), its frames
placed (`hpl`), its writes' obligations (`hwr`). -/
theorem nodeW_WSO {n : ND} {l : Label} {k z : Nat} (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (hokpc : Spike.Lib.X64.WakePh.okC (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hfree : freeAt l [k] = true) (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s' : State, TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n)
    (hwr : NodeW (NoWrC ar p lbl lsize Ctx []) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (WO) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hf0 : freeN n.pc.toBitVec.toNat = true := by
    rw [← he]; exact freeAt_pc hlab hfree (List.mem_singleton.mpr rfl)
  have hJ' : ∀ σ c, n.J σ c → ([] = ([] : List TermRun.Frame) → ∀ a, c.term ≠ .ret a) ∧ RunWf p c [] :=
    fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩
  have hP := Spike.Lib.X64.WakeWf.nodeW_phSt (Cl := Cl) (R := R) (F := F) (μ := Spike.Lib.X64.PhRec.μ L)
    (exe := L.exe) (endPc := L.endPc) he (Spike.Lib.X64.WakeWf.siOffW_sound hlab hph)
    (Spike.Lib.X64.WakePh.CalWf.htkC hlab hsite hokpc) hstep
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_
    (Spike.Lib.X64.WakeWf.nodeW_wf (Spike.Lib.X64.WakePh.CalWf.nodeW_dt hst)
      (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩) hcl
      (fun s c hA => ⟨⟨(Spike.Lib.X64.WakeWf.nodeW_ofJ hJ' s c hA).1.1, (hpl s c hA).1,
        (Spike.Lib.X64.WakeWf.nodeW_ofJ hJ' s c hA).1.2⟩, fun _ h => h⟩) hwr
      (Spike.Lib.X64.WakeWf.nodeW_abortWf_off (Spike.Lib.X64.WakePh.CalWf.habtC hp hlo hΛ hokpc)))
  rintro s c ⟨_, _, _, hpc, _⟩
  exact ⟨hX0 _ (by unfold pcOf; rw [hpc]; exact hf0), fun _ h => h⟩

/-! ## Up to the allocator's return -/

set_option maxHeartbeats 1600000 in
/-- **`wc_main`'s prologue inside the level**: its `SFactsSt2` at `own`
(`hS`), the thread pointer `tp` at every entry state (`htp`) and its limit
word unmapped under `F` (`hun`, the load's step), its controls' facts at
the entry (`hc0J`), its frames placed (`hpl`). -/
theorem proW_WSO (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none)
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hS : XProW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F ms
      (L.lab "wc_main") 64 8 ".Lwc_main.stk" 5 9 3 6 4 [(.rdi, -8, 4)] J0)
    (hpl : XProW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms
      (L.lab "wc_main") 64 8 ".Lwc_main.stk" 5 9 3 6 4 [(.rdi, -8, 4)] J0) :
    XProW (WO) K L.exe L.endPc R F ms (L.lab "wc_main") 64 8 ".Lwc_main.stk" 5 9 3 6 4 [(.rdi, -8, 4)] J0 := by
  obtain ⟨eW, eC, -, -, -, -, -⟩ := Spike.Lib.X64.WakePh.OwnWc.wc_labs hlab (L := L)
  have h := wake_wcPro
  simp only [wcPro, prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩ := h
  have hI := instOkW hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have esc : L.lab ".Lwc_main.chk" = L.lab "wc_main" + Int64.ofNat 4 :=
    label_labelGapB L.lays (by rw [hp]; exact hgap)
  have h4 : L.lab "wc_main" + 1 + 3 = L.lab ".Lwc_main.chk" := by rw [esc, Int64.add_assoc]; rfl
  have e14 : L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 = L.lab ".Lwc_main.chk" + Int64.ofNat 14 := by
    rw [h4, ← ofNat_add']
  have e23 : L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 6 =
      L.lab ".Lwc_main.chk" + Int64.ofNat 23 := by
    rw [e14, ← ofNat_add', ← ofNat_add']
  have hxs : (xS2 64 · |>.regs.fsBase) = fun σ : Spike.Lib.X64.AS => σ.regs.fsBase := by
    funext σ; simp [xS2, xS1, hdRegs, Reg64s.set64]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_WSO hp hlo hΛ hlab hsite hcl hX0 (l := "wc_main") (k := 0) bHd (ofNat_zero' _)
      (xHead_ok (lo := -72) (hi := 0) (by decide) (Int.le_refl _)) hR hRlo hhi hS.w0
      (by intro j hj; rw [eW]; revert j; decide +kernel)
      (by unfold Spike.Lib.X64.WakeWf.phOffW; decide +kernel) xHead_noRet (by wcfreeB_dec) hc0J hpl.w0
  · exact blkW_WSO hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.chk") (k := 0) bLea
      (by show _ = L.lab "wc_main" + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -72) (hi := 0) _ _) hR hRlo hhi hS.w1
      (by intro j hj; rw [eC]; revert j; decide +kernel)
      (by unfold Spike.Lib.X64.WakeWf.phOffW; decide +kernel) (xLea_noRet _ _) (by wcfreeB_dec)
      (fun _ _ ⟨σ0, hJ0, _⟩ => hc0J σ0 _ hJ0) hpl.w1
  · have hbL : blockAtB L.prog ".Lwc_main.chk" 5 [(fsDir .r11 8, 9)] = true := by rw [hp]; exact bLd
    have key : ∀ s c, At L.exe L.endPc R F (xProN2 (L.lab "wc_main") 5 64 J0) s c →
        CellAt s (fsDir .r11 8) 9 ∧
        fsAddr s 9 { base := none, idx := none, disp := .int64 8 } = Spike.Lib.X64.Flow.Ret0.limA tp ∧
        Mem.loadInt s.st.1.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none ∧ s.decls = {} := by
      rintro s c ⟨h1, h2, h3', h4', σ2, hA, hF, σ0, hJ0, rfl⟩
      refine ⟨Spike.Lib.X64.Rt.cellOf hI hbL rfl h1 h2
        (by rw [h4']; show L.lab "wc_main" + 1 + 3 + _ = _; rw [h4]), ?_, hun _ hF, h3'⟩
      rw [show Spike.Lib.X64.Flow.Ret0.limA tp = (xS2 64 σ0).regs.fsBase.toBitVec + (8 : Int64).toBitVec by
        rw [congrFun hxs σ0, htp _ _ hJ0]; rfl]
      simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
    refine nodeW_WSO hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.chk") (k := 5) (z := 9)
      (by show _ = L.lab "wc_main" + 1 + 3 + _; rw [h4]) hS.w2 (by rw [eC]; decide +kernel) (by wcfree_dec)
      (by unfold Spike.Lib.X64.WakeWf.siOffW; decide +kernel) ?_ (fun _ _ ⟨σ0, hJ0, _⟩ => hc0J σ0 _ hJ0) hpl.w2
      (Spike.Lib.X64.WakeWf.nodeW_noWrC fun s c hA =>
        let ⟨hc, ha', hdm, hdc⟩ := key s c hA
        ⟨Spike.Lib.X64ConsumerA.noWr_load (exec_movfs_load_agrees hc ha' hdm (agrees_of_decls hdc _ _)),
          fun _ h => h⟩)
    intro s c hA
    obtain ⟨hc, ha', hdm, hdc⟩ := key s c hA
    refine ⟨_, _, hc, fun w w' h => (by cases h), exec_movfs_load_agrees hc ha' hdm (agrees_of_decls hdc _ _),
      fun s' hu => ?_⟩
    simp only [TreeLeaf] at hu
    obtain ⟨_, rfl⟩ := hu; rfl
  · exact blkW_WSO hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.chk") (k := 14) bCmp
      (by show _ = L.lab "wc_main" + 1 + 3 + _ + _; rw [e14])
      (xCmp_ok (lo := -72) (hi := 0) _ _ _ _) hR hRlo hhi hS.w3
      (by intro j hj; rw [eC]; revert j; decide +kernel)
      (by unfold Spike.Lib.X64.WakeWf.phOffW; decide +kernel) (xCmp_noRet _ _ _) (by wcfreeB_dec)
      (fun _ _ ⟨σ0, _, hJ0, _⟩ => hc0J σ0 _ hJ0) hpl.w3
  · exact blkW_WSO hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.chk") (k := 23) bFr
      (by show _ = L.lab "wc_main" + 1 + 3 + _ + _ + _ + _; rw [e23])
      (xFr_ok (lo := -72) (hi := 0) _ _ _ (by decide)) hR hRlo hhi hS.w4
      (by intro j hj; rw [eC]; revert j; decide +kernel)
      (by unfold Spike.Lib.X64.WakeWf.phOffW; decide +kernel) (xFr_noRet _ _ _) (by wcfreeB_dec)
      (fun _ _ ⟨σ0, _, hJ0, _⟩ => hc0J σ0 _ hJ0) hpl.w4

/-- **`wc_main`'s entry block inside the level.** -/
theorem eW_WSO (hR : R.OK) (hRlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi) {J0 : Spike.Lib.X64.AS → Ctl → Prop}
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hS : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F
      (wN L.lab R J0 .e) wcE)
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F (wN L.lab R J0 .e) wcE) :
    BlkW (WO) K L.exe L.endPc R F (wN L.lab R J0 .e) wcE := by
  obtain ⟨-, -, eE, -, -, -, -⟩ := Spike.Lib.X64.WakePh.OwnWc.wc_labs hlab (L := L)
  exact blkW_WSO hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.entry") (k := 0)
    (by have := wake_wcEIn; simp only [wcEIn, Bool.and_eq_true] at this; exact this.1)
    (ofNat_zero' _) wcE_ok hR hRlo hhi hS (by intro j hj; rw [eE]; revert j; decide +kernel)
    (by unfold Spike.Lib.X64.WakeWf.phOffW; decide +kernel) (by decide) (by wcfreeB_dec)
    (fun _ _ ⟨⟨σe, hJe, _⟩, _⟩ => hc0J σe _ hJe) hpl

omit hX0 in
set_option maxHeartbeats 800000 in
/-- **`scc_rt_alloc` inside the level** (`WakeWf.allocW_WS` at the
allocator's `SFactsSt2` at `own`, `hSa`): per component of `Wf` as there. -/
theorem allocW_WSO {ms : Spike.Lib.MemSide isa} {q : Call}
    (hR : R.OK) (hlo' : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hra : q.ra = (L.lab ".Lwc_main.x0").toBitVec) (hq : ∀ m, F m → q.OKS ms L.lab)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hSa : AllocW ms q (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F)
    (hpl : AllocW ms q (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F)
    (hX0a : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc R F)
    (hcf : AllocW ms q (fun _ c => (∀ a, c.term ≠ .ret a) ∧ RunWf p c []) (fun _ _ => False)
      L.exe L.endPc R F)
    (hctx : ∀ s c, At L.exe L.endPc R F (Spike.Lib.X64.Alloc.N L.lab ms q .rmw) s c → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (WO) K L.exe L.endPc R F := by
  have hI := instOkW hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hA : Spike.Lib.X64.Alloc.allocIn L.prog = true := by
    rw [hp]; exact Spike.Lib.X64.Flow.WakeWc.wake_alloc
  have hph := Spike.Lib.X64.WakePh.WcW.allocPhW (Λ := L.Λ) hΛ hlab
  have hPh := Spike.Lib.X64.WakeWf.allocAbAcW (Cl := Cl) hI hA hph hlab hR hlo' hhi hq hra hmem
  have hAr := Spike.Lib.X64.AllocG.allocArenaS (lbl := lbl) (p := p) hI hA hR hlo' hhi hq hmem hctr hheap
    hoff hnew
  have hCx := Spike.Lib.X64.AllocG.allocCtrS (Ctx := fun s c => Ctx s c []) hI hA hR hlo' hhi hq
    (fun a h => hmem a (.inr h)) hheap hlt h64 hctx
  have hPc := Spike.Lib.X64.AllocG.allocPc (R := R) (F := F) (ms := ms) (q := q) hI hph
  have g1 := Spike.Lib.X64.AllocG.AllocW.imp hX0a hcf (fun _ _ => And.intro)
  have g2 := Spike.Lib.X64.AllocG.AllocW.imp hpl g1 (fun _ _ => And.intro)
  have g3 := Spike.Lib.X64.AllocG.AllocW.imp hPc g2 (fun _ _ => And.intro)
  have g4 := Spike.Lib.X64.AllocG.AllocW.imp hCx g3 (fun _ _ => And.intro)
  have g5 := Spike.Lib.X64.AllocG.AllocW.imp hAr g4 (fun _ _ => And.intro)
  have h2 := Spike.Lib.X64.AllocG.AllocW.imp hPh g5 (fun _ _ => And.intro)
  refine Spike.Lib.X64.AllocG.AllocW.imp hSa h2 ?_
  rintro s c hst ⟨⟨hab, hac⟩, har, hcx, hpc, hpl', hx, hnr, hr⟩
  exact Spike.Lib.X64.WakeWf.W0.intro0 hx (Spike.Lib.X64.WakeWf.Wf.intro
    (Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt hst fun h => h.elim) hab hac hcl (fun _ => hnr) hpl'
    (fun c' fs' hrun L0 hW hne => .inl (har [] c' fs' hrun L0 hW hne lsize)) hcx hr
    (Spike.Lib.X64.WakeWf.abortWf_of_off (hI.off s hpc).1.noAbort))

/-- **`wc_main` up to the allocator's return inside the level** (`WcPreW`
at `J0 = Jc`), moved only by `K`: the nodes' `SFactsSt2` at `own` (`hS`),
the thread pointer and its limit word (`htp`, `hun`), the counter and
headers unmapped (`hmem`), the entry's controls' facts (`hc0J`), the frames
placed per node (`hpl`), and at every box allocation returning to `.x18`
the allocator's `X0` (`hX0a`) and counter context (`hctx`); the memory
side's arena the arena's (`hctr` … `h64`). -/
theorem wcPreW_WSO (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none)
    (hmem : ∀ q : Call, q.OKB ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hS : WcPreW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F ms J0 J0)
    (hpl : WcPreW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms J0 J0)
    (hX0a : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".Lwc_main.x0").toBitVec →
      AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (wAR R)
        (fun m => F m ∧ CallerCells R (-80) (-160) 8 m ∧ WcCtx ms L.lab R J0 q m))
    (hctx : ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".Lwc_main.x0").toBitVec →
      ∀ s c, At L.exe L.endPc (wAR R) (fun m => F m ∧ CallerCells R (-80) (-160) 8 m ∧
        WcCtx ms L.lab R J0 q m) (Spike.Lib.X64.Alloc.N L.lab ms q .rmw) s c → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    WcPreW (WO) K L.exe L.endPc R F ms J0 J0 := by
  obtain ⟨hR', -⟩ := Spike.Lib.X64.WakePh.WcW.wAR_ok hR hR8 hRlo hhi
  refine ⟨proW_WSO hp hlo hΛ hlab hsite hcl hX0 hR (by omega) (by omega) htp hun hc0J hS.pro hpl.pro,
    eW_WSO hp hlo hΛ hlab hsite hcl hX0 hR hRlo hhi hc0J hS.e hpl.e, fun q hq hra => ?_⟩
  refine allocW_WSO hp hlo hΛ hlab hsite hcl hR' (by simp [Spike.Lib.Region.callee])
    (by simp [Spike.Lib.Region.callee]) hra (fun _ _ => hq.toS) (fun w hw m hm => hmem q hq w hw m hm.1)
    (hS.alloc q hq hra) (hpl.alloc q hq hra) (hX0a q hq hra) ?_ (hctx q hq hra) hctr hheap hoff hnew hlt h64
  refine Spike.Lib.X64SetupPlaced.allocW_of_ctl fun m0 hF s c _ hc => ?_
  obtain ⟨-, -, mC, σC, c', -, ⟨⟨σe, hJe, -⟩, -⟩, hN, -⟩ := hF
  have hq0 : c' = q.c0 := hN.1
  have h0 := hc0J σe c' hJe
  rw [hq0] at h0
  rcases hc with rfl | ⟨o, rfl⟩
  · exact h0
  · exact cf_hold h0

/-! ## `.x18` -/

/-- **`.x18`'s block and the box's store inside the level**: the nodes'
`SFactsSt2` at `own` (`hS`), every cell the allocator may return unmapped
under `F` (`hunB`, the store's step), the entry's controls' facts (`hc0J`,
held at `.x18`), the frames placed per node (`hpl`), the store's writes'
obligation (`hwr`). -/
theorem wcSp0W_WSO (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Ctl → Prop}
    (hunB : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J0 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hS : WcSp0W (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F ms J0)
    (hpl : WcSp0W (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms J0)
    (hwr : NodeW (NoWrC ar p lbl lsize Ctx []) (fun _ _ => False) L.exe L.endPc R F (sN ms L.lab R J0 .st)) :
    WcSp0W (WO) K L.exe L.endPc R F ms J0 := by
  obtain ⟨-, -, -, eX, -, -, -⟩ := Spike.Lib.X64.WakePh.OwnWc.wc_labs hlab (L := L)
  have hin := wake_wcS0In
  simp only [wcS0In, Bool.and_eq_true] at hin
  obtain ⟨h0, h3⟩ := hin
  have hI := instOkW hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hb : blockAtB L.prog ".Lwc_main.x0" 15 [(Spike.Lib.X64.stDir .rcx 0 .rax, 3)] = true := by
    rw [hp]; exact h3
  refine ⟨?_, ?_⟩
  · exact blkW_WSO hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.x0") (k := 0) h0 (ofNat_zero' _) wcS0_ok
      hR hRlo hhi hS.b (by intro j hj; rw [eX]; revert j; decide +kernel)
      (by unfold Spike.Lib.X64.WakeWf.phOffW; decide +kernel) (by decide) (by wcfreeB_dec)
      (fun _ _ ⟨q, ⟨σe, hJe, _⟩, _, o, hc, _⟩ => hc ▸ cf_hold (hc0J σe _ hJe)) hpl.b
  · refine nodeW_WSO hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.x0") (k := 15) (z := 3) rfl hS.st
      (by rw [eX]; decide +kernel) (by wcfree_dec) (by unfold Spike.Lib.X64.WakeWf.siOffW; decide +kernel) ?_
      (fun _ _ ⟨q, o, ⟨σe, hJe, _⟩, hc, _⟩ => hc ▸ cf_hold (hc0J σe _ hJe)) hpl.st hwr
    rintro s c ⟨h1, h2, h3', h4', σ, hA, hF, hJ⟩
    have hc := Spike.Lib.X64.Rt.cellOf hI hb rfl h1 h2 h4'
    obtain ⟨q, o, hj, hlo', hle, e⟩ := Spike.Lib.X64.WakePh.WcW.slot_box hJ
    have ha' : eaddr s 3 (mB .rcx 0) = σ.slot (-24) :=
      (eaddr_mB s 3 .rcx 0).trans (by rw [hA.regs]; exact Spike.Lib.X64.WakePh.WcW.bAddr_box hJ)
    refine ⟨_, _, hc, fun w w' h => (by cases h),
      exec_store_agrees hc ha' (by rw [e]; exact hunB q o hj hlo' hle _ hF) (agrees_of_decls h3' _ _),
      fun s' hu => ?_⟩
    simp only [TreeLeaf] at hu
    obtain ⟨_, rfl⟩ := hu; rfl

end Gen

end Spike.Lib.X64.WakePh.WcWfS

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.WakePh.WcWfS.blkW_WSO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfS.blkW_WSO

/-- info: 'Spike.Lib.X64.WakePh.WcWfS.nodeW_WSO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfS.nodeW_WSO

/-- info: 'Spike.Lib.X64.WakePh.WcWfS.wcPreW_WSO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfS.wcPreW_WSO

/-- info: 'Spike.Lib.X64.WakePh.WcWfS.wcSp0W_WSO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfS.wcSp0W_WSO
