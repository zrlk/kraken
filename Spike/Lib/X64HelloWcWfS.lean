/-
**hello.w's `wc_main` before the box's landing inside the start's level `WSH`** (x86-64; twin of
`Spike/Lib/A64HelloWcWfS.lean`, the hello twin of `Spike/Lib/X64WakeWcWfS.lean` at `helloCells`, frame 128):
`WcPreWH` and `WcSp0WH` at `StartWf.WSH` (`W0` at the frames `[]` at `ownGH`), moved only by the take
(`PhRec.K L rS`). Each node is `WcWf.blkW_wfCH`/`nodeW_wfCH` at its `SFactsSt2` (`WcW.*_wcGH`), `X0` from its
free pcs (`hX0`, over `freeNH`). Generic in the layout `L`, the region `R`, the source, the arena and the level.
No absolute address appears in this file.

- `blkW_WSH`, `nodeW_WSH`: a block, a single instruction inside `WSH`.
- `proW_WSH`, `eW_WSH`, `allocW_wcWSH`, `wcPreW_WSH`: `wc_main` up to the allocator's return. Per node the frames
  placed come bundled (`hpl : WcPreWH (PlacedSE · · []) …`); at the allocator also `X0` (`hX0a`) and the
  counter's context (`hctx`). The allocator's return label is `.Lwc_main.x22`.
- `wcSp0W_WSH`: `.x22`'s block and the box's store, whose writes' obligation is a premise (`hwr`).
- `wcPreW_nsH`, `wcSp0W_nsH`: inside `NoSetFsW`.

Wake's entry section (`wc_main` entered straight from `scc_rt_main` after the switch) has no twin here: hello's
`scc_rt_main` calls `wc_rodata` before `wc_main`, so `wc_main`'s entry invariant comes from `wc_rodata`'s exit.

## Unlike AArch64

- As `X64WakeWcWfS` against `A64WakeWcWfS`: a block sits at a byte offset `k` of a label (`blockAtB helloCells
  l k blk`, `lab l + k`), its instructions at `cellOff blk j`; a single instruction has a size `z` (steps to
  `pc + z`, its phase fact `.step l k z`, its check `siOffW pfxM l k z`), and its cell is not a `syscall`
  (AArch64: not an `SVC`). Free pcs are `freeBlkH`/`freeAtH l os` at byte offsets (AArch64's `freeAtH l k n`
  words). There is no `hal`; the regions' bases are 8-aligned where the allocator's region is formed (`hR8`).
- The prologue is x86-64's five-node `XProW` (frame 128, five argument spills; AArch64's four-node `ProW`, frame
  144), its limit's load a `%fs` load (AArch64 `ldr`); the thread pointer is `fsBase` (AArch64 `TPIDR_EL0`).
- `call` pushes the return address, so the entry block and the allocator need `8 ≤ R.hi` and the allocator's
  region is `wARH R = R.callee (-144) (-160) 8` (AArch64's `hi' = 0`). The bounds are x86-64's frame
  (`R.lo ≤ -136` for the prologue and `.x22`, `-304` for the entry block's call).
- The allocator returns to `.Lwc_main.x22` (AArch64 `.L22_wc_main.sp0`), and the box's store is one
  `movq %rax, (%rcx)` at `.x22 + 15`, the cell at slot `-56` (AArch64 at `.sp0 + 3` words).
- x86-64 has no separate `allocW_WSH` (only the thread-pointer form `HelloWf.allocW_WSH_tp`), so
  `allocW_wcWSH` assembles `WSH` from `WcW.allocW_wcGH`, `HelloWf.allocAbAcH` and `AllocG`'s arena, counter and
  pc lemmas in place, as `X64WakeWcWfS.allocW_WSO` does.
- AArch64's `NoMsrW` lemmas (`wcPreW_nmH`, `wcSp0W_nmH`) become `NoSetFsW` lemmas (`wcPreW_nsH`, `wcSp0W_nsH`):
  the instruction x86-64 must avoid is the `%fs` base's write.
-/
import Spike.Lib.X64HelloWcWf
import Spike.Lib.X64HelloWcPreG
import Spike.Lib.X64HelloWcNoMsr
import Spike.Lib.X64HelloAllocWSTp
import Spike.Lib.X64SetupPlaced
import Spike.Lib.X64WakeWcWfS

namespace Spike.Lib.X64.HelloPh.WcWfS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (PhFact blockAtB okPcOf codeT_eq label_labelGapB)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW At cellOff okBlk fsDir mB eaddr_mB agrees_of_decls)
open Spike.Lib.X64.Flow (XProW xProN2 xHead_ok xLea_ok xCmp_ok xFr_ok xS1 xS2 hdRegs prologueIn ofNat_add'
  ofNat_zero')
open Spike.Lib.X64.Rt.MainU (xHead_noRet xLea_noRet xCmp_noRet xFr_noRet)
open Spike.Lib.X64.WakeWf (W0 Wf RunWf NoWrC)
open Spike.Lib.X64.WakePh.WcWfS (cf_hold)
open Spike.Lib.X64.HelloPh (lo ownGH ownH instOkH)
open Spike.Lib.X64.HelloPh.WcW (freeNH freeAtH freeBlkH freeAt_pcH freeBlk_pcH wcTabWH wcW_factH BoxOkH)
open Spike.Lib.X64.HelloPh.StartWf (WSH pfxM)
open Spike.Lib.X64.Flow.HelloWc (wNH sNH wcEH wcS0H WcPreWH WcSp0WH wARH WcCtxH)
open Spike.Lib.X64.Flow.WakeWc (AGB)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Alloc (Call AllocW)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (CellAt fsAddr eaddr exec_movfs_load_agrees exec_store_agrees)

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {K : State → State → Prop}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

include hp hlo hΛ hlab hsite hcl hX0

/-! ## A block and a node inside `WSH` -/

/-- **A covered `ret`-free block of `wc_main` inside `WSH`**: its `SFactsSt2` at `ownGH` (`hst`), its phase
fact in `wcTabWH` (`hf`, giving its pcs off the sites), its abort phases' check (`hph`), its pcs free (`hfree`,
giving `X0`), its controls not `main`'s `ret` with their runs well formed (`hJ`), its frames placed (`hpl`). -/
theorem blkW_WSH {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n blk)
    (hf : PhFact.blk l k blk none none ∈ wcTabWH) (hph : Spike.Lib.X64.HelloWf.phOffW pfxM l k l blk = true)
    (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true) (hfree : freeBlkH l k blk = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n blk := by
  have hph' := Spike.Lib.X64.Rt.PhOfTab.blkPh_of_factOk hlab (rapc := 0) (dset := fun _ => false)
    (fun _ _ h => by cases h) (fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h) (wcW_factH hΛ hf)
  have hokpc : ∀ j < blk.length,
      okPcOf lo helloCells L.Λ (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true := fun j hj => by
    have := List.all_eq_true.mp hph' j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true] at this
    rw [← he]; exact this.1.1
  refine Spike.Lib.X64.WakeWf.blkW_w0 (.inl rfl) ?_
    (Spike.Lib.X64.HelloPh.WcWf.blkW_wfCH (Dt := Dt) (ar := ar) (Ctx := Ctx) (lsize := lsize)
      hp hlo hlab hsite hb he hok hR hlo' hhi hst hokpc hph hnr hcl
      (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl)
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  refine ⟨hX0 _ ?_, fun _ h => h⟩
  show freeNH (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true
  rw [← he]; exact freeBlk_pcH hlab hfree hj

/-- **A single instruction of `wc_main` without an event inside `WSH`**: its `SFactsSt2` at `ownGH` (`hst`),
its pc free (`hfree`, giving `X0` and off the take site), its phase fact in `wcTabWH` (`hf`), its next pc off
the abort phases' (`hph`), its step to `pc + z` (`hstep`), its controls' facts (`hJ`), its frames placed
(`hpl`), its writes' obligations (`hwr`). -/
theorem nodeW_WSH {n : ND} {l : Label} {k z : Nat} (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n)
    (hfree : freeAtH l [k] = true) (hf : PhFact.step l k z ∈ wcTabWH)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s' : State, TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n)
    (hwr : NodeW (NoWrC ar p lbl lsize Ctx []) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  have hf0 : freeNH n.pc.toBitVec.toNat = true := by
    rw [← he]; exact freeAt_pcH hlab hfree (List.mem_singleton.mpr rfl)
  have hok := (Spike.Lib.X64.Rt.PhOfTab.step_of_factOk hlab (wcW_factH hΛ hf)).1
  rw [he] at hok
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_
    (Spike.Lib.X64.HelloPh.WcWf.nodeW_wfCH (Dt := Dt) (Cl := Cl) hp hlo hlab he hst
      (Spike.Lib.X64.HelloPh.WcWf.htk_of_freeNH hlab hsite hf0) hok hph hstep hcl
      (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl hwr)
  rintro s c ⟨_, _, _, hpc, _⟩
  exact ⟨hX0 _ (by unfold pcOf; rw [hpc]; exact hf0), fun _ h => h⟩

/-! ## Up to the allocator's return -/

set_option maxHeartbeats 1600000 in
/-- **`wc_main`'s prologue inside `WSH`** (`proW_wcGH`'s premises: the thread pointer `tp` at every entry
state, `htp`; its limit word mapped and unmapped, `hmr`, `hun`), its controls' facts at the entry (`hc0J`), its
frames placed (`hpl`). -/
theorem proW_WSH (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) false
      ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none)
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : XProW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms
      (L.lab "wc_main") 128 8 ".Lwc_main.stk" 5 9 3 6 7
      [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4)] J0) :
    XProW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F ms
      (L.lab "wc_main") 128 8 ".Lwc_main.stk" 5 9 3 6 7
      [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4)] J0 := by
  have hS := Spike.Lib.X64.HelloPh.WcW.proW_wcGH (Λ := L.Λ) (rS := rS) (ms := ms) hp hlo hΛ hlab hsite a hR
    hRlo hhi htp hmr hun
  have h := Spike.Lib.X64.Flow.HelloWc.hello_wcPro
  simp only [Spike.Lib.X64.Flow.HelloWc.hWcPro, prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩ := h
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have esc : L.lab ".Lwc_main.chk" = L.lab "wc_main" + Int64.ofNat 4 :=
    label_labelGapB L.lays (by rw [hp]; exact hgap)
  have h4 : L.lab "wc_main" + 1 + 3 = L.lab ".Lwc_main.chk" := by rw [esc, Int64.add_assoc]; rfl
  have e14 : L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 = L.lab ".Lwc_main.chk" + Int64.ofNat 14 := by
    rw [h4, ← ofNat_add']
  have e23 : L.lab "wc_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 6 =
      L.lab ".Lwc_main.chk" + Int64.ofNat 23 := by
    rw [e14, ← ofNat_add', ← ofNat_add']
  have hxs : (xS2 128 · |>.regs.fsBase) = fun σ : Spike.Lib.X64.AS => σ.regs.fsBase := by
    funext σ; simp [xS2, xS1, hdRegs, Reg64s.set64]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := "wc_main") (k := 0) bHd (ofNat_zero' _)
      (xHead_ok (lo := -136) (hi := 0) (by decide) (Int.le_refl _)) hR hRlo hhi hS.w0 (by decide)
      (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) xHead_noRet (by wcfreeBH_dec) hc0J hpl.w0
  · exact blkW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.chk") (k := 0) bLea
      (by show _ = L.lab "wc_main" + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -136) (hi := 0) _ _) hR hRlo hhi hS.w1 (by decide)
      (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (xLea_noRet _ _) (by wcfreeBH_dec)
      (fun _ _ ⟨σ0, hJ0, _⟩ => hc0J σ0 _ hJ0) hpl.w1
  · have hbL : blockAtB L.prog ".Lwc_main.chk" 5 [(fsDir .r11 8, 9)] = true := by rw [hp]; exact bLd
    have key : ∀ s c, At L.exe L.endPc R F (xProN2 (L.lab "wc_main") 5 128 J0) s c →
        CellAt s (fsDir .r11 8) 9 ∧
        fsAddr s 9 { base := none, idx := none, disp := .int64 8 } = Spike.Lib.X64.Flow.Ret0.limA tp ∧
        Mem.loadInt s.st.1.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none ∧ s.decls = {} := by
      rintro s c ⟨h1, h2, h3', h4', σ2, hA, hF, σ0, hJ0, rfl⟩
      refine ⟨Spike.Lib.X64.Rt.cellOf hI hbL rfl h1 h2
        (by rw [h4']; show L.lab "wc_main" + 1 + 3 + _ = _; rw [h4]), ?_, hun _ hF, h3'⟩
      rw [show Spike.Lib.X64.Flow.Ret0.limA tp = (xS2 128 σ0).regs.fsBase.toBitVec + (8 : Int64).toBitVec by
        rw [congrFun hxs σ0, htp _ _ hJ0]; rfl]
      simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
    refine nodeW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.chk") (k := 5) (z := 9)
      (by show _ = L.lab "wc_main" + 1 + 3 + _; rw [h4]) hS.w2 (by wcfreeH_dec) (by decide)
      (by unfold Spike.Lib.X64.HelloWf.siOffW; decide +kernel) ?_ (fun _ _ ⟨σ0, hJ0, _⟩ => hc0J σ0 _ hJ0) hpl.w2
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
  · exact blkW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.chk") (k := 14) bCmp
      (by show _ = L.lab "wc_main" + 1 + 3 + _ + _; rw [e14])
      (xCmp_ok (lo := -136) (hi := 0) _ _ _ _) hR hRlo hhi hS.w3 (by decide)
      (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (xCmp_noRet _ _ _) (by wcfreeBH_dec)
      (fun _ _ ⟨σ0, _, hJ0, _⟩ => hc0J σ0 _ hJ0) hpl.w3
  · exact blkW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.chk") (k := 23) bFr
      (by show _ = L.lab "wc_main" + 1 + 3 + _ + _ + _ + _; rw [e23])
      (xFr_ok (lo := -136) (hi := 0) _ _ _ (by decide)) hR hRlo hhi hS.w4 (by decide)
      (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (xFr_noRet _ _ _) (by wcfreeBH_dec)
      (fun _ _ ⟨σ0, _, hJ0, _⟩ => hc0J σ0 _ hJ0) hpl.w4

/-- **`wc_main`'s entry block inside `WSH`.** -/
theorem eW_WSH (hR : R.OK) (hRlo : R.lo ≤ -304) (hhi : 8 ≤ R.hi)
    {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (hc0J : ∀ σ c, J0 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F
      (wNH L.lab R J0 J1 .e) wcEH) :
    BlkW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F
      (wNH L.lab R J0 J1 .e) wcEH :=
  blkW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.entry") (k := 0)
    (by have := Spike.Lib.X64.Flow.HelloWc.hello_wcEInH
        simp only [Spike.Lib.X64.Flow.HelloWc.wcEInH, Bool.and_eq_true] at this; exact this.1)
    (ofNat_zero' _) Spike.Lib.X64.Flow.HelloWc.wcEH_ok hR hRlo hhi
    (Spike.Lib.X64.HelloPh.WcW.eW_wcGH hp hlo hΛ hlab hsite a hR hRlo hhi) (by decide)
    (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (by decide) (by wcfreeBH_dec)
    (fun _ _ ⟨⟨σe, hJe, _⟩, _⟩ => hc0J σe _ hJe) hpl

omit hX0 in
set_option maxHeartbeats 800000 in
/-- **The allocator inside `WSH`** at `wc_main`'s call (at the allocator's region `wARH R`, return label
`.Lwc_main.x22`): `WcW.allocW_wcGH` (`hpool`, `hmp`, `hmem`, `hno`), both abort phases (`HelloWf.allocAbAcH`),
the arena, the counter's context (`hctx`) and the pcs (`AllocG`), the frames placed (`hpl`), `X0` (`hX0a`), and
its controls' facts from the call context's (`hc1J`, through `WcCtxH`: the allocator's `c0` that of a `J1`
state); the memory side's arena the arena's (`hctr` … `h64`). -/
theorem allocW_wcWSH (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -304) (hhi : 8 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isa}
    {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {q : Call} (hq : q.OKB ms L.lab)
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
      WcCtxH ms L.lab R J0 J1 q m) (Spike.Lib.X64.Alloc.N L.lab ms q .rmw) s c → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc (wARH R)
      (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧ WcCtxH ms L.lab R J0 J1 q m) := by
  obtain ⟨hR', hR8'⟩ := Spike.Lib.X64.HelloPh.WcW.wARH_ok hR hR8 hRlo hhi
  have hlo' : (wARH R).lo ≤ -160 := by simp [Spike.Lib.Region.callee]
  have hhi' : 8 ≤ (wARH R).hi := by simp [Spike.Lib.Region.callee]
  have hq' : ∀ m, (F m ∧ CallerCells R (-144) (-160) 8 m ∧ WcCtxH ms L.lab R J0 J1 q m) → q.OKS ms L.lab :=
    fun _ _ => hq.toS
  have hmem' : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, (F m ∧ CallerCells R (-144) (-160) 8 m ∧ WcCtxH ms L.lab R J0 J1 q m) →
        Mem.loadInt m.dmem w 8 = none :=
    fun w hw m hm => hmem w hw m hm.1
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hA : Spike.Lib.X64.Alloc.allocIn L.prog = true := by
    rw [hp]; exact Spike.Lib.X64.Flow.HelloRd.hello_alloc
  have hph := Spike.Lib.X64.HelloPh.WcW.allocPhH (Λ := L.Λ) hΛ hlab
  have hS := Spike.Lib.X64.HelloPh.WcW.allocW_wcGH (rS := rS) (Λ := L.Λ) hp hlo hΛ hlab hsite a hR' hR8' hlo'
    hhi' (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee]) hpool (Or.inr rfl) hra hq'
    hmp hmem' hno
  have hPh := Spike.Lib.X64.HelloWf.allocAbAcH (Cl := Cl) hI hA hph hlab hR' hlo' hhi' hq' (Or.inr rfl) hra
    hmem'
  have hAr := Spike.Lib.X64.AllocG.allocArenaS (lbl := lbl) (p := p) hI hA hR' hlo' hhi' hq' hmem' hctr hheap
    hoff hnew
  have hCx := Spike.Lib.X64.AllocG.allocCtrS (Ctx := fun s c => Ctx s c []) hI hA hR' hlo' hhi' hq'
    (fun a h => hmem' a (.inr h)) hheap hlt h64 hctx
  have hPc := Spike.Lib.X64.AllocG.allocPc (R := wARH R)
    (F := fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧ WcCtxH ms L.lab R J0 J1 q m) (ms := ms) (q := q) hI hph
  have hcf : AllocW ms q (fun _ c => (∀ a, c.term ≠ .ret a) ∧ RunWf p c []) (fun _ _ => False) L.exe L.endPc
      (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧ WcCtxH ms L.lab R J0 J1 q m) := by
    refine Spike.Lib.X64SetupPlaced.allocW_of_ctl fun m0 hF s c _ hc => ?_
    obtain ⟨-, -, mC, σC, c', -, ⟨⟨σe, hJe, -⟩, -⟩, hN, -⟩ := hF
    have hq0 : c' = q.c0 := hN.1
    have h0 := hc1J σe c' hJe
    rw [hq0] at h0
    rcases hc with rfl | ⟨o, rfl⟩
    · exact h0
    · exact cf_hold h0
  have g1 := Spike.Lib.X64.AllocG.AllocW.imp hX0a hcf (fun _ _ => And.intro)
  have g2 := Spike.Lib.X64.AllocG.AllocW.imp hpl g1 (fun _ _ => And.intro)
  have g3 := Spike.Lib.X64.AllocG.AllocW.imp hPc g2 (fun _ _ => And.intro)
  have g4 := Spike.Lib.X64.AllocG.AllocW.imp hCx g3 (fun _ _ => And.intro)
  have g5 := Spike.Lib.X64.AllocG.AllocW.imp hAr g4 (fun _ _ => And.intro)
  have h2 := Spike.Lib.X64.AllocG.AllocW.imp hPh g5 (fun _ _ => And.intro)
  refine Spike.Lib.X64.AllocG.AllocW.imp hS h2 ?_
  rintro s c hst ⟨⟨hab, hac⟩, har, hcx, hpc, hpl', hx, hnr, hr⟩
  exact W0.intro0 hx (Wf.intro (Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt hst fun h => h.elim) hab hac hcl
    (fun _ => hnr) hpl' (fun c' fs' hrun L0 hW hne => .inl (har [] c' fs' hrun L0 hW hne lsize)) hcx hr
    (Spike.Lib.X64.WakeWf.abortWf_of_off (hI.off s hpc).1.noAbort))

/-- **`wc_main` up to the allocator's return inside `WSH`** (`WcPreWH`), moved only by the take:
`wcPreW_wcGH`'s premises (`htp`, `hmr`, `hun`, `hpool`, `hmp`, `hmem`, `hno`), the controls' facts at the
entry (`hc0J`) and at the source advanced (`hc1J`, the allocator's caller), the frames placed per node
(`hpl`), and at every box allocation returning to `.x22` the allocator's `X0` (`hX0a`) and counter context
(`hctx`); the memory side's arena the arena's (`hctr` … `h64`). -/
theorem wcPreW_WSH (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -304) (hhi : 8 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isa}
    {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
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
        WcCtxH ms L.lab R J0 J1 q m) (Spike.Lib.X64.Alloc.N L.lab ms q .rmw) s c → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    WcPreWH (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F ms J0 J1 :=
  ⟨proW_WSH hp hlo hΛ hlab hsite hcl hX0 hR (by omega) (by omega) htp hmr hun hc0J hpl.pro,
    eW_WSH hp hlo hΛ hlab hsite hcl hX0 hR hRlo hhi hc0J hpl.e,
    fun q hq hra => allocW_wcWSH hp hlo hΛ hlab hsite hcl hR hR8 hRlo hhi hpool hq hra hmp (hmem q hq)
      (hno q hq) hc1J (hpl.alloc q hq hra) (hX0a q hq hra) (hctx q hq hra) hctr hheap hoff hnew hlt h64⟩

/-! ## `.x22` -/

/-- **`.x22`'s block and the box's store inside `WSH`**: `wcSp0W_wcGH`'s premise (every cell the allocator
may return `BoxOkH`, `hbox`), the controls' facts at the source advanced (`hc1J`, held at `.x22`), the frames
placed per node (`hpl`), the store's writes' obligation (`hwr`). -/
theorem wcSp0W_WSH (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 8 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (hbox : ∀ (q : AGB ms L.lab) (o : Nat), (∃ σ, J1 σ q.1.c0) → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BoxOkH L.Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)))
    (hc1J : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : WcSp0WH (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F ms J1)
    (hwr : NodeW (NoWrC ar p lbl lsize Ctx []) (fun _ _ => False) L.exe L.endPc R F (sNH ms L.lab R J1 .st)) :
    WcSp0WH (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F ms J1 := by
  have hS := Spike.Lib.X64.HelloPh.WcW.wcSp0W_wcGH (Λ := L.Λ) (rS := rS) hp hlo hΛ hlab hsite a hR hRlo hhi
    hbox
  have hin := Spike.Lib.X64.Flow.HelloWc.hello_wcS0InH
  simp only [Spike.Lib.X64.Flow.HelloWc.wcS0InH, Bool.and_eq_true] at hin
  obtain ⟨h0, h3⟩ := hin
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hb : blockAtB L.prog ".Lwc_main.x22" 15 [(Spike.Lib.X64.stDir .rcx 0 .rax, 3)] = true := by
    rw [hp]; exact h3
  refine ⟨?_, ?_⟩
  · exact blkW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.x22") (k := 0) h0 (ofNat_zero' _)
      Spike.Lib.X64.Flow.HelloWc.wcS0H_ok hR hRlo hhi hS.b (by decide)
      (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (by decide) (by wcfreeBH_dec)
      (fun _ _ ⟨q, ⟨σe, hJe, _⟩, _, o, hc, _⟩ => hc ▸ cf_hold (hc1J σe _ hJe)) hpl.b
  · refine nodeW_WSH hp hlo hΛ hlab hsite hcl hX0 (l := ".Lwc_main.x22") (k := 15) (z := 3) rfl hS.st
      (by wcfreeH_dec) (by decide) (by unfold Spike.Lib.X64.HelloWf.siOffW; decide +kernel) ?_
      (fun _ _ ⟨q, o, ⟨σe, hJe, _⟩, hc, _⟩ => hc ▸ cf_hold (hc1J σe _ hJe)) hpl.st hwr
    rintro s c ⟨h1, h2, h3', h4', σ, hA, hF, hJ⟩
    have hc := Spike.Lib.X64.Rt.cellOf hI hb rfl h1 h2 h4'
    obtain ⟨q, o, hj, hlo', hle, e⟩ := Spike.Lib.X64.HelloPh.WcW.slot_boxH hJ
    have ha' : eaddr s 3 (mB .rcx 0) = σ.slot (-56) :=
      (eaddr_mB s 3 .rcx 0).trans (by rw [hA.regs]; exact Spike.Lib.X64.HelloPh.WcW.bAddr_boxH hJ)
    refine ⟨_, _, hc, fun w w' h => (by cases h),
      exec_store_agrees hc ha' (by rw [e]; exact (hbox q o hj hlo' hle).2.1 _ hF) (agrees_of_decls h3' _ _),
      fun s' hu => ?_⟩
    simp only [TreeLeaf] at hu
    obtain ⟨_, rfl⟩ := hu; rfl

end Gen

/-! ## Inside `NoSetFsW` -/

section NoSetFs

variable {L : RuntimeLayout} {W : Spike.Lib.Frag isa} {K : State → State → Prop} {R : Spike.Lib.Region}
  {F : MachineData → Prop} {ms : Spike.Lib.MemSide isa}

/-- `WcPreWH` in `L`'s layout of helloCells is inside `NoSetFsW`. -/
theorem wcPreW_nsH (hp : L.prog = helloCells) {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (h : WcPreWH W K L.exe L.endPc R F ms J0 J1) :
    WcPreWH (Spike.Lib.X64.NoSetFsW W K) K L.exe L.endPc R F ms J0 J1 := by
  have hpS : Scc.Cert.Rt.X64.Lays L.exe helloCells L.pfx := hp ▸ L.lays
  have hendS : L.endPc = Scc.Cert.Rt.X64.endOf L.exe helloCells L.pfx := by
    show Scc.Cert.Rt.X64.endOf L.exe L.prog L.pfx = _; rw [hp]
  exact Spike.Lib.X64.Flow.HelloWc.WcPreWH.noSetFs hpS hendS h

/-- `WcSp0WH` in `L`'s layout of helloCells is inside `NoSetFsW`. -/
theorem wcSp0W_nsH (hp : L.prog = helloCells) {J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (h : WcSp0WH W K L.exe L.endPc R F ms J1) :
    WcSp0WH (Spike.Lib.X64.NoSetFsW W K) K L.exe L.endPc R F ms J1 := by
  have hpS : Scc.Cert.Rt.X64.Lays L.exe helloCells L.pfx := hp ▸ L.lays
  have hendS : L.endPc = Scc.Cert.Rt.X64.endOf L.exe helloCells L.pfx := by
    show Scc.Cert.Rt.X64.endOf L.exe L.prog L.pfx = _; rw [hp]
  exact Spike.Lib.X64.Flow.HelloWc.WcSp0WH.noSetFs hpS hendS h

end NoSetFs

end Spike.Lib.X64.HelloPh.WcWfS

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.WcWfS.blkW_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfS.blkW_WSH

/-- info: 'Spike.Lib.X64.HelloPh.WcWfS.nodeW_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfS.nodeW_WSH

/-- info: 'Spike.Lib.X64.HelloPh.WcWfS.proW_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfS.proW_WSH

/-- info: 'Spike.Lib.X64.HelloPh.WcWfS.eW_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfS.eW_WSH

/--
info: 'Spike.Lib.X64.HelloPh.WcWfS.allocW_wcWSH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfS.allocW_wcWSH

/-- info: 'Spike.Lib.X64.HelloPh.WcWfS.wcPreW_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfS.wcPreW_WSH

/-- info: 'Spike.Lib.X64.HelloPh.WcWfS.wcSp0W_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfS.wcSp0W_WSH

/-- info: 'Spike.Lib.X64.HelloPh.WcWfS.wcPreW_nsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfS.wcPreW_nsH

/-- info: 'Spike.Lib.X64.HelloPh.WcWfS.wcSp0W_nsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfS.wcSp0W_nsH
