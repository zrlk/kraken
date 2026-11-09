/-
**hello.w's `wc_rodata` up to the allocator's return inside the start's level at `ownGHXW`** (x86-64; the twin of
`Spike/Lib/A64HelloRdWfSF.lean`, at `ownGHXW`): `HelloRd.RdPreW` at `AllocWSF.WSHFg (ownGHXW L a) … fs` (`fs` one
of `[]` and `[frM]`, `hfs`), moved only by the take (`PhRec.K L rS`). rodata runs under the setup block's frame
`HelloRdCf.frH env`, so its states are at `[frH env]` (`fs := [frH env]`, `frM := frH env`). Each node is
`WcWfX.blkW_wfCX`/`nodeW_wfCX` at its `SFactsSt2` at `ownGHXW` from `OwnRd.proW_rdGHX` / `eW_rdGHX`; the allocator
is `HelloWf.allocW_WSHFg` at `OwnAlloc.allocW_wcGHX`. The frames are on the pool: `hb : BandOnP L R (-208) 8`
(`wc_rodata`'s and the allocator's region `aR R`'s, `OwnRd.bandOnP_aR`).

- `blkW_rdWSHFg`, `nodeW_rdWSHFg`: a block, a single instruction of `wc_rodata` inside `WSHFg own` at any `own`.
- `proW_rdWSHX`, `eW_rdWSHX`, `allocW_rdWSHX`, `rdPreW_WSHX`: `wc_rodata` up to the allocator's return at
  `ownGHXW`.

## Differences from the AArch64 version

- AArch64's level is at `ownGH` (main owns no TCB word there); here it is `WSHFg (ownGHXW L a)`, and the producers
  take `ownGHXW`'s separation premises (`hsep`, `ha`, `hW`) and the band `hb`; the allocator's counter and headers
  are also off `tcbM` (`hnoM`).
- The prologue is x86-64's five nodes (`XProW`: `xHead` at `wc_rodata`, the check's `xLea`, the limit's `%fs`
  load, `xCmp`, `xFr` at `.Lwc_rodata.chk`'s byte offsets 0, 5, 14, 19; AArch64's four-node `ProW` at
  `.L19_wc_rodata.stack_check`), so `proW_rdWSHX` has five cases and its load is a `movq %fs:8, %r11` (AArch64:
  `ldr`).
- Offsets are bytes and cells sized: a block's free pcs are `freeBlkH l k blk` (AArch64's
  `freeAtH l k blk.length`), a node's `freeAtH l [k]`, its fact `PhFact.step l k z` and its phase check
  `siOffW pfxM l k z`; the phase checks are `HelloWf.phOffW` / `siOffW` (AArch64's `phOffHC` / `siOffHC`).
- No 16-alignment (`hal`); the allocator's region `aR R` needs the caller's base 8-aligned (`hR8`,
  `WcW.aRH_ok`) and `8 ≤ R.hi` (the return address pushed by `call`); the allocator returns to
  `.Lwc_rodata.x0` (AArch64's `.L19_wc_rodata.sp0`); the caller's cells are `CallerCells R (-48) (-160) 8`.
-/
import Spike.Lib.X64HelloRdPreWI
import Spike.Lib.X64HelloAllocWSF
import Spike.Lib.X64HelloWcWf
import Spike.Lib.X64SetupPlaced
import Spike.Lib.X64HelloRdPreWIX
import Spike.Lib.X64HelloWcWfX

namespace Spike.Lib.X64.HelloPh.RdWfSFX

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
open Spike.Lib.X64 (ND BlkW NodeW At cellOff okBlk arun fsDir agrees_of_decls)
open Spike.Lib.X64.Flow (XProW xProN2 xHead xLea xCmp xFr xHead_ok xLea_ok xCmp_ok xFr_ok xS1 xS2 hdRegs
  prologueIn ofNat_add' ofNat_zero')
open Spike.Lib.X64.Rt.MainU (xHead_noRet xLea_noRet xCmp_noRet xFr_noRet)
open Spike.Lib.X64.WakeWf (RunWf NoWrC)
open Spike.Lib.X64.HelloPh (lo ownGHXW ownH instOkH)
open Spike.Lib.X64.HelloPh.WcW (freeNH freeAtH freeBlkH freeAt_pcH freeBlk_pcH rdTabH rdW_factH)
open Spike.Lib.X64.HelloWf (WSHFg)
open Spike.Lib.X64.HelloPh.StartWf (pfxM)
open Spike.Lib.X64.Flow.HelloRd (rN RdPreW RdCtx hello_rdPro hello_rdEIn rdEIn rdPro)
open Spike.Lib.X64.Flow.Hello1 (rdE rdE_ok aR)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Alloc (Call AllocW)
open Spike.Lib.X64.WakePh (tcbM BandOnP)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (CellAt fsAddr eaddr exec_movfs_load_agrees)

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {own : Spike.Lib.X64Consumer.Own} {rS : Range} {R : Spike.Lib.Region}
  {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {K : State → State → Prop} {fs : List TermRun.Frame}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s) (hfs : fs = [] ∨ fs = [frM])

include hp hlo hΛ hlab hsite hcl hX0 hfs

/-! ## A block and a node inside `WSHX` -/

/-- **A covered `ret`-free block of `wc_rodata` inside `WSHX`** (`WcWfX.blkW_wfCX` at `rdTabH`): its
`SFactsSt2` at `ownGH` (`hst`), its phase fact in `rdTabH` (`hf`), its abort phases' check (`hph`), its pcs
free (`hfree`), its controls' facts (`hJ`), its frames placed (`hpl`). -/
theorem blkW_rdWSHFg {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n blk)
    (hf : PhFact.blk l k blk none none ∈ rdTabH) (hph : Spike.Lib.X64.HelloWf.phOffW pfxM l k l blk = true)
    (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true) (hfree : freeBlkH l k blk = true)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (WSHFg own L ar p Dt Cl Ctx lbl lsize frM X0 fs) K L.exe L.endPc R F n blk := by
  have hph' := Spike.Lib.X64.Rt.PhOfTab.blkPh_of_factOk hlab (rapc := 0) (dset := fun _ => false)
    (fun _ _ h => by cases h) (fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h) (rdW_factH hΛ hf)
  have hokpc : ∀ j < blk.length,
      okPcOf lo helloCells L.Λ (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true := fun j hj => by
    have := List.all_eq_true.mp hph' j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true] at this
    rw [← he]; exact this.1.1
  refine Spike.Lib.X64.WakeWf.blkW_w0 hfs ?_
    (Spike.Lib.X64.HelloPh.WcWfX.blkW_wfCX (Dt := Dt) (ar := ar) (Cl := Cl) (Ctx := Ctx) (lsize := lsize)
      hp hlo hlab hsite hb he hok hR hlo' hhi hst hokpc hph hnr hcl hJ hpl)
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  refine ⟨hX0 _ ?_, fun _ h => h⟩
  show freeNH (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true
  rw [← he]; exact freeBlk_pcH hlab hfree hj

/-- **A single instruction of `wc_rodata` without an event inside `WSHX`** (`WcWfX.nodeW_wfCX` at
`rdTabH`). -/
theorem nodeW_rdWSHFg {n : ND} {l : Label} {k z : Nat} (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (hfree : freeAtH l [k] = true) (hf : PhFact.step l k z ∈ rdTabH)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s' : State, TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n)
    (hwr : NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (WSHFg own L ar p Dt Cl Ctx lbl lsize frM X0 fs) K L.exe L.endPc R F n := by
  have hf0 : freeNH n.pc.toBitVec.toNat = true := by
    rw [← he]; exact freeAt_pcH hlab hfree (List.mem_singleton.mpr rfl)
  have hok := (Spike.Lib.X64.Rt.PhOfTab.step_of_factOk hlab (rdW_factH hΛ hf)).1
  rw [he] at hok
  refine Spike.Lib.X64.WakeWf.nodeW_w0 hfs ?_
    (Spike.Lib.X64.HelloPh.WcWfX.nodeW_wfCX (Dt := Dt) (Cl := Cl) hp hlo hlab he hst
      (Spike.Lib.X64.HelloPh.WcWf.htk_of_freeNH hlab hsite hf0) hok hph hstep hcl hJ hpl hwr)
  rintro s c ⟨_, _, _, hpc, _⟩
  exact ⟨hX0 _ (by unfold pcOf; rw [hpc]; exact hf0), fun _ h => h⟩

/-! ## Up to the allocator's return -/

set_option maxHeartbeats 1600000 in
/-- **`wc_rodata`'s prologue inside `WSHX`** (`proW_rdGHX`'s premises: the thread pointer `tp` at every entry
state, `htp`; its limit word mapped and unmapped, `hmr`, `hun`), its controls' facts at the entry (`hc0J`), its
frames placed (`hpl`). -/
theorem proW_rdWSHX
    (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hb : BandOnP L R (-208) 8)
    (hR : R.OK) (hRlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none)
    (hc0J : ∀ σ c, J0 σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : XProW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F ms
      (L.lab "wc_rodata") 32 8 ".Lwc_rodata.stk" 5 9 3 2 4 [] J0) :
    XProW (WSHFg (ownGHXW L a) L ar p Dt Cl Ctx lbl lsize frM X0 fs) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F ms
      (L.lab "wc_rodata") 32 8 ".Lwc_rodata.stk" 5 9 3 2 4 [] J0 := by
  have hS := Spike.Lib.X64.HelloPh.OwnRd.proW_rdGHX (Λ := L.Λ) (rS := rS) (ms := ms) hp hlo hΛ hlab hsite hsep
    ha hW hb hR hRlo hhi htp hmr hun
  have h := hello_rdPro
  simp only [rdPro, prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩ := h
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have esc : L.lab ".Lwc_rodata.chk" = L.lab "wc_rodata" + Int64.ofNat 4 :=
    label_labelGapB L.lays (by rw [hp]; exact hgap)
  have h4 : L.lab "wc_rodata" + 1 + 3 = L.lab ".Lwc_rodata.chk" := by rw [esc, Int64.add_assoc]; rfl
  have e14 : L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 =
      L.lab ".Lwc_rodata.chk" + Int64.ofNat 14 := by
    rw [h4, ← ofNat_add']
  have e19 : L.lab "wc_rodata" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2 =
      L.lab ".Lwc_rodata.chk" + Int64.ofNat 19 := by
    rw [e14, ← ofNat_add', ← ofNat_add']
  have hxs : (xS2 32 · |>.regs.fsBase) = fun σ : Spike.Lib.X64.AS => σ.regs.fsBase := by
    funext σ; simp [xS2, xS1, hdRegs, Reg64s.set64]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_rdWSHFg hp hlo hΛ hlab hsite hcl hX0 hfs (l := "wc_rodata") (k := 0) bHd (ofNat_zero' _)
      (xHead_ok (lo := -40) (hi := 0) (by decide) (Int.le_refl _)) hR hRlo hhi hS.w0 (by decide)
      (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) xHead_noRet (by wcfreeBH_dec) hc0J hpl.w0
  · exact blkW_rdWSHFg hp hlo hΛ hlab hsite hcl hX0 hfs (l := ".Lwc_rodata.chk") (k := 0) bLea
      (by show _ = L.lab "wc_rodata" + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -40) (hi := 0) _ _) hR hRlo hhi hS.w1 (by decide)
      (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (xLea_noRet _ _) (by wcfreeBH_dec)
      (fun _ _ ⟨σ0, hJ0, _⟩ => hc0J σ0 _ hJ0) hpl.w1
  · have hbL : blockAtB L.prog ".Lwc_rodata.chk" 5 [(fsDir .r11 8, 9)] = true := by rw [hp]; exact bLd
    have key : ∀ s c, At L.exe L.endPc R F (xProN2 (L.lab "wc_rodata") 5 32 J0) s c →
        CellAt s (fsDir .r11 8) 9 ∧
        fsAddr s 9 { base := none, idx := none, disp := .int64 8 } = Spike.Lib.X64.Flow.Ret0.limA tp ∧
        Mem.loadInt s.st.1.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none ∧ s.decls = {} := by
      rintro s c ⟨h1, h2, h3', h4', σ2, hA, hF, σ0, hJ0, rfl⟩
      refine ⟨Spike.Lib.X64.Rt.cellOf hI hbL rfl h1 h2
        (by rw [h4']; show L.lab "wc_rodata" + 1 + 3 + _ = _; rw [h4]), ?_, hun _ hF, h3'⟩
      rw [show Spike.Lib.X64.Flow.Ret0.limA tp = (xS2 32 σ0).regs.fsBase.toBitVec + (8 : Int64).toBitVec by
        rw [congrFun hxs σ0, htp _ _ hJ0]; rfl]
      simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
    refine nodeW_rdWSHFg hp hlo hΛ hlab hsite hcl hX0 hfs (l := ".Lwc_rodata.chk") (k := 5) (z := 9)
      (by show _ = L.lab "wc_rodata" + 1 + 3 + _; rw [h4]) hS.w2 (by wcfreeH_dec) (by decide)
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
  · exact blkW_rdWSHFg hp hlo hΛ hlab hsite hcl hX0 hfs (l := ".Lwc_rodata.chk") (k := 14) bCmp
      (by show _ = L.lab "wc_rodata" + 1 + 3 + _ + _; rw [e14])
      (xCmp_ok (lo := -40) (hi := 0) _ _ _ _) hR hRlo hhi hS.w3 (by decide)
      (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (xCmp_noRet _ _ _) (by wcfreeBH_dec)
      (fun _ _ ⟨σ0, _, hJ0, _⟩ => hc0J σ0 _ hJ0) hpl.w3
  · exact blkW_rdWSHFg hp hlo hΛ hlab hsite hcl hX0 hfs (l := ".Lwc_rodata.chk") (k := 19) bFr
      (by show _ = L.lab "wc_rodata" + 1 + 3 + _ + _ + _ + _; rw [e19])
      (xFr_ok (lo := -40) (hi := 0) _ _ _ (by decide)) hR hRlo hhi hS.w4 (by decide)
      (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (xFr_noRet _ _ _) (by wcfreeBH_dec)
      (fun _ _ ⟨σ0, _, hJ0, _⟩ => hc0J σ0 _ hJ0) hpl.w4

/-- **`wc_rodata`'s entry block inside `WSHX`.** -/
theorem eW_rdWSHX
    (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hb : BandOnP L R (-208) 8)
    (hR : R.OK) (hRlo : R.lo ≤ -208) (hhi : 8 ≤ R.hi)
    {J0 J1 : Spike.Lib.X64.AS → Ctl → Prop}
    (hc0J : ∀ σ c, J0 σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F
      (rN L.lab R J0 J1 .e) rdE) :
    BlkW (WSHFg (ownGHXW L a) L ar p Dt Cl Ctx lbl lsize frM X0 fs) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F
      (rN L.lab R J0 J1 .e) rdE :=
  blkW_rdWSHFg hp hlo hΛ hlab hsite hcl hX0 hfs (l := ".Lwc_rodata.entry") (k := 0)
    (by have := hello_rdEIn; simp only [rdEIn, Bool.and_eq_true] at this; exact this.1)
    (ofNat_zero' _) rdE_ok hR hRlo hhi
    (Spike.Lib.X64.HelloPh.OwnRd.eW_rdGHX hp hlo hΛ hlab hsite hsep ha hW hb hR hRlo hhi) (by decide)
    (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (by decide) (by wcfreeBH_dec)
    (fun _ _ ⟨⟨σe, hJe, _⟩, _⟩ => hc0J σe _ hJe) hpl

omit hX0 in
/-- **The allocator inside `WSHX`** at `wc_rodata`'s call (`HelloWf.allocW_WSHFg` at `OwnAlloc.allocW_wcGHX`, the
allocator's region
`aR R`, return label `.Lwc_rodata.x0`), its controls' facts from the call context's (`hc1J`, through `RdCtx`:
the allocator's `c0` that of a `J1` state). -/
theorem allocW_rdWSHX
    (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hb : BandOnP L R (-208) 8)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -208) (hhi : 8 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isa}
    {J0 J1 : Spike.Lib.X64.AS → Ctl → Prop} {q : Call} (hq : q.OK ms L.lab)
    (hra : q.ra = (L.lab ".Lwc_rodata.x0").toBitVec)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j)
    (hnoM : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      w ≠ tcbM L)
    (hc1J : ∀ σ c, J1 σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : AllocW ms q (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc (aR R)
      (fun m => F m ∧ CallerCells R (-48) (-160) 8 m ∧ RdCtx ms L.lab R J0 J1 q m))
    (hX0a : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (aR R)
      (fun m => F m ∧ CallerCells R (-48) (-160) 8 m ∧ RdCtx ms L.lab R J0 J1 q m))
    (hctx : ∀ s c, At L.exe L.endPc (aR R) (fun m => F m ∧ CallerCells R (-48) (-160) 8 m ∧
      RdCtx ms L.lab R J0 J1 q m) (Spike.Lib.X64.Alloc.N L.lab ms q .rmw) s c → Ctx s c fs)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (WSHFg (ownGHXW L a) L ar p Dt Cl Ctx lbl lsize frM X0 fs) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc
      (aR R) (fun m => F m ∧ CallerCells R (-48) (-160) 8 m ∧ RdCtx ms L.lab R J0 J1 q m) := by
  obtain ⟨hR', hR8'⟩ := Spike.Lib.X64.HelloPh.WcW.aRH_ok hR hR8 hRlo hhi
  have hS : AllocW ms q (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s)
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc (aR R)
      (fun m => F m ∧ CallerCells R (-48) (-160) 8 m ∧ RdCtx ms L.lab R J0 J1 q m) :=
    Spike.Lib.X64.HelloPh.OwnAlloc.allocW_wcGHX (rS := rS) hp hlab hsite hsep ha hW
    (Spike.Lib.X64.HelloPh.OwnRd.bandOnP_aR hb) hlo hΛ hR' hR8'
    (by simp [aR, Spike.Lib.Region.callee]) (by simp [aR, Spike.Lib.Region.callee])
    (by simp [aR, Spike.Lib.Region.callee]) (by simp [aR, Spike.Lib.Region.callee]) hpool (Or.inl rfl) hra
    (fun _ _ => hq.toS) hmp (fun w hw m hm => hmem w hw m hm.1) hno hnoM
  refine Spike.Lib.X64.HelloWf.allocW_WSHFg hp hlo hΛ hlab hsite hR' (by simp [aR, Spike.Lib.Region.callee])
    (by simp [aR, Spike.Lib.Region.callee]) hfs (Or.inl rfl) hra (fun _ _ => hq.toS)
    (fun w hw m hm => hmem w hw m hm.1) hS hcl hpl hX0a ?_ hctx hctr hheap hoff hnew hlt h64
  refine Spike.Lib.X64SetupPlaced.allocW_of_ctl fun m0 hF s c _ hc => ?_
  obtain ⟨-, -, mC, σC, c', -, ⟨⟨σe, hJe, -⟩, -⟩, hN, -⟩ := hF
  have hq0 : c' = q.c0 := hN.1
  have h0 := hc1J σe c' hJe
  rw [hq0] at h0
  rcases hc with rfl | ⟨o, rfl⟩
  · exact h0
  · exact ⟨h0.1, Spike.Lib.X64.WakePh.WcWf.RunWf.hold h0.2⟩

/-- **`wc_rodata` up to the allocator's return inside `WSHX`** (`RdPreW`), moved only by the take:
`rdPreW_wcGHX`'s premises (`htp`, `hmr`, `hun`, `hpool`, `hmp`, `hmem`, `hno`), the controls' facts at the
entry (`hc0J`) and at the source advanced (`hc1J`, the allocator's caller), the frames placed per node (`hpl`),
and at every buffer allocation returning to `.x15` the allocator's `X0` (`hX0a`) and counter context (`hctx`);
the memory side's arena the arena's (`hctr` … `h64`). -/
theorem rdPreW_WSHX
    (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hb : BandOnP L R (-208) 8)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -208) (hhi : 8 ≤ R.hi)
    (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64) {ms : Spike.Lib.MemSide isa}
    {J0 J1 : Spike.Lib.X64.AS → Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J0 σ c → σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ q : Call, q.OK ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem w 8 = none)
    (hno : ∀ q : Call, q.OK ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ ownH L a j)
    (hnoM : ∀ q : Call, q.OK ms L.lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      w ≠ tcbM L)
    (hc0J : ∀ σ c, J0 σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hc1J : ∀ σ c, J1 σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : RdPreW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F ms J0 J1)
    (hX0a : ∀ q : Call, q.OK ms L.lab → q.ra = (L.lab ".Lwc_rodata.x0").toBitVec →
      AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc (aR R)
        (fun m => F m ∧ CallerCells R (-48) (-160) 8 m ∧ RdCtx ms L.lab R J0 J1 q m))
    (hctx : ∀ q : Call, q.OK ms L.lab → q.ra = (L.lab ".Lwc_rodata.x0").toBitVec →
      ∀ s c, At L.exe L.endPc (aR R) (fun m => F m ∧ CallerCells R (-48) (-160) 8 m ∧
        RdCtx ms L.lab R J0 J1 q m) (Spike.Lib.X64.Alloc.N L.lab ms q .rmw) s c → Ctx s c fs)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    RdPreW (WSHFg (ownGHXW L a) L ar p Dt Cl Ctx lbl lsize frM X0 fs) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F
      ms J0 J1 :=
  ⟨proW_rdWSHX hp hlo hΛ hlab hsite hcl hX0 hfs hsep ha hW hb hR (by omega) (by omega) htp hmr hun hc0J hpl.pro,
    eW_rdWSHX hp hlo hΛ hlab hsite hcl hX0 hfs hsep ha hW hb hR hRlo hhi hc0J hpl.e,
    fun q hq hra => allocW_rdWSHX hp hlo hΛ hlab hsite hcl hfs hsep ha hW hb hR hR8 hRlo hhi hpool hq hra hmp
      (hmem q hq)
      (hno q hq) (hnoM q hq) hc1J (hpl.alloc q hq hra) (hX0a q hq hra) (hctx q hq hra) hctr hheap hoff hnew hlt h64⟩

end Gen

end Spike.Lib.X64.HelloPh.RdWfSFX

/-! ## Axioms -/

/--
info: 'Spike.Lib.X64.HelloPh.RdWfSFX.blkW_rdWSHFg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdWfSFX.blkW_rdWSHFg

/--
info: 'Spike.Lib.X64.HelloPh.RdWfSFX.nodeW_rdWSHFg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdWfSFX.nodeW_rdWSHFg

/--
info: 'Spike.Lib.X64.HelloPh.RdWfSFX.proW_rdWSHX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdWfSFX.proW_rdWSHX

/--
info: 'Spike.Lib.X64.HelloPh.RdWfSFX.eW_rdWSHX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdWfSFX.eW_rdWSHX

/--
info: 'Spike.Lib.X64.HelloPh.RdWfSFX.allocW_rdWSHX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdWfSFX.allocW_rdWSHX

/--
info: 'Spike.Lib.X64.HelloPh.RdWfSFX.rdPreW_WSHX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdWfSFX.rdPreW_WSHX
