/-
**hello.w's `wc_main` up to the box's allocator's return, the heap abort keeping the spills** (x86-64; the twin
of `Spike/Lib/A64HelloWcPreA.lean`'s live part): `HelloWc.hello_wc_pre_segW` with its heap-abort exit
strengthened to `wXA`: `wXH .abort`'s invariant and, for the call's entry witness `σe`, `wc_main`'s spilled
argument words at the abort's abstract state (`σ.slot (-16) … σ.slot (-48) = σe.rdi, rsi, rdx, rcx, r8`). The
allocator's call context keeps `wc_main`'s frame outside the allocator's region (`CKept R (-144) (-160) 8`), so
the slots are the call node's (`wcJH`), as at `.x22`.

- `wXA`, `wXHA`: the strengthened abort node; the exits with it.
- `hello_wc_pre_segWA`: the segment with the exits `wXHA`.
- `at_wXA_of_tpXa`, `hello_wc_entry_segWA`, `hello_wc_entry_segJrA`: `wc_main`'s entry to its heap abort at
  `wXA`, the box's landing (with `TP t`) the `xa` exit; at `scc_rt_main`'s call after `wc_rodata`.

## Differences from the AArch64 version

- The spills are at the region's `-16 … -48` (below the saved `%rbp`; AArch64: `-144 … -112`), the abort's
  return address the pushed `.Lscc_rt_alloc.full + 12` at `-304` (AArch64: `x30 = .L2_scc_rt_alloc.4_full + 8`).
- `wXHA` takes the region `R` (as `wXH` does: `.x18` records `%rbp = R.addr (-8)`).
- `R.hi` is at least `8` (the return address cell above the region's base; AArch64: `0`); there is no
  alignment premise.
- The box's landing (`hxa`) is on the frame based at the saved `%rbp`, `R.fp (-8)` (as `hello_wc_sp0_segW`).
- The thread pointer is `fsBase`, the segment inside `NoSetFsW (tpG t W) K` (AArch64: `TPIDR_EL0`, `NoMsrW`);
  the limit word is at `fsBase + 8` and bounded by `%rsp - 8 - 128` (`lim_wcJ0`: `wc_rodata`'s `%rsp - 8 - 8 - 128`).
- `at_wXA_wXH` is not twinned: it is dead in hello.
-/
import Spike.Lib.X64HelloWcEntry

namespace Spike.Lib.X64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells LimOk)
open Spike.Lib.X64.Alloc (Call AllocW Jfull)
open Spike.Lib.X64.Flow.WakeWc (AGB BoxW WN WX call_nd_FWKL okb_tpXa okb_of_tpXa)
open Spike.Lib.X64.Flow.HelloRd (hello_alloc)
open Spike.Lib.X64.Flow.HelloM (wcJ0 wcR wcF)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.WakeTP (tpG tp_of_at)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-- **The allocator's heap abort with `wc_main`'s spills** (`wXH .abort` and the call's entry witness's argument
words at the spill slots). -/
def wXA (ms : MemSide isa) (lab : Label → Int64) (J1 : AS → Ctl → Prop) : ND :=
  ⟨lab "scc_rt_abort", ⟨-304, []⟩, fun σ c => σ.regs.rdi.toBitVec = 2#64 ∧
    σ.slot (-304) = (lab ".Lscc_rt_alloc.full" + 12).toBitVec ∧ ∃ q : AGB ms lab, Jfull ms q.1 c ∧
    ∃ σe, J1 σe q.1.c0 ∧ σ.slot (-16) = σe.regs.rdi.toBitVec ∧ σ.slot (-24) = σe.regs.rsi.toBitVec ∧
      σ.slot (-32) = σe.regs.rdx.toBitVec ∧ σ.slot (-40) = σe.regs.rcx.toBitVec ∧
      σ.slot (-48) = σe.regs.r8.toBitVec⟩

/-- **The exits with the abort at `wXA`**. -/
def wXHA (ms : MemSide isa) (lab : Label → Int64) (R : Region) (J1 : AS → Ctl → Prop) : WX → ND
  | .x18 => wXH ms lab R J1 .x18
  | .abort => wXA ms lab J1

section WcFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`hello_wc_pre_segW` with the heap abort at `wXA`** (the spilled words recorded): the same segment, its
abort exit's abstract state keeping `wc_main`'s spill slots `-16 … -48` (the allocator's call context keeps
`wc_main`'s frame outside its region, `CKept R (-144) (-160) 8`; the slots are the call node's `wcJH`). -/
theorem hello_wc_pre_segWA {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -304) (hhi : 8 ≤ R.hi)
    {J0 J1 : AS → Ctl → Prop} (hW : WcPreWH W K exe endPc R F ms J0 J1)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (128 : Int64).toBitVec))
    (hloc : ∀ σ c, J0 σ c → ∃ c', LocalRun p c c' ∧ J1 σ c')
    (hq : ∀ σ c, J1 σ c → ∃ q : Call, q.OKB ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 256#64 ∧ q.k = 1#64 ∧ q.u ms = 2#64)
    (hmem : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (wXHA ms (_root_.Executable.labels exe).label R J1 y) s c) := by
  have hin := hello_wcEInH
  simp only [wcEInH, Bool.and_eq_true] at hin
  obtain ⟨h0, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e26 : lab ".Lwc_main.x0" = lab ".Lwc_main.entry" + Int64.ofNat 26 := label_labelGapB hp hgap
  refine SegW.seq (prologue_seg_ofW hp hend hello_wcPro (nb := ⟨lab ".Lwc_main.entry", oWRH, wcJH J0⟩)
    (by decide) hF hR
    (by show R.lo ≤ -8 - (128 : Int64).toInt; rw [show (128 : Int64).toInt = 128 from rfl]; omega) (by omega)
    (by decide) rfl (by show SO.le oWRH (oF 128) = true; decide) hW.pro ?_)
    ((fn_segW (N := wNH lab R J0 J1) (E := wXHA ms lab R J1) (fun i => ?_) WN.e).mono_pre
      fun _ _ h => Hello1.At.reg_addr (r := .rbp) (k := -8) rfl h)
  · intro σ c hJ
    have hl := hlim σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs =>
      ⟨σ, hJ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
    · rw [hs]; simp [xStSlots, xS1, upd_apply]
    · rw [hs]; simp [xStSlots, xS1, upd_apply]
    all_goals rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64]
  cases i
  case e =>
    refine seg_ndW (by simp [wcEH]) wcEH_ok hF hR hlo hhi (code_field hp hend h0 (ofNat_zero' _)) hW.e
      fun σ c hJ => ?_
    simp only [wNH] at hJ
    obtain ⟨⟨σe, hJe, h0', h8, h16, h24, h32, h40, h48⟩, hb⟩ := hJ
    obtain ⟨c', hr, hJ1⟩ := hloc σe c hJe
    refine ⟨c', hr, .inl ⟨WN.call, ?_, ?_, ?_⟩⟩
    · simp only [wNH]; rw [wcEH_run]
    · simp only [wNH]; rw [wcEH_run]; rfl
    · simp only [wNH]
      rw [wcEH_run]
      refine ⟨⟨σe, hJ1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [upd_apply]; exact h0'
      · simp only [upd_apply]; exact h8
      · simp only [upd_apply]; exact h16
      · simp only [upd_apply]; exact h24
      · simp only [upd_apply]; exact h32
      · simp only [upd_apply]; exact h40
      · simp only [upd_apply]; exact h48
      · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; exact hb
      · simp [Reg64s.set64]
      · simp [Reg64s.set64]
      · simp [Reg64s.set64]
      · rw [e26]
        simp only [upd_apply, ↓reduceIte, Int64.toBitVec_add]
        rfl
  case call =>
    refine call_nd_FWKL (KC := False) (e0 := 0) (lo' := -160) (hi' := 8) (M := fun _ => True)
      (Ne := fun g : AGB ms lab => Alloc.N lab ms g.1 .e) (Ex := fun g : AGB ms lab => Alloc.EB lab ms g.1)
      hR hF (by show R.lo ≤ -144 - 0 + -160; omega) (by decide) (by show (-144 : Int) - 0 < R.hi; omega)
      (by show (-144 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-144 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide) (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, -, -, -, h80⟩, ⟨-, -, hra, -⟩⟩ := hg
        have hr : g.1.ra = (lab ".Lwc_main.x0").toBitVec := by
          rw [← hra, ← h80]; rfl
        exact (Alloc.seg_allocBW hp hend hello_alloc hF' hR' hlo' hhi' g.2
          (fun a ha m hm => hmem g.1 g.2 a ha m (hFF m hm))
          (Hello1.allocW_mono (hW.alloc g.1 g.2 hr) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩)).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨σe, hJe, -, -, -, -, -, -, -⟩, -, h0, h1, h2, -⟩
      obtain ⟨q, hok, hc, hh, hk, hu⟩ := hq σe c hJe
      exact ⟨⟨{ q with fp := σC.regs.rbp.toBitVec, ra := σC.slot (-144 - 0 + 0) },
        ⟨{ hok.toS with }, hok.newOk, hok.term, hok.ev, hok.one⟩⟩, rfl,
        hc.symm, rfl, rfl, h0.trans hh.symm, h1.trans hk.symm, h2.trans hu.symm⟩
    · rintro g y σC c σx c' σR ⟨⟨σe, hJe, h0', h8, h16, h24, h32, h40, h48⟩, hb, -, -, -, h80⟩ ⟨hc, hfp, hra, -⟩
        hx hreg - - hsl hin
      have hk : ∀ k : Int, -48 ≤ k → k ≤ 0 → k % 8 = 0 → σR.slot k = σC.slot k := fun k hk1 hk2 hk3 =>
        hsl k ⟨by omega, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wNH]; omega)
      cases y
      · refine .inr ⟨WX.x18, ?_, by show SO.le ⟨-136, []⟩ ⟨-144 - 0 + 8, []⟩ = true; decide, g,
          ⟨σe, hc ▸ hJe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
        · show lab ".Lwc_main.x0" = Int64.ofBitVec g.1.ra
          rw [← hra]
          show _ = Int64.ofBitVec (σC.slot (-144 - 0 + 0))
          rw [show (-144 : Int) - 0 + 0 = -144 by decide, h80, int64_ofBitVec_toBitVec]
        · rw [hk 0 (by decide) (by decide) (by decide), h0']
        · rw [hk (-8) (by decide) (by decide) (by decide), h8]
        · rw [hk (-16) (by decide) (by decide) (by decide), h16]
        · rw [hk (-24) (by decide) (by decide) (by decide), h24]
        · rw [hk (-32) (by decide) (by decide) (by decide), h32]
        · rw [hk (-40) (by decide) (by decide) (by decide), h40]
        · rw [hk (-48) (by decide) (by decide) (by decide), h48]
        · simp only [Alloc.EB] at hx
          obtain ⟨-, -, -, -, -, hbx⟩ := hx
          rw [← hb]
          simp only [Reg64s.get64]
          rw [hreg, hbx, ← hfp]; rfl
        · simp only [Alloc.EB] at hx ⊢
          rw [hreg]; exact hx
      · obtain ⟨h2, hfull, hs⟩ := hx
        refine .inr ⟨WX.abort, rfl, by show SO.le ⟨-304, []⟩ ⟨-144 - 0 + -160, []⟩ = true; decide, ?_, ?_,
          g, hfull, σe, hc ▸ hJe, ?_, ?_, ?_, ?_, ?_⟩
        · show σR.regs.rdi.toBitVec = 2#64
          rw [hreg]; exact h2
        · show σR.slot (-304) = _
          rw [hin (-304) (by simp only [Region.Off, Region.callee, wNH]; omega)]
          exact hs
        · rw [hk (-16) (by decide) (by decide) (by decide), h16]
        · rw [hk (-24) (by decide) (by decide) (by decide), h24]
        · rw [hk (-32) (by decide) (by decide) (by decide), h32]
        · rw [hk (-40) (by decide) (by decide) (by decide), h40]
        · rw [hk (-48) (by decide) (by decide) (by decide), h48]

end WcFn

/-- **`wXA` at `tpXa` is at `ms`**. -/
theorem at_wXA_of_tpXa {ms : MemSide isa} {t : UInt64} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {J1 : AS → Ctl → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F (wXA (tpXa ms t) (_root_.Executable.labels exe).label J1) s c) :
    At exe endPc R F (wXA ms (_root_.Executable.labels exe).label J1) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, h0, hs, q, hq, hJ⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, h0, hs, ⟨q.1, okb_of_tpXa q.2⟩, hq, hJ⟩

section Entry

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from its entry is one segment inside `W`, the thread pointer kept, the heap abort at `wXA`**, in
any valid layout of `helloCells`: `hello_wc_pre_segWA`, then `hello_wc_sp0_segW` at its allocator's return, both
at `tpXa ms t` inside `NoSetFsW (tpG t W) K`, the thread pointer `t` at the entry (`hJ0tp`;
`KeepTP.SegW.keepTP'`). The box's landing `bXH l A` on `R.fp (-8)` with `TP t` is the `xa` exit (`hxa`). -/
theorem hello_wc_entry_segWA {t : UInt64} (hK : ms.K = some Scc.Sem.X64.abi)
    {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -304) (hhi : 8 ≤ R.hi)
    {J0 J1 : AS → Ctl → Prop} (hJ0tp : ∀ σ c, J0 σ c → σ.regs.fsBase = t)
    (hWp : WcPreWH (NoSetFsW (tpG t W) K) K exe endPc R F (tpXa ms t) J0 J1)
    (hWs : WcSp0WH (NoSetFsW (tpG t W) K) K exe endPc R F (tpXa ms t) J1)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (128 : Int64).toBitVec))
    (hloc : ∀ σ c, J0 σ c → ∃ c', LocalRun p c c' ∧ J1 σ c')
    (hq : ∀ σ c, J1 σ c → ∃ q : Call, q.OKB ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 256#64 ∧ q.k = 1#64 ∧ q.u ms = 2#64)
    (hmem : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hbox : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J1 σ q.1.c0) → BoxW lbl q.1)
    (hcell : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J1 σ q.1.c0) → ∀ o : Nat, ms.lo o →
      o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hxa : ∀ l A s c, lbl l = none →
      At exe endPc (R.fp (-8)) F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c →
      TP t s → ms.xa l A 1 s c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J0⟩)
      (fun s c => At exe endPc R F (wXA ms (_root_.Executable.labels exe).label J1) s c ∧ TP t s) := by
  let lab := (_root_.Executable.labels exe).label
  have hpre := hello_wc_pre_segWA (p := p) (lbl := lbl) (ms := tpXa ms t) (W := NoSetFsW (tpG t W) K)
    hp hend hF hR hlo hhi hWp (fun σ c h => { hlim σ c h with }) hloc
    (fun σ c h => let ⟨q, hq1, hq2⟩ := hq σ c h; ⟨q, okb_tpXa hq1, hq2⟩)
    (fun q hq a ha m hm => hmem q (okb_of_tpXa hq) a ha m hm)
  have hsp0 := hello_wc_sp0_segW (p := p) (lbl := lbl) (ms := tpXa ms t) (W := NoSetFsW (tpG t W) K)
    (Q := fun _ _ => False) hp hend hF hR (by omega) hhi hWs (fun q h => hbox ⟨q.1, okb_of_tpXa q.2⟩ h)
    (fun q h o h1 h2 => hcell ⟨q.1, okb_of_tpXa q.2⟩ h o h1 h2)
    (fun l A s c hl h ht => hxa l A s c hl (at_bXH_of_tpXa h) ht)
  have hin := (hpre.mono_post (Q' := fun s c => At exe endPc R F (wXH (tpXa ms t) lab R J1 .x18) s c ∨
    At exe endPc R F (wXA (tpXa ms t) lab J1) s c) fun s c ⟨y, h⟩ => by
      cases y
      · exact .inl h
      · exact .inr h).seq_left hsp0
  refine ((KeepTP.SegW.keepTP' hK hin (fun _ _ hw => hw.2.1) (fun _ _ hw s' hk _ => (hw.2.2 s' hk).elim)
    fun _ _ hw ht => hw.1 ht).mono_pre fun s c h => ⟨h, tp_of_at hJ0tp h⟩).mono_post ?_
  rintro s c ⟨h | h, ht⟩
  · exact h.elim
  · exact ⟨at_wXA_of_tpXa h, ht⟩

end Entry

/-- **`hello_wc_entry_segWA` at `scc_rt_main`'s call after `wc_rodata`** (region `HelloM.wcR R D`, frame
condition `HelloM.wcF`, entry invariant `HelloM.wcJ0 (Hello1.mWC lab σC Jr).J σ1`): the premises read off
`wc_rodata`'s return invariants `Jr`, `Jr1` and the caller's `F0` (`X64HelloWcEntry`). -/
theorem hello_wc_entry_segJrA {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {R : Region} {D : Int} {F0 : MachineData → Prop} {m1 : MachineData} {σC σ1 : AS}
    {Jr Jr1 : AS → Ctl → Prop} {t : UInt64} (hK : ms.K = some Scc.Sem.X64.abi)
    {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    (hF : FStable (wcR R D) (wcF R D F0 m1 σ1)) (hR : (wcR R D).OK)
    (hlo : (wcR R D).lo ≤ -304) (hhi : 8 ≤ (wcR R D).hi)
    (htp : ∀ σ c, Jr σ c → σ.regs.fsBase = t)
    (hWp : WcPreWH (NoSetFsW (tpG t W) K) K exe endPc (wcR R D) (wcF R D F0 m1 σ1) (tpXa ms t)
      (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr).J σ1)
      (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1))
    (hWs : WcSp0WH (NoSetFsW (tpG t W) K) K exe endPc (wcR R D) (wcF R D F0 m1 σ1) (tpXa ms t)
      (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1))
    (hlim : ∀ σ c, Jr σ c → LimOk ms F0 (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - 8#64 - (128 : Int64).toBitVec))
    (hloc : ∀ σ c, Jr σ c → ∃ c', LocalRun p c c' ∧ Jr1 σ c')
    (hq : ∀ σ c, Jr1 σ c → ∃ q : Call, q.OKB ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 256#64 ∧ q.k = 1#64 ∧ q.u ms = 2#64)
    (hmem0 : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F0 m → Mem.loadInt m.dmem a 8 = none)
    (hbox : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, Jr1 σ q.1.c0) → BoxW lbl q.1)
    (hcell0 : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, Jr1 σ q.1.c0) → ∀ o : Nat, ms.lo o →
      o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F0 m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hxa : ∀ l A s c, lbl l = none → At exe endPc ((wcR R D).fp (-8)) (wcF R D F0 m1 σ1)
      (bXH ms (_root_.Executable.labels exe).label (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)
        l A) s c →
      TP t s → ms.xa l A 1 s c) :
    SegW W K p lbl ms (At exe endPc (wcR R D) (wcF R D F0 m1 σ1)
        ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩,
          wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr).J σ1⟩)
      (fun s c => At exe endPc (wcR R D) (wcF R D F0 m1 σ1)
        (wXA ms (_root_.Executable.labels exe).label (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1))
          s c ∧ TP t s) :=
  hello_wc_entry_segWA hK hp hend hF hR hlo hhi (tp_wcJ0 htp) hWp hWs (lim_wcJ0 hlim) (loc_wcJ0 hloc)
    (ctl_wcJ0 hq) (mem_wcF hmem0) (fun q h => hbox q (hj_wcJ0 h)) (cell_wcF hcell0) hxa

end Spike.Lib.X64.Flow.HelloWc

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.Flow.HelloWc.hello_wc_pre_segWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.hello_wc_pre_segWA

/-- info: 'Spike.Lib.X64.Flow.HelloWc.at_wXA_of_tpXa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.at_wXA_of_tpXa

/--
info: 'Spike.Lib.X64.Flow.HelloWc.hello_wc_entry_segWA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.hello_wc_entry_segWA

/--
info: 'Spike.Lib.X64.Flow.HelloWc.hello_wc_entry_segJrA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.hello_wc_entry_segJrA
