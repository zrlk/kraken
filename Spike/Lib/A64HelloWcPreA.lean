/-
**`wc_main` up to the box's allocator's return, the heap abort keeping the spills** (AArch64, row
`5h-S-habctl-L1`): `HelloWc.hello_wc_pre_segW` with its heap-abort exit strengthened to
`wXA`: `wXH .abort`'s invariant and, for the call's entry witness `σe`, `wc_main`'s spilled argument words at the
abort's abstract state (`σ.slot (-144 … -112) = σe.x0 … x4`). The allocator's call context keeps `wc_main`'s frame
outside the allocator's region (`CKept R (-144) (-160) 0`), so the slots are the call node's (`wcJH`), as at
`.sp0`. `HabCtl`'s abort-path placement (`HabCtlHS`) reads `c0H`'s words from them.

- `wXA`, `wXHA`: the strengthened abort node; the exits with it.
- `at_wXA_wXH`: `wXA` is `wXH .abort` with more.
- `hello_wc_pre_segWA`: the segment with the exits `wXHA`.
- `at_wXA_of_tpXa`, `hello_wc_entry_segWA`, `hello_wc_entry_segJrA`: `HelloWc.hello_wc_entry_segW`/`…segJr`'s
  twins with the abort at `wXA`.
-/
import Spike.Lib.A64HelloWcEntry

namespace Spike.Lib.A64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk)
open Spike.Lib.A64.Alloc (Call AllocW Ea Jfull)
open Spike.Lib.A64.Flow.WakeWc (AGB BoxW tpG tp_of_at okb_tpXa okb_of_tpXa seg_allocB_ofW WN WX)
open Spike.Lib.A64.Flow.HelloRd (hello_alloc)
open Spike.Lib.A64.Flow.HelloM (wcJ0 wcR wcF)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)

set_option linter.unusedSimpArgs false

/-- **The allocator's heap abort with `wc_main`'s spills** (`wXH .abort` and the call's entry witness's argument
words at the spill slots). -/
def wXA (ms : MemSide isaLSE2) (lab : Label → Int64) (J1 : AS → Ctl → Prop) : ND :=
  ⟨lab "scc_rt_abort", ⟨-304, []⟩, fun σ c => σ.regs.X0 = 2 ∧
    σ.regs.X30.toBitVec = (lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec ∧ ∃ q : AGB ms lab, Jfull ms q.1 c ∧
    ∃ σe, J1 σe q.1.c0 ∧ σ.slot (-144) = σe.regs.X0.toBitVec ∧ σ.slot (-136) = σe.regs.X1.toBitVec ∧
      σ.slot (-128) = σe.regs.X2.toBitVec ∧ σ.slot (-120) = σe.regs.X3.toBitVec ∧
      σ.slot (-112) = σe.regs.X4.toBitVec⟩

/-- **The exits with the abort at `wXA`**. -/
def wXHA (ms : MemSide isaLSE2) (lab : Label → Int64) (J1 : AS → Ctl → Prop) : WX → ND
  | .sp0 => wXH ms lab J1 .sp0
  | .abort => wXA ms lab J1

/-- **`wXA` is `wXH .abort` with the spills**. -/
theorem at_wXA_wXH {ms : MemSide isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {J1 : AS → Ctl → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F (wXA ms (_root_.Executable.labels exe).label J1) s c) :
    At exe endPc R F (wXH ms (_root_.Executable.labels exe).label J1 .abort) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, h0, h30, q, hq, σe, hJ, -⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, h0, h30, q, hq, σe, hJ⟩

section WcFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`hello_wc_pre_segW` with the heap abort at `wXA`** (the spilled words recorded): the same segment, its
abort exit's abstract state keeping `wc_main`'s spill slots `-144 … -112` (the allocator's call context keeps
`wc_main`'s frame outside its region, `CKept R (-144) (-160) 0`; the slots are the call node's `wcJH`). -/
theorem hello_wc_pre_segWA {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    {J0 J1 : AS → Ctl → Prop} (hW : WcPreWH W K exe endPc R F ms J0 J1)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (144 : Int64).toBitVec))
    (hloc : ∀ σ c, J0 σ c → ∃ c', LocalRun p c c' ∧ J1 σ c')
    (hq : ∀ σ c, J1 σ c → ∃ q : Call, q.OKB ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 256#64 ∧ q.k = 1#64 ∧ q.u ms = 2#64)
    (hmem : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (wXHA ms (_root_.Executable.labels exe).label J1 y) s c) := by
  have hin := hello_wcEInH
  simp only [wcEInH, Bool.and_eq_true] at hin
  obtain ⟨h0, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e4 : lab ".L22_wc_main.sp0" = lab ".L22_wc_main.0_entry" + Int64.ofNat (4 * 4) := label_labelGap hp hgap
  refine SegW.seq (prologue_seg_ofW hp hend hello_wcPro (nb := wNH lab J0 J1 .e) (by decide) (by decide) hF hR hal
    (by show R.lo ≤ -144; omega) hhi (by decide) rfl
    (by show SO.le ⟨-144, []⟩ (oFr 144) = true; decide) hW.pro ?_)
    (fn_segW (N := wNH lab J0 J1) (E := wXHA ms lab J1) (fun i => ?_) WN.e)
  · intro σ c hJ
    have hl := hlim σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs]
  cases i
  case e =>
    refine seg_ndW (by simp [wcEH]) wcEH_ok hF hR hal hlo hhi (code_of hp hend h0 (ofNat4_zero _)) hW.e
      fun σ c hJ => ?_
    obtain ⟨σe, hJe, h16, h8, h0', h1', h2', h3', h4'⟩ := hJ
    obtain ⟨c', hr, hJ1⟩ := hloc σe c hJe
    refine ⟨c', hr, .inl ⟨WN.call, ?_, ?_, ?_⟩⟩
    · simp only [wNH]; rw [wcEH_run]
    · simp only [wNH]; rw [wcEH_run]; rfl
    · simp only [wNH]
      rw [wcEH_run]
      refine ⟨⟨σe, hJ1, h16, h8, h0', h1', h2', h3', h4'⟩, rfl, rfl, rfl, ?_⟩
      rw [e4]
      show BitVec.ofInt 64 _ = _
      rw [Ret0.ofInt_bmod]
      simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
      rfl
  case call =>
    refine call_nd_FWK (KC := False) (lo' := -160) (hi' := 0) (M := fun _ => True)
      (Ne := fun g : AGB ms lab => Alloc.N lab ms g.1 .e) (Ex := fun g : AGB ms lab => Alloc.EB lab ms g.1)
      hR hal hF (by show R.lo ≤ -144 + -160; omega) (by decide) (by show (-144 : Int) < R.hi; omega) (by decide)
      (by show (-144 : Int) % 16 = 0; decide) (by decide) (by decide) (fun h => h.elim) (fun h => h.elim)
      (fun _ h _ => h)
      (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, -, -, h30⟩, ⟨-, -, h30', -⟩⟩ := hg
        have hra : g.1.ra = (lab ".L22_wc_main.sp0").toBitVec := by
          rw [← h30']; exact h30
        exact (seg_allocB_ofW hp hend hello_alloc hF' hR' hal' hlo' hhi' g.2
          (fun a ha m hm => hmem g.1 g.2 a ha m (hFF m hm))
          (allocW_mono (hW.alloc g.1 g.2 hra) fun m h =>
            ⟨hFF m h, hcc m h, hkeep m h⟩)).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨σe, hJe, -⟩, h0, h1, h2, -⟩
      obtain ⟨q, hok, hc, hh, hk, hu⟩ := hq σe c hJe
      exact ⟨⟨{ q with x29 := σC.regs.X29.toBitVec, ra := σC.regs.X30.toBitVec },
        ⟨{ hok.toS with }, hok.newOk, hok.term, hok.ev, hok.one⟩⟩, rfl,
        hc.symm, rfl, rfl, h0.trans hh.symm, h1.trans hk.symm, h2.trans hu.symm⟩
    · rintro g y σC c σx c' σR ⟨⟨σe, hJe, h16, h8, h0', h1', h2', h3', h4'⟩, -, -, -, h30⟩ ⟨hc, -, h30', -⟩ hx
        hreg - hsl
      have hk : ∀ k : Int, -144 ≤ k → k < 0 → k % 8 = 0 → σR.slot k = σC.slot k := fun k hk1 hk2 hk3 =>
        hsl k ⟨by omega, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wNH]; omega)
      cases y
      · refine .inr ⟨WX.sp0, ?_, rfl, g, ⟨σe, hc ▸ hJe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · show lab ".L22_wc_main.sp0" = Int64.ofBitVec g.1.ra
          rw [← h30']
          show _ = Int64.ofBitVec σC.regs.X30.toBitVec
          rw [h30, int64_ofBitVec_toBitVec]
        · exact (hk (-16) (by decide) (by decide) (by decide)).trans h16
        · exact (hk (-8) (by decide) (by decide) (by decide)).trans h8
        · exact (hk (-144) (by decide) (by decide) (by decide)).trans h0'
        · exact (hk (-136) (by decide) (by decide) (by decide)).trans h1'
        · exact (hk (-128) (by decide) (by decide) (by decide)).trans h2'
        · exact (hk (-120) (by decide) (by decide) (by decide)).trans h3'
        · exact (hk (-112) (by decide) (by decide) (by decide)).trans h4'
        · simp only [Alloc.EB] at hx ⊢
          rw [hreg]; exact hx
      · obtain ⟨h2, h30x, hfull⟩ := hx
        refine .inr ⟨WX.abort, rfl, rfl, ?_, ?_, g, hfull, σe, hc ▸ hJe, ?_, ?_, ?_, ?_, ?_⟩
        · show σR.regs.X0 = 2
          rw [hreg]; exact h2
        · show σR.regs.X30.toBitVec = _
          rw [hreg]; exact h30x
        · exact (hk (-144) (by decide) (by decide) (by decide)).trans h0'
        · exact (hk (-136) (by decide) (by decide) (by decide)).trans h1'
        · exact (hk (-128) (by decide) (by decide) (by decide)).trans h2'
        · exact (hk (-120) (by decide) (by decide) (by decide)).trans h3'
        · exact (hk (-112) (by decide) (by decide) (by decide)).trans h4'

end WcFn

/-- **`wXA` at `tpXa` is at `ms`**. -/
theorem at_wXA_of_tpXa {ms : MemSide isaLSE2} {t : UInt64} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {J1 : AS → Ctl → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F (wXA (tpXa ms t) (_root_.Executable.labels exe).label J1) s c) :
    At exe endPc R F (wXA ms (_root_.Executable.labels exe).label J1) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, h0, h30, q, hq, hJ⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, h0, h30, ⟨q.1, okb_of_tpXa q.2⟩, hq, hJ⟩

section Entry

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`hello_wc_entry_segW` with the heap abort at `wXA`** (`hello_wc_pre_segWA`). -/
theorem hello_wc_entry_segWA {t : UInt64} (hK : ms.K = some Scc.Sem.A64.abi)
    {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    {J0 J1 : AS → Ctl → Prop} (hJ0tp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = t)
    (hWp : WcPreWH (NoMsrW (tpG t W) K) K exe endPc R F (tpXa ms t) J0 J1)
    (hWs : WcSp0WH (NoMsrW (tpG t W) K) K exe endPc R F (tpXa ms t) J1)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (144 : Int64).toBitVec))
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
    (hxa : ∀ l A s c, lbl l = none → At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c →
      TP t s → ms.xa l A 1 s c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J0⟩)
      (fun s c => At exe endPc R F (wXA ms (_root_.Executable.labels exe).label J1) s c ∧ TP t s) := by
  let lab := (_root_.Executable.labels exe).label
  have hpre := hello_wc_pre_segWA (p := p) (lbl := lbl) (ms := tpXa ms t) (W := NoMsrW (tpG t W) K)
    hp hend hF hR hal hlo hhi hWp (fun σ c h => { hlim σ c h with }) hloc
    (fun σ c h => let ⟨q, hq1, hq2⟩ := hq σ c h; ⟨q, okb_tpXa hq1, hq2⟩)
    (fun q hq a ha m hm => hmem q (okb_of_tpXa hq) a ha m hm)
  have hsp0 := hello_wc_sp0_segW (p := p) (lbl := lbl) (ms := tpXa ms t) (W := NoMsrW (tpG t W) K)
    (Q := fun _ _ => False) hp hend hF hR hal (by omega) hhi hWs (fun q h => hbox ⟨q.1, okb_of_tpXa q.2⟩ h)
    (fun q h o h1 h2 => hcell ⟨q.1, okb_of_tpXa q.2⟩ h o h1 h2)
    (fun l A s c hl h ht => hxa l A s c hl (at_bXH_of_tpXa h) ht)
  have hin := (hpre.mono_post (Q' := fun s c => At exe endPc R F (wXH (tpXa ms t) lab J1 .sp0) s c ∨
    At exe endPc R F (wXA (tpXa ms t) lab J1) s c) fun s c ⟨y, h⟩ => by
      cases y
      · exact .inl h
      · exact .inr h).seq_left hsp0
  refine ((SegW.keepTPN' hK hin fun _ _ h ht => h ht).mono_pre fun s c h => ⟨h, tp_of_at hJ0tp h⟩).mono_post ?_
  rintro s c ⟨h | h, ht⟩
  · exact h.elim
  · exact ⟨at_wXA_of_tpXa h, ht⟩

end Entry

/-- **`hello_wc_entry_segJr` with the heap abort at `wXA`** (`hello_wc_entry_segWA`). -/
theorem hello_wc_entry_segJrA {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {R : Region} {D : Int} {F0 : MachineData → Prop} {m1 : MachineData} {σC σ1 : AS}
    {Jr Jr1 : AS → Ctl → Prop} {t : UInt64} (hK : ms.K = some Scc.Sem.A64.abi)
    {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable (wcR R D) (wcF R D F0 m1 σ1)) (hR : (wcR R D).OK) (hal : (wcR R D).base.toNat % 16 = 0)
    (hlo : (wcR R D).lo ≤ -304) (hhi : 0 ≤ (wcR R D).hi)
    (htp : ∀ σ c, Jr σ c → σ.regs.TPIDR_EL0 = t)
    (hWp : WcPreWH (NoMsrW (tpG t W) K) K exe endPc (wcR R D) (wcF R D F0 m1 σ1) (tpXa ms t)
      (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr).J σ1)
      (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1))
    (hWs : WcSp0WH (NoMsrW (tpG t W) K) K exe endPc (wcR R D) (wcF R D F0 m1 σ1) (tpXa ms t)
      (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1))
    (hlim : ∀ σ c, Jr σ c → LimOk ms F0 exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (144 : Int64).toBitVec))
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
    (hxa : ∀ l A s c, lbl l = none → At exe endPc (wcR R D) (wcF R D F0 m1 σ1)
      (bXH ms (_root_.Executable.labels exe).label (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)
        l A) s c →
      TP t s → ms.xa l A 1 s c) :
    SegW W K p lbl ms (At exe endPc (wcR R D) (wcF R D F0 m1 σ1)
        ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩,
          wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr).J σ1⟩)
      (fun s c => At exe endPc (wcR R D) (wcF R D F0 m1 σ1)
        (wXA ms (_root_.Executable.labels exe).label (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1))
          s c ∧ TP t s) :=
  hello_wc_entry_segWA hK hp hend hF hR hal hlo hhi (tp_wcJ0 htp) hWp hWs (lim_wcJ0 hlim) (loc_wcJ0 hloc)
    (ctl_wcJ0 hq) (mem_wcF hmem0) (fun q h => hbox q (hj_wcJ0 h)) (cell_wcF hcell0) hxa

end Spike.Lib.A64.Flow.HelloWc

/-- info: 'Spike.Lib.A64.Flow.HelloWc.at_wXA_wXH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.at_wXA_wXH

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_pre_segWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_pre_segWA

/-- info: 'Spike.Lib.A64.Flow.HelloWc.at_wXA_of_tpXa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.at_wXA_of_tpXa

/--
info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_entry_segWA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_entry_segWA

/--
info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_entry_segJrA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_entry_segJrA
