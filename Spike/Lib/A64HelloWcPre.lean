/-
**`hello.w`'s `wc_main` up to the box's allocator's return** (AArch64), inside `W`, in any valid
layout of `helloProg` (`Spike/Lib/A64HelloCode.lean`), from checks decided once on the program (`decide +kernel`).
It is the twin of `Spike/Lib/A64WakeWcPre.lean` at hello's `wc_main` (`.L22_`). The differences:
- the frame is 144, with `main`'s five argument words spilled at the frame's base (`[sp, #0..32]`: the packet's
  four words and main's thread id);
- `.0_entry` takes the source's local run to the box's allocation (`hloc`: `HelloMainPreSrc.c0H_run`, from `main`'s
entry to `let o = new z`).

- `hWcPro`, `hello_wcPro`, `wcEH`, `wcEInH`, `hello_wcEInH`: the checks.
- `wcJH`, `wNH`, `wXH`, `wARH`, `WcCtxH`, `WcPreWH`: the frame (record, spills), the nodes and exits up to the
  allocator's return (the entry's at `J0`, the call's at `J1`), the allocator's region and call context, the states
  inside `W`.
- `hello_wc_pre_segW`: from `wc_main`'s entry to the allocator's return at `.sp0` or its heap abort.
-/
import Spike.Lib.A64HelloRodata
import Spike.Lib.A64WakeWcPre

namespace Spike.Lib.A64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk)
open Spike.Lib.A64.Alloc (Call AllocW Ea Jfull)
open Spike.Lib.A64.Flow.WakeWc (AGB seg_allocB_ofW WN WX)
open Spike.Lib.A64.Flow.HelloRd (hello_alloc)
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)

set_option linter.unusedSimpArgs false

/-! ## The checks -/

/-- `wc_main`'s prologue: frame 144, its five argument words at 0–32. -/
abbrev hWcPro : Bool := prologueIn SccCode.helloProg "wc_main" ".L22_wc_main.stack_check" ".L22_wc_main.0_entry"
  144 8 ".L22_wc_main.stack_grow" [(.X0, 0), (.X1, 8), (.X2, 16), (.X3, 24), (.X4, 32)]

theorem hello_wcPro : hWcPro = true := by decide +kernel

/-- `wc_main`'s `.0_entry` block: the box allocation's arguments, the call. -/
def wcEH : List Directive := parseAArch64("movz x0, #256
movz x1, #1
movz x2, #2
bl scc_rt_alloc")

block_spec wcEH (-304) 0 (⟨-144, []⟩ : SO) wcEH

/-- **`wc_main`'s entry block in `prog`**, `.sp0` right after the call. -/
def wcEInH (prog : List Directive) : Bool :=
  blockAt prog ".L22_wc_main.0_entry" 0 wcEH && labelGap prog ".L22_wc_main.0_entry" ".L22_wc_main.sp0" 4

theorem hello_wcEInH : wcEInH SccCode.helloProg = true := by decide +kernel

/-! ## Nodes -/

/-- **`wc_main`'s frame** as some entry state of `J` left it: the record and the five spilled argument words. -/
def wcJH (J : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ σe, J σe c ∧ σ.slot (-16) = σe.regs.X29.toBitVec ∧ σ.slot (-8) = σe.regs.X30.toBitVec ∧
    σ.slot (-144) = σe.regs.X0.toBitVec ∧ σ.slot (-136) = σe.regs.X1.toBitVec ∧
    σ.slot (-128) = σe.regs.X2.toBitVec ∧ σ.slot (-120) = σe.regs.X3.toBitVec ∧ σ.slot (-112) = σe.regs.X4.toBitVec

section Wc

variable (ms : MemSide isaLSE2) (lab : Label → Int64) (lbl : WeakMem.AllocLabel → Option Nat)
  (J0 J1 : AS → Ctl → Prop)

/-- **The nodes**: `.0_entry` (at the entry's invariant `J0`) and the allocator's entry with its arguments (at
`J1`, the source advanced in the block). -/
def wNH : WN → ND
  | .e => ⟨lab ".L22_wc_main.0_entry", ⟨-144, []⟩, wcJH J0⟩
  | .call => ⟨lab "scc_rt_alloc", ⟨-144, []⟩, fun σ c => wcJH J1 σ c ∧ σ.regs.X0.toBitVec = 256#64 ∧
      σ.regs.X1.toBitVec = 1#64 ∧ σ.regs.X2.toBitVec = 2#64 ∧
      σ.regs.X30.toBitVec = (lab ".L22_wc_main.sp0").toBitVec⟩

/-- **The exits**: the allocator's return at `.sp0` (its return's facts, the frame kept), and its heap abort
(`x30` past `.4_full`'s `bl scc_rt_abort`). -/
def wXH : WX → ND
  | .sp0 => ⟨lab ".L22_wc_main.sp0", ⟨-144, []⟩, fun σ c => ∃ q : AGB ms lab, wcJH J1 σ q.1.c0 ∧
      (Alloc.EB lab ms q.1 .ret).J σ c⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-304, []⟩, fun σ c => σ.regs.X0 = 2 ∧
      σ.regs.X30.toBitVec = (lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec ∧ ∃ q : AGB ms lab, Jfull ms q.1 c ∧
      ∃ σe, J1 σe q.1.c0⟩

end Wc

/-- The allocator's region at the call. -/
abbrev wARH (R : Region) : Region := R.callee (-144) (-160) 0

/-- **The allocator's call context in `wc_main`'s region `R`** at the memory `m` (`WakeWc.WcCtx` at frame 144). -/
def WcCtxH (ms : MemSide isaLSE2) (lab : Label → Int64) (R : Region) (J0 J1 : AS → Ctl → Prop) (q : Call)
    (m : MachineData) : Prop :=
  ∃ mC σC c, Abs R ⟨-144, []⟩ mC σC ∧ (wNH lab J0 J1 .call).J σC c ∧ (Alloc.N lab ms q .e).J (enter (-144) σC) c ∧
    CKept R (-144) (-160) 0 mC m

/-- **`wc_main`'s states up to the allocator's return inside `W`**, none moved by `K`: its prologue's, the entry
block's, and the allocator's in its region. -/
structure WcPreWH (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (J0 J1 : AS → Ctl → Prop) : Prop where
  pro : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main") 144 8
    ".L22_wc_main.stack_grow" [(.X0, 0), (.X1, 8), (.X2, 16), (.X3, 24), (.X4, 32)] J0
  e : BlkW W K exe endPc R F (wNH (_root_.Executable.labels exe).label J0 J1 .e) wcEH
  alloc : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label →
    q.ra = ((_root_.Executable.labels exe).label ".L22_wc_main.sp0").toBitVec →
    AllocW ms q W K exe endPc (wARH R)
      (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧ WcCtxH ms (_root_.Executable.labels exe).label R J0 J1 q m)

/-- `wc_main` up to the allocator's return is inside the trivial predicate, with no outside moves. -/
theorem WcPreWH.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {J0 J1 : AS → Ctl → Prop} :
    WcPreWH (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 J1 :=
  ⟨ProW.triv, BlkW.triv, fun q _ _ => Alloc.AllocW.triv ms q⟩

section WcFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` up to the box's allocator's return is one segment inside `W`** in any valid layout of
`helloProg`: from its entry (invariant `J0`, `sp` at the region's base, the limit word's facts for its frame of
144, `hlim`) to the allocator's return at `.sp0` or its heap abort.
- The entry block takes a local run from each of `J0`'s controls to one of `J1` at the same state (`hloc`).
- At `J1` the source is at a box allocation the allocator's premises hold for (`Call.OKB`: hello.w's
  `let o = new z`), with header `256`, one object of two units (`hq`).
- The counter and the headers the allocator may store are unmapped in private memory under `F` (`hmem`).
- The allocator's return keeps the hold recording the counter's old value (`Alloc.EB`): the source's `new` is
  taken at `.sp0`'s box store.
- Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello_wc_pre_segW {W : Frag isaLSE2} {K : State → State → Prop}
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
      (fun s c => ∃ y, At exe endPc R F (wXH ms (_root_.Executable.labels exe).label J1 y) s c) := by
  have hin := hello_wcEInH
  simp only [wcEInH, Bool.and_eq_true] at hin
  obtain ⟨h0, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e4 : lab ".L22_wc_main.sp0" = lab ".L22_wc_main.0_entry" + Int64.ofNat (4 * 4) := label_labelGap hp hgap
  refine SegW.seq (prologue_seg_ofW hp hend hello_wcPro (nb := wNH lab J0 J1 .e) (by decide) (by decide) hF hR hal
    (by show R.lo ≤ -144; omega) hhi (by decide) rfl
    (by show SO.le ⟨-144, []⟩ (oFr 144) = true; decide) hW.pro ?_)
    (fn_segW (N := wNH lab J0 J1) (E := wXH ms lab J1) (fun i => ?_) WN.e)
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
        refine .inr ⟨WX.abort, rfl, rfl, ?_, ?_, g, hfull, σe, hc ▸ hJe⟩
        · show σR.regs.X0 = 2
          rw [hreg]; exact h2
        · show σR.regs.X30.toBitVec = _
          rw [hreg]; exact h30x

end WcFn

end Spike.Lib.A64.Flow.HelloWc

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wcPro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wcPro

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wcEInH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wcEInH

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_pre_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_pre_segW
