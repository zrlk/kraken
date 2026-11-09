/-
**hello.w's `wc_main` up to the box's allocator's return** (x86-64; the twin of `Spike/Lib/A64HelloWcPre.lean`),
inside `W`, in any valid layout of `helloCells` (`Spike/Lib/X64HelloCode.lean`), from checks decided once on the
cells (`decide +kernel`). It is `X64WakeWcPre` at hello's `wc_main`:

    wc_main:          pushq %rbp; movq %rsp, %rbp; … subq $128, %rsp
                      movq %rdi, -8(%rbp) … movq %r8, -40(%rbp)      (the prologue, hWcPro)
    .Lwc_main.entry:  movq $256, %rdi; movq $1, %rsi; movq $2, %rdx
                      call scc_rt_alloc                              (wcEH)
    .Lwc_main.x0:                                                   -- the exit `wXH .x18`

The region `R` is `wc_main`'s as handed over at the call: based at the return address's cell, so the saved
`%rbp` is at `-8`, `main`'s five argument words (`%rdi, %rsi, %rdx, %rcx, %r8`: the slice's four registers and
main's `ThreadId`) at `-16 .. -48`, `%rsp` at `-136` past the prologue (`oWRH`), the pushed `.x22` at `-144`,
the allocator's region `R.callee (-144) (-160) 8` (`wARH`). From the box's store on the nodes are in the frame
based at the saved `%rbp` (`X64HelloWcSp6.oWH`), `R.fp (-8)`.

- `hWcPro`, `hello_wcPro`, `wcEH`, `wcEInH`, `hello_wcEInH`: the checks.
- `oWRH`, `wcJH`, `wNH`, `wXH`, `wARH`, `WcCtxH`, `WcPreWH`: the body's offsets, the frame (record, spills), the
  nodes and exits up to the allocator's return (the entry's at `J0`, the call's at `J1`), the allocator's region
  and call context, the states inside `W`.
- `hello_wc_pre_segW`: from `wc_main`'s entry to the allocator's return at `.x22` or its heap abort.

## Differences from the AArch64 version

- The frame is 128 below the saved `%rbp` (AArch64: 144 with the record at its top); the five argument words are
  spilled below `%rbp` (`-8 .. -40(%rbp)`, the region's `-16 .. -48`; AArch64: at the frame's base). `wcJH`
  records the return address and the caller's `%rbp` (AArch64: `x29`/`x30`).
- The nodes and exits are `X64WakeWcPre`'s shapes (`WakeWc.WN`/`WX`; the return exit is the constructor `.x18`,
  at hello's `.Lwc_main.x0`); the heap abort's return address is `.Lscc_rt_alloc.full + 12`, pushed at `-304`.
- `.entry` takes the source's local run to the box's allocation (`hloc`), as on AArch64 (wake: none).
-/
import Spike.Lib.X64HelloRodata

namespace Spike.Lib.X64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells LimOk)
open Spike.Lib.X64.Alloc (Call AllocW Jfull)
open Spike.Lib.X64.Flow.WakeWc (AGB WN WX call_nd_FWKL)
open Spike.Lib.X64.Flow.HelloRd (hello_alloc)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## The checks -/

/-- `wc_main`'s prologue: frame 128, its five argument words at `-8 .. -40(%rbp)`. -/
abbrev hWcPro : Bool := prologueIn SccCode.helloCells "wc_main" ".Lwc_main.chk" ".Lwc_main.entry" 128 8
  ".Lwc_main.stk" 5 9 3 6 7 [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4)]

theorem hello_wcPro : hWcPro = true := by decide +kernel

/-- `wc_main`'s `.entry` block: the box allocation's arguments, the call. -/
def wcEH : List (Directive × Nat) := (parse("movq $256, %rdi
movq $1, %rsi
movq $2, %rdx
call scc_rt_alloc")).zip [7, 7, 7, 5]

/-- `wc_main`'s body offsets from the return address's base: `%rsp` at the frame's base, `%rbp` at the saved
`%rbp`. -/
abbrev oWRH : SO := ⟨-136, [(.rbp, -8)]⟩

block_spec wcEH (-304) 8 oWRH wcEH

/-- **`wc_main`'s entry block in `cells`**, `.x22` right after the call. -/
def wcEInH (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_main.entry" 0 wcEH && labelGapB cells ".Lwc_main.entry" ".Lwc_main.x0" 26

theorem hello_wcEInH : wcEInH SccCode.helloCells = true := by decide +kernel

/-! ## Nodes -/

/-- **`wc_main`'s frame** as some entry state of `J` left it: the return address, the caller's `%rbp`, the five
spilled argument words. -/
def wcJH (J : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ σe, J σe c ∧ σ.slot 0 = σe.slot 0 ∧ σ.slot (-8) = σe.regs.rbp.toBitVec ∧
    σ.slot (-16) = σe.regs.rdi.toBitVec ∧ σ.slot (-24) = σe.regs.rsi.toBitVec ∧
    σ.slot (-32) = σe.regs.rdx.toBitVec ∧ σ.slot (-40) = σe.regs.rcx.toBitVec ∧ σ.slot (-48) = σe.regs.r8.toBitVec

section Wc

variable (ms : MemSide isa) (lab : Label → Int64) (R : Region) (J0 J1 : AS → Ctl → Prop)

/-- **The nodes**: `.entry` (at the entry's invariant `J0`, `%rbp` at the saved `%rbp`) and the allocator's
entry with its arguments (at `J1`, the source advanced in the block), the return address `.x22` pushed. -/
def wNH : WN → ND
  | .e => ⟨lab ".Lwc_main.entry", oWRH, Hello1.wJ R (wcJH J0)⟩
  | .call => ⟨lab "scc_rt_alloc", ⟨-144, []⟩, fun σ c => wcJH J1 σ c ∧ σ.regs.get64 .rbp = R.addr (-8) ∧
      σ.regs.rdi.toBitVec = 256#64 ∧ σ.regs.rsi.toBitVec = 1#64 ∧ σ.regs.rdx.toBitVec = 2#64 ∧
      σ.slot (-144) = (lab ".Lwc_main.x0").toBitVec⟩

/-- **The exits**: the allocator's return at `.x22` (its return's facts, the frame and `%rbp` kept), and its
heap abort (the return address `.Lscc_rt_alloc.full + 12` its `call scc_rt_abort` pushed, at `-304`). -/
def wXH : WX → ND
  | .x18 => ⟨lab ".Lwc_main.x0", ⟨-136, []⟩, fun σ c => ∃ q : AGB ms lab, wcJH J1 σ q.1.c0 ∧
      σ.regs.get64 .rbp = R.addr (-8) ∧ (Alloc.EB lab ms q.1 .ret).J σ c⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-304, []⟩, fun σ c => σ.regs.rdi.toBitVec = 2#64 ∧
      σ.slot (-304) = (lab ".Lscc_rt_alloc.full" + 12).toBitVec ∧
      ∃ q : AGB ms lab, Jfull ms q.1 c ∧ ∃ σe, J1 σe q.1.c0⟩

end Wc

/-- The allocator's region at the call: based at the pushed return address (`-144`), its frame of 160 below,
the return address cell above. -/
abbrev wARH (R : Region) : Region := R.callee (-144) (-160) 8

/-- **The allocator's call context in `wc_main`'s region `R`** at the memory `m` (`WakeWc.WcCtx` at the call's
`-144`). -/
def WcCtxH (ms : MemSide isa) (lab : Label → Int64) (R : Region) (J0 J1 : AS → Ctl → Prop) (q : Call)
    (m : MachineData) : Prop :=
  ∃ mC σC c, Abs R ⟨-144, []⟩ mC σC ∧ (wNH lab R J0 J1 .call).J σC c ∧
    (Alloc.N lab ms q .e).J (enter (-144) σC) c ∧ CKept R (-144) (-160) 8 mC m

/-- **`wc_main`'s states up to the allocator's return inside `W`**, none moved by `K`: its prologue's, the entry
block's, and the allocator's in its region. -/
structure WcPreWH (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (J0 J1 : AS → Ctl → Prop) : Prop where
  pro : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main") 128 8
    ".Lwc_main.stk" 5 9 3 6 7 [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4)] J0
  e : BlkW W K exe endPc R F (wNH (_root_.Executable.labels exe).label R J0 J1 .e) wcEH
  alloc : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label →
    q.ra = ((_root_.Executable.labels exe).label ".Lwc_main.x0").toBitVec →
    AllocW ms q W K exe endPc (wARH R)
      (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧ WcCtxH ms (_root_.Executable.labels exe).label R J0 J1 q m)

/-- `wc_main` up to the allocator's return is inside the trivial predicate, with no outside moves. -/
theorem WcPreWH.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {J0 J1 : AS → Ctl → Prop} :
    WcPreWH (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 J1 :=
  ⟨XProW.triv, BlkW.triv, fun q _ _ => Alloc.AllocW.triv ms q⟩

section WcFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` up to the box's allocator's return is one segment inside `W`** in any valid layout of
`helloCells`: from its entry (invariant `J0`, `%rsp` at the region's offset 0, the return address there, the
limit word's facts for its frame of 128 below the saved `%rbp`, `hlim`) to the allocator's return at `.x22` or
its heap abort.
- The entry block takes a local run from each of `J0`'s controls to one of `J1` at the same state (`hloc`).
- At `J1` the source is at a box allocation the allocator's premises hold for (`Call.OKB`: hello.w's
  `let o = new z`), with header `256`, one object of two units (`hq`).
- The counter and the headers the allocator may store are unmapped in private memory under `F` (`hmem`).
- The allocator's return keeps the hold recording the counter's old value (`Alloc.EB`).
- Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello_wc_pre_segW {W : Frag isa} {K : State → State → Prop}
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
      (fun s c => ∃ y, At exe endPc R F (wXH ms (_root_.Executable.labels exe).label R J1 y) s c) := by
  have hin := hello_wcEInH
  simp only [wcEInH, Bool.and_eq_true] at hin
  obtain ⟨h0, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e26 : lab ".Lwc_main.x0" = lab ".Lwc_main.entry" + Int64.ofNat 26 := label_labelGapB hp hgap
  refine SegW.seq (prologue_seg_ofW hp hend hello_wcPro (nb := ⟨lab ".Lwc_main.entry", oWRH, wcJH J0⟩)
    (by decide) hF hR
    (by show R.lo ≤ -8 - (128 : Int64).toInt; rw [show (128 : Int64).toInt = 128 from rfl]; omega) (by omega)
    (by decide) rfl (by show SO.le oWRH (oF 128) = true; decide) hW.pro ?_)
    ((fn_segW (N := wNH lab R J0 J1) (E := wXH ms lab R J1) (fun i => ?_) WN.e).mono_pre
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
          g, hfull, σe, hc ▸ hJe⟩
        · show σR.regs.rdi.toBitVec = 2#64
          rw [hreg]; exact h2
        · show σR.slot (-304) = _
          rw [hin (-304) (by simp only [Region.Off, Region.callee, wNH]; omega)]
          exact hs

end WcFn

end Spike.Lib.X64.Flow.HelloWc

/-- info: 'Spike.Lib.X64.Flow.HelloWc.hello_wcPro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.hello_wcPro

/-- info: 'Spike.Lib.X64.Flow.HelloWc.hello_wcEInH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.hello_wcEInH

/-- info: 'Spike.Lib.X64.Flow.HelloWc.hello_wc_pre_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.hello_wc_pre_segW
