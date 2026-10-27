/-
**`hello1.w`'s `wc_rodata` with the source's local steps on x64**: the
segments of `Spike/Lib/X64Hello1Rodata.lean` with the source advanced by
local runs inside its blocks, for a source whose body binds values before
its allocation and between its exchanges (`hello1`'s `rodata`,
`Spike/Lib/Hello1RodataSrc.lean`). The x64 twin of
`Spike/Lib/A64Hello1RodataS.lean`.

- `rNL`: the nodes up to the call, the entry block's at the entry's
  invariant `J0`, the call's at `J1`;
- `hello1_rodata_pre_runW`: `hello1_rodata_pre_segW` with the source taking
  a local run from `J0`'s controls to `J1`'s in the entry block (`hloc`),
  the allocation's premises asked at `J1` (`hq`).
-/
import Spike.Lib.X64Hello1Rodata

namespace Spike.Lib.X64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)
open Spike.Lib.X64.Flow.Ret0 (CallerCells LimOk)
open Spike.Lib.X64.Alloc (Call AllocW Ea Jfull)

set_option linter.unusedSimpArgs false

/-! ## `wc_rodata` up to the allocator's return, the source advanced -/

/-- **The nodes up to the call**: `.entry` at the entry's invariant `J0`,
the allocator's entry at `J1` (the source advanced in the block). -/
def rNL (lab : Label → Int64) (R : Region) (J0 J1 : AS → Ctl → Prop) : RN → ND
  | .e => rN lab R J0 .e
  | .call => rN lab R J1 .call

section RdFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_rodata` up to the allocator's return, the source advanced in its
entry block, is one segment inside `W`** in any valid layout of
`hello1Cells`: `hello1_rodata_pre_segW` where the entry block takes a local
run from each control of the entry's invariant `J0` to one of `J1` at the
same state (`hloc`), the allocation's premises holding at `J1`'s controls
(`hq`); the exits are at `J1`. -/
theorem hello1_rodata_pre_runW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -208) (hhi : 8 ≤ R.hi)
    {J0 J1 : AS → Ctl → Prop} (hW : RdPreW W K exe endPc R F ms J0 J1)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (32 : Int64).toBitVec))
    (hloc : ∀ σ c, J0 σ c → ∃ c', LocalRun p c c' ∧ J1 σ c')
    (hq : ∀ σ c, J1 σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ms = 3#64)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧
        (rNL (_root_.Executable.labels exe).label R J0 J1 .call).J σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧
        CKept R (-48) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR R) F' (Ea ms q.1 l b w) s c → ms.xa l b w s c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_rodata", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (rX ms (_root_.Executable.labels exe).label lbl R J1 y) s c) := by
  have hin := hello1_rdEIn
  simp only [rdEIn, Bool.and_eq_true] at hin
  obtain ⟨h0, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e26 : lab ".Lwc_rodata.x13" = lab ".Lwc_rodata.entry" + Int64.ofNat 26 := label_labelGapB hp hgap
  refine SegW.seq (hello1_rodata_prologue_segW hp hend (nb := ⟨lab ".Lwc_rodata.entry", oR, rdJ J0⟩)
    hF hR (by omega) (by omega) rfl (by show SO.le oR (oF 32) = true; decide) hW.pro ?_)
    ((fn_segW (N := rNL lab R J0 J1) (E := rX ms lab lbl R J1) (fun i => ?_) RN.e).mono_pre
      fun _ _ h => At.reg_addr (r := .rbp) (k := -8) rfl h)
  · intro σ c hJ
    have hl := hlim σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64]
  cases i
  case e =>
    refine seg_ndW (by simp [rdE]) rdE_ok hF hR hlo hhi (code_field hp hend h0 (ofNat_zero' _)) hW.e
      fun σ c hJ => ?_
    obtain ⟨⟨σe, hJe, h0', h8⟩, hb⟩ := hJ
    obtain ⟨c', hr, hJ1⟩ := hloc σe c hJe
    refine ⟨c', hr, .inl ⟨RN.call, ?_, ?_, ?_⟩⟩
    · simp only [rNL, rN]; rw [rdE_run]
    · simp only [rNL, rN]; rw [rdE_run]; rfl
    · simp only [rNL, rN]
      rw [rdE_run]
      refine ⟨⟨σe, hJ1, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [upd_apply]; exact h0'
      · simp only [upd_apply]; exact h8
      · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; exact hb
      · simp [Reg64s.set64]
      · simp [Reg64s.set64]
      · simp [Reg64s.set64]
      · rw [e26]
        simp only [upd_apply, ↓reduceIte, Int64.toBitVec_add]
        rfl
  case call =>
    refine call_nd_FWK (KC := False) (e0 := 0) (lo' := -160) (hi' := 8) (M := fun _ => True)
      (Ne := fun g : AG ms lab => Alloc.N lab ms g.1 .e) (Ex := fun g : AG ms lab => Alloc.E lab ms g.1 lbl)
      hR hF (by show R.lo ≤ -48 - 0 + -160; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide) (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, -, -, -, h48⟩, ⟨-, -, hra, -⟩⟩ := hg
        have hr : g.1.ra = (lab ".Lwc_rodata.x13").toBitVec := by
          rw [← hra, ← h48]; rfl
        exact (Alloc.seg_allocW hp hend Alloc.hello1_allocIn hF' hR' hlo' hhi' g.2
          (fun a ha m hm => hmem g.1 g.2 a ha m (hFF m hm))
          (hxa g F' hFF hkeep)
          (allocW_mono (hW.alloc g.1 g.2 hr) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩)).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨σe, hJe, -, -⟩, -, h0, h1, h2, -⟩
      obtain ⟨q, hok, hc, hh, hk, hu⟩ := hq σe c hJe
      exact ⟨⟨{ q with fp := σC.regs.rbp.toBitVec, ra := σC.slot (-48 - 0 + 0) }, { hok with }⟩, rfl,
        hc.symm, rfl, rfl, h0.trans hh.symm, h1.trans hk.symm, h2.trans hu.symm⟩
    · rintro g y σC c σx c' σR ⟨⟨σe, hJe, h0', h8⟩, hb, -, -, -, h48⟩ ⟨hc, hfp, hra, -⟩ hx hreg - - hsl
      cases y
      · refine .inr ⟨RX.x13, ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, g,
          ⟨σe, hc ▸ hJe, ?_, ?_⟩, ?_, ?_⟩
        · show lab ".Lwc_rodata.x13" = Int64.ofBitVec g.1.ra
          rw [← hra]
          show _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
          rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
        · rw [hsl 0 ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, rNL, rN]; omega),
            h0']
        · rw [hsl (-8) ⟨by decide, by omega, by omega⟩
            (by simp only [Region.Off, Region.callee, rNL, rN]; omega), h8]
        · simp only [Alloc.E] at hx
          obtain ⟨-, -, -, -, -, -, -, hbx⟩ := hx
          rw [← hb]
          simp only [Reg64s.get64]
          rw [hreg, hbx, ← hfp]; rfl
        · simp only [Alloc.E] at hx ⊢
          rw [hreg]; exact hx
      · obtain ⟨h2, hfull⟩ := hx
        refine .inr ⟨RX.abort, rfl, by show SO.le ⟨-208, []⟩ ⟨-48 - 0 + -160, []⟩ = true; decide, ?_,
          g, hfull, σe, hc ▸ hJe⟩
        show σR.regs.rdi.toBitVec = 2#64
        rw [hreg]; exact h2

end RdFn

end Spike.Lib.X64.Flow.Hello1
