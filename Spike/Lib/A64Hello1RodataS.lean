/-
**`hello1.w`'s `wc_rodata` with the source's local steps on AArch64**:
the segments of `Spike/Lib/A64Hello1Rodata.lean` with the source advanced
by local runs inside its blocks, for a source whose body binds values
before its allocation and between its exchanges (`hello1`'s `rodata`,
`Spike/Lib/Hello1RodataSrc.lean`).

- `rNL`: the nodes up to the call, the entry block's at the entry's
  invariant `J0`, the call's at `J1`;
- `hello1_rodata_pre_runW`: `hello1_rodata_pre_segW` with the source taking
  a local run from `J0`'s controls to `J1`'s in the entry block (`hloc`),
  the allocation's premises asked at `J1` (`hq`).
-/
import Spike.Lib.A64Hello1Rodata

namespace Spike.Lib.A64.Flow

namespace Hello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk)
open Spike.Lib.A64.Alloc (Call AllocW Ea Jfull)

set_option linter.unusedSimpArgs false

/-! ## `wc_rodata` up to the allocator's return, the source advanced -/

/-- **The nodes up to the call**: `.0_entry` at the entry's invariant
`J0`, the allocator's entry at `J1` (the source advanced in the block). -/
def rNL (lab : Label → Int64) (J0 J1 : AS → Ctl → Prop) : RN → ND
  | .e => rN lab J0 .e
  | .call => rN lab J1 .call

section RdFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_rodata` up to the allocator's return, the source advanced in its
entry block, is one segment inside `W`** in any valid layout of
`hello1Prog`: `hello1_rodata_pre_segW` where the entry block takes a local
run from each control of the entry's invariant `J0` to one of `J1` at the
same state (`hloc`), the allocation's premises holding at `J1`'s controls
(`hq`); the exits are at `J1`. -/
theorem hello1_rodata_pre_runW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    {J0 J1 : AS → Ctl → Prop} (hW : RdPreW W K exe endPc R F ms J0 J1)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (48 : Int64).toBitVec))
    (hloc : ∀ σ c, J0 σ c → ∃ c', LocalRun p c c' ∧ J1 σ c')
    (hq : ∀ σ c, J1 σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ms = 3#64)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧ (rNL (_root_.Executable.labels exe).label J0 J1 .call).J σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧ CKept R (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR R) F' (Ea ms q.1 l b w) s c → ms.xa l b w s c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_rodata", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (rX ms (_root_.Executable.labels exe).label lbl J1 y) s c) := by
  have hin := hello1_rdEIn
  simp only [rdEIn, Bool.and_eq_true] at hin
  obtain ⟨h0, hgap⟩ := hin
  have e4 := label_labelGap hp hgap
  let lab := (_root_.Executable.labels exe).label
  have e4' : lab ".L18_wc_rodata.sp0" = lab ".L18_wc_rodata.0_entry" + Int64.ofNat (4 * 4) := e4
  refine SegW.seq (hello1_rodata_prologue_segW hp hend (nb := rN lab J0 .e)
    hF hR hal (by omega) hhi rfl (by show SO.le ⟨-48, []⟩ (oFr 48) = true; decide) hW.pro ?_)
    (fn_segW (N := rNL lab J0 J1) (E := rX ms lab lbl J1) (fun i => ?_) RN.e)
  · intro σ c hJ
    have hl := hlim σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs]
  cases i
  case e =>
    refine seg_ndW (by simp [rdE]) rdE_ok hF hR hal hlo hhi (code_of hp hend h0 (ofNat4_zero _)) hW.e
      fun σ c hJ => ?_
    obtain ⟨σe, hJe, h16, h8⟩ := hJ
    obtain ⟨c', hr, hJ1⟩ := hloc σe c hJe
    refine ⟨c', hr, .inl ⟨RN.call, ?_, ?_, ?_⟩⟩
    · simp only [rNL, rN]; rw [rdE_run]
    · simp only [rNL, rN]; rw [rdE_run]; rfl
    · simp only [rNL, rN]
      rw [rdE_run]
      refine ⟨⟨σe, hJ1, h16, h8⟩, rfl, rfl, rfl, ?_⟩
      rw [e4']
      show BitVec.ofInt 64 _ = _
      rw [Ret0.ofInt_bmod]
      simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
      rfl
  case call =>
    refine call_nd_FWK (KC := False) (lo' := -160) (hi' := 0) (M := fun _ => True)
      (Ne := fun g : AG ms lab => Alloc.N lab ms g.1 .e) (Ex := fun g : AG ms lab => Alloc.E lab ms g.1 lbl)
      hR hal hF (by show R.lo ≤ -48 + -160; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
      (by show (-48 : Int) % 16 = 0; decide) (by decide) (by decide) (fun h => h.elim) (fun h => h.elim)
      (fun _ h _ => h)
      (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, -, -, h30⟩, ⟨-, -, h30', -⟩⟩ := hg
        have hra : g.1.ra = (lab ".L18_wc_rodata.sp0").toBitVec := by
          rw [← h30']; exact h30
        exact (seg_alloc_ofW hp hend hello1_alloc hF' hR' hal' hlo' hhi' g.2
          (fun a ha m hm => hmem g.1 g.2 a ha m (hFF m hm))
          (hxa g F' hFF hkeep)
          (allocW_mono (hW.alloc g.1 g.2 hra) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩)).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨σe, hJe, -, -⟩, h0, h1, h2, -⟩
      obtain ⟨q, hok, hc, hh, hk, hu⟩ := hq σe c hJe
      exact ⟨⟨{ q with x29 := σC.regs.X29.toBitVec, ra := σC.regs.X30.toBitVec }, { hok with }⟩, rfl,
        hc.symm, rfl, rfl, h0.trans hh.symm, h1.trans hk.symm, h2.trans hu.symm⟩
    · rintro g y σC c σx c' σR ⟨⟨σe, hJe, h16, h8⟩, -, -, -, h30⟩ ⟨hc, -, h30', -⟩ hx hreg - hsl
      cases y
      · refine .inr ⟨RX.sp0, ?_, rfl, g, ⟨σe, hc ▸ hJe, ?_, ?_⟩, ?_⟩
        · show lab ".L18_wc_rodata.sp0" = Int64.ofBitVec g.1.ra
          rw [← h30']
          show _ = Int64.ofBitVec σC.regs.X30.toBitVec
          rw [h30, int64_ofBitVec_toBitVec]
        · rw [hsl (-16) ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, rNL, rN]; omega), h16]
        · rw [hsl (-8) ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, rNL, rN]; omega), h8]
        · simp only [Alloc.E] at hx ⊢
          rw [hreg]; exact hx
      · obtain ⟨h2, hfull⟩ := hx
        refine .inr ⟨RX.abort, rfl, rfl, ?_, g, hfull, σe, hc ▸ hJe⟩
        show σR.regs.X0 = 2
        rw [hreg]; exact h2

end RdFn

end Hello1

end Spike.Lib.A64.Flow
