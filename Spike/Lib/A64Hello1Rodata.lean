/-
**`hello1.w`'s `wc_rodata` up to the allocator's return on AArch64**,
inside `W`, in any valid layout of `hello1Prog`
(`Spike/Lib/A64Hello1Code.lean`), from checks decided once on the program
(`decide +kernel`).

- `allocIn`, `hello1_alloc`: the allocator's blocks and single instructions
  at their labels in a program, checked on `hello1Prog`; `seg_alloc_ofW`:
  `seg_allocW` with its code from them.
- `hello1_rodata_pre_segW`: `wc_rodata` from its entry (invariant `J0`):
  its prologue, the block passing the allocation's arguments, and the call
  of `scc_rt_alloc` (`call_nd_FWK`, the allocator's frame of 160 below
  `wc_rodata`'s 48: the region reaches `-208`). Exits: the allocator's
  return to `.sp0` (the label already placed), and its heap abort; an
  allocation of a fresh label lands in `ms.xa` (`hxa`). The source is at a
  buffer allocation of two words with header `257` from the entry on
  (`hq`).
- `hello1_rodata_post_segW`: `wc_rodata` from `.sp0` to its return: the two
  exchanges of the buffer's words (each load a hold, `holdLd_ndW`; each
  store the exchange, `xchgSt_ndW`), the results and the epilogue. The
  source's facts at each exchange stay given (`h1` … `h4`, over invariants
  `J1` … `J4` of `.sp0`'s state), as does its run at the return (`hedge`).
-/
import Spike.Lib.A64Hello1Body
import Spike.Lib.A64Alloc
import Scc.Cert.Rt.A64AllocIn

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)

set_option linter.unusedSimpArgs false

/-! ## `scc_rt_alloc` -/

section Alloc

open Scc.Cert.Rt.A64.Print (code_field add4 add0)
open Spike.Lib.A64.Alloc

theorem hello1_alloc : allocIn SccCode.hello1Prog = true := by decide +kernel

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {q : Call}

/-- **`scc_rt_alloc`'s code** for the call `q` in any valid layout `exe` of a
program `prog` with `allocIn prog = true`. -/
theorem alloc_code {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : allocIn prog = true) : Code ms q exe endPc := by
  simp only [allocIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, hgap⟩ := hprog
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact code_field hp hend h0 (by simp only [N, add4, add0])
  · exact code_field hp hend h1 (by simp only [N, add4, add0])
  · exact code_field hp hend h2 (by simp only [N, add4, add0])
  · exact code_field hp hend h3 (by simp only [N, add4, add0])
  · exact code_field hp hend h4 (by simp only [N, add4, add0])
  · exact code_field hp hend h5 (by simp only [N, add4, add0])
  · exact code_field hp hend h6 (by simp only [N, add4, add0])
  · exact code_field hp hend h7 (by simp only [N, add4, add0])
  · exact code_field hp hend h8 (by simp only [N, add4, add0])
  · exact code_field hp hend h9 (by simp only [N, add4, add0])
  · exact code_field hp hend h10 (by simp only [N, add4, add0])
  · exact code_field hp hend h11 (by simp only [N, add4, add0])
  · exact code_field hp hend h12 (by simp only [N, add4, add0])
  · exact code_field hp hend h13 (by simp only [N, add4, add0])
  · exact code_field hp hend h14 (by simp only [N, add4, add0])
  · exact code_field hp hend h15 (by simp only [N, add4, add0])
  · exact code_field hp hend h16 (by simp only [N, add4, add0])
  · exact code_field hp hend h17 (by simp only [N, add4, add0])
  · exact code_field hp hend h18 (by simp only [N, add4, add0])

/-- **`scc_rt_alloc` is one segment inside `W` from any of its nodes `i0`**
in any valid layout `exe` of a program `prog` with `allocIn prog = true`
(`hello1_alloc` for `hello1Prog`): `seg_allocW_at` with its code from the
checks. -/
theorem seg_alloc_ofW_at {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive}
    {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : allocIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : q.OK ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R F (Ea ms q l b w) s c → ms.xa l b w s c)
    (hW : AllocW ms q W K exe endPc R F) (i0 : AN) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q i0))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label ms q lbl x) s c) := by
  have hcode := alloc_code (ms := ms) (q := q) hp hend hprog
  simp only [allocIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap⟩ := hprog
  exact seg_allocW_at hF hR hal hlo hhi hq hcode (by rw [label_labelGap hp hgap]; simp only [add4, add0]) hmem hxa
    hW i0

/-- **`scc_rt_alloc` is one segment inside `W`** in any valid layout `exe`
of a program `prog` with `allocIn prog = true` (`hello1_alloc` for
`hello1Prog`): `seg_alloc_ofW_at` from its entry. -/
theorem seg_alloc_ofW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive}
    {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : allocIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : q.OK ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ l b w s c, lbl l = none →
      At exe endPc R F (Ea ms q l b w) s c → ms.xa l b w s c)
    (hW : AllocW ms q W K exe endPc R F) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label ms q .e))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label ms q lbl x) s c) :=
  seg_alloc_ofW_at hp hend hprog hF hR hal hlo hhi hq hmem hxa hW .e

omit [Kraken.Executable.ValidLayout exe] in
/-- The allocator's obligations under a weaker frame condition hold under a
stronger one. -/
theorem allocW_mono {W : Frag isaLSE2} {K : State → State → Prop} {F' : MachineData → Prop}
    (h : AllocW ms q W K exe endPc R F) (hFF : ∀ m, F' m → F m) : AllocW ms q W K exe endPc R F' :=
  ⟨Ret0.blkW_mono h.e hFF, Ret0.blkW_mono h.entry hFF, Ret0.blkW_mono h.n2 hFF, Ret0.nodeW_mono h.cnt hFF,
    Ret0.nodeW_mono h.cnt1 hFF, Ret0.blkW_mono h.cnt2 hFF, Ret0.nodeW_mono h.rmw hFF, Ret0.blkW_mono h.n4 hFF,
    Ret0.blkW_mono h.n5 hFF, Ret0.blkW_mono h.slow hFF, Ret0.blkW_mono h.n7 hFF, Ret0.blkW_mono h.full hFF,
    Ret0.blkW_mono h.ok hFF, Ret0.nodeW_mono h.ok1 hFF, Ret0.nodeW_mono h.ok2 hFF, Ret0.blkW_mono h.n12 hFF,
    Ret0.nodeW_mono h.hdr hFF, Ret0.blkW_mono h.n13 hFF, Ret0.nodeW_mono h.ret hFF⟩

end Alloc

/-! ## `wc_rodata` up to the allocator's return -/

namespace Hello1

open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk)
open Spike.Lib.A64.Alloc (Call AllocW Ea Jfull)

/-- `wc_rodata`'s `.0_entry` block: the allocation's arguments, the call. -/
def rdE : List Directive := parseAArch64("movz x0, #257
movz x1, #2
movz x2, #3
bl scc_rt_alloc")

block_spec rdE (-208) 0 (⟨-48, []⟩ : SO) rdE

/-- **`wc_rodata`'s entry block in `prog`**, `.sp0` right after the call. -/
def rdEIn (prog : List Directive) : Bool :=
  blockAt prog ".L18_wc_rodata.0_entry" 0 rdE && labelGap prog ".L18_wc_rodata.0_entry" ".L18_wc_rodata.sp0" 4

theorem hello1_rdEIn : rdEIn SccCode.hello1Prog = true := by decide +kernel

/-- `wc_rodata`'s frame record as some entry state of `J0` left it. -/
def rdJ (J0 : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ σe, J0 σe c ∧ σ.slot (-16) = σe.regs.X29.toBitVec ∧ σ.slot (-8) = σe.regs.X30.toBitVec

/-- The allocator's ghost: a call with its premises. -/
abbrev AG (ms : MemSide isaLSE2) (lab : Label → Int64) : Type := {q : Call // q.OK ms lab}

/-- `wc_rodata`'s nodes up to the call. -/
inductive RN where
  | e | call

/-- `wc_rodata`'s exits up to the allocator's return. -/
inductive RX where
  | sp0 | abort

section Rd

variable (ms : MemSide isaLSE2) (lab : Label → Int64) (lbl : WeakMem.AllocLabel → Option Nat)
  (J0 : AS → Ctl → Prop)

/-- **The nodes**: `.0_entry` and the allocator's entry with its arguments. -/
def rN : RN → ND
  | .e => ⟨lab ".L18_wc_rodata.0_entry", ⟨-48, []⟩, rdJ J0⟩
  | .call => ⟨lab "scc_rt_alloc", ⟨-48, []⟩, fun σ c => rdJ J0 σ c ∧ σ.regs.X0.toBitVec = 257#64 ∧
      σ.regs.X1.toBitVec = 2#64 ∧ σ.regs.X2.toBitVec = 3#64 ∧
      σ.regs.X30.toBitVec = (lab ".L18_wc_rodata.sp0").toBitVec⟩

/-- **The exits**: the allocator's return at `.sp0` (its return's facts,
the frame record kept), and its heap abort. -/
def rX : RX → ND
  | .sp0 => ⟨lab ".L18_wc_rodata.sp0", ⟨-48, []⟩, fun σ c => ∃ q : AG ms lab, rdJ J0 σ q.1.c0 ∧
      (Alloc.E lab ms q.1 lbl .ret).J σ c⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-208, []⟩, fun σ c => σ.regs.X0 = 2 ∧ ∃ q : AG ms lab, Jfull ms q.1 c ∧
      ∃ σe, J0 σe q.1.c0⟩

end Rd

/-- The allocator's region at the call. -/
abbrev aR (R : Region) : Region := R.callee (-48) (-160) 0

/-- **The allocator's call context in `wc_rodata`'s region `R`** at the
memory `m`: some caller's state `mC`, `σC` at the call node (`rN .call` at
the invariant `Jc`) whose entry into the allocator is at `q`'s entry, the
caller's cells outside the allocator's region as at the call
(`call_nd_FWK`'s callee frame condition). -/
def RdCtx (ms : MemSide isaLSE2) (lab : Label → Int64) (R : Region) (Jc : AS → Ctl → Prop) (q : Call)
    (m : MachineData) : Prop :=
  ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧ (rN lab Jc .call).J σC c ∧ (Alloc.N lab ms q .e).J (enter (-48) σC) c ∧
    CKept R (-48) (-160) 0 mC m

/-- **`wc_rodata`'s states up to the allocator's return inside `W`**, none
moved by `K`: its prologue's, the entry block's, and the allocator's in its
region (for every call with its premises returning to `.sp0`, the caller's cells outside it
holding values, in the call's context `RdCtx` at the call node's invariant
`Jc`, the source possibly advanced from `J0` in the entry block). -/
structure RdPreW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (J0 Jc : AS → Ctl → Prop) : Prop where
  pro : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_rodata") 48 8
    ".L18_wc_rodata.stack_grow" [] J0
  e : BlkW W K exe endPc R F (rN (_root_.Executable.labels exe).label J0 .e) rdE
  alloc : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label →
    q.ra = ((_root_.Executable.labels exe).label ".L18_wc_rodata.sp0").toBitVec →
    AllocW ms q W K exe endPc (aR R)
      (fun m => F m ∧ CallerCells R (-48) (-160) 0 m ∧ RdCtx ms (_root_.Executable.labels exe).label R Jc q m)

/-- `wc_rodata` up to the allocator's return is inside the trivial
predicate, with no outside moves. -/
theorem RdPreW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {J0 Jc : AS → Ctl → Prop} :
    RdPreW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 Jc :=
  ⟨ProW.triv, BlkW.triv, fun q _ _ => Alloc.AllocW.triv ms q⟩

section RdFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_rodata` up to the allocator's return is one segment inside `W`**
in any valid layout of `hello1Prog`: from its entry (invariant `J0`, `sp`
at the region's base, the limit word's facts for its frame of 48, `hlim`)
to the allocator's return at `.sp0` or its heap abort. The source at the
entry is at a buffer allocation the allocator's premises hold for, with
header `257`, two elements of three units (`hq`); the counter and the
headers it may store are unmapped in private memory under `F`
(`hmem`); an allocation of a fresh label lands in `ms.xa` (`hxa`, for every frame
condition the call hands the allocator: with its states, the caller's at
the call and its cells outside the allocator's region, as `at_leave`
needs). Its states lie in `W`, none moved by `K` (`hW`).
VACUOUS at the entry at `rodata`'s source (`hq` at `rdC0`): see A64Hello1RodataSetupG (`rdC0_not_call`). -/
theorem hello1_rodata_pre_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi)
    {J0 : AS → Ctl → Prop} (hW : RdPreW W K exe endPc R F ms J0 J0)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (48 : Int64).toBitVec))
    (hq : ∀ σ c, J0 σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ms = 3#64)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧ (rN (_root_.Executable.labels exe).label J0 .call).J σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧ CKept R (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR R) F' (Ea ms q.1 l b w) s c → ms.xa l b w s c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_rodata", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (rX ms (_root_.Executable.labels exe).label lbl J0 y) s c) := by
  have hin := hello1_rdEIn
  simp only [rdEIn, Bool.and_eq_true] at hin
  obtain ⟨h0, hgap⟩ := hin
  have e4 := label_labelGap hp hgap
  let lab := (_root_.Executable.labels exe).label
  have e4' : lab ".L18_wc_rodata.sp0" = lab ".L18_wc_rodata.0_entry" + Int64.ofNat (4 * 4) := e4
  refine SegW.seq (hello1_rodata_prologue_segW hp hend (nb := rN lab J0 .e)
    hF hR hal (by omega) hhi rfl (by show SO.le ⟨-48, []⟩ (oFr 48) = true; decide) hW.pro ?_)
    (fn_segW (N := rN lab J0) (E := rX ms lab lbl J0) (fun i => ?_) RN.e)
  · intro σ c hJ
    have hl := hlim σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs]
  cases i
  case e =>
    refine seg_ndW (by simp [rdE]) rdE_ok hF hR hal hlo hhi (code_of hp hend h0 (ofNat4_zero _)) hW.e
      fun σ c hJ => ⟨c, .refl c, .inl ⟨RN.call, ?_, ?_, ?_⟩⟩
    · simp only [rN]; rw [rdE_run]
    · simp only [rN]; rw [rdE_run]; rfl
    · simp only [rN] at hJ ⊢
      rw [rdE_run]
      refine ⟨?_, rfl, rfl, rfl, ?_⟩
      · obtain ⟨σe, hJe, h16, h8⟩ := hJ
        exact ⟨σe, hJe, h16, h8⟩
      · rw [e4']
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
          (allocW_mono (hW.alloc g.1 g.2 hra) fun m h =>
            ⟨hFF m h, hcc m h, hkeep m h⟩)).mono_post
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
        · rw [hsl (-16) ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, rN]; omega), h16]
        · rw [hsl (-8) ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, rN]; omega), h8]
        · simp only [Alloc.E] at hx ⊢
          rw [hreg]; exact hx
      · obtain ⟨h2, hfull⟩ := hx
        refine .inr ⟨RX.abort, rfl, rfl, ?_, g, hfull, σe, hc ▸ hJe⟩
        show σR.regs.X0 = 2
        rw [hreg]; exact h2

end RdFn

/-! ## `wc_rodata` from the allocator's return -/

/-- `.sp0`'s first block: the buffer's base saved, reloaded. -/
def rpB0 : List Directive := parseAArch64("str x0, [sp]
ldr x10, [sp]")

/-- `.sp0`'s second block: the old first word saved, the new one built. -/
def rpB1 : List Directive := parseAArch64("str x9, [sp, #8]
movz x9, #25928
movk x9, #27756, lsl #16
movk x9, #11375, lsl #32
movk x9, #30496, lsl #48
ldr x10, [sp]")

/-- `.sp0`'s third block: the base reloaded. -/
def rpB2 : List Directive := parseAArch64("ldr x10, [sp]")

/-- `.sp0`'s fourth block: the old second word saved, the new one built. -/
def rpB3 : List Directive := parseAArch64("str x9, [sp, #16]
movz x9, #29295
movk x9, #25708, lsl #16
movk x9, #10, lsl #32
ldr x10, [sp]")

/-- `.sp0`'s last block: the results, the epilogue, `ret`. -/
def rpB4 : List Directive := parseAArch64("ldr x0, [sp]
movz x1, #0
movz x2, #2
movz x3, #13
ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")

block_spec rpB0 (-48) 0 (⟨-48, []⟩ : SO) rpB0
block_spec rpB1 (-48) 0 (⟨-48, []⟩ : SO) rpB1
block_spec rpB2 (-48) 0 (⟨-48, []⟩ : SO) rpB2
block_spec rpB3 (-48) 0 (⟨-48, []⟩ : SO) rpB3
block_spec rpB4 (-48) 0 (⟨-48, []⟩ : SO) rpB4

/-- **`.sp0` in `prog`**: its blocks and the two exchanges' loads and
stores at their offsets. -/
def rpIn (prog : List Directive) : Bool :=
  blockAt prog ".L18_wc_rodata.sp0" 0 rpB0 && blockAt prog ".L18_wc_rodata.sp0" 2 [ldrDir .X9 .X10 0] &&
  blockAt prog ".L18_wc_rodata.sp0" 3 rpB1 && blockAt prog ".L18_wc_rodata.sp0" 9 [strDir .X9 .X10 0] &&
  blockAt prog ".L18_wc_rodata.sp0" 10 rpB2 && blockAt prog ".L18_wc_rodata.sp0" 11 [ldrDir .X9 .X10 8] &&
  blockAt prog ".L18_wc_rodata.sp0" 12 rpB3 && blockAt prog ".L18_wc_rodata.sp0" 17 [strDir .X9 .X10 8] &&
  blockAt prog ".L18_wc_rodata.sp0" 18 rpB4

theorem hello1_rpIn : rpIn SccCode.hello1Prog = true := by decide +kernel

/-- The first word stored (`"Hello, w"`). -/
abbrev rpK1 : BitVec 64 := 0x77202c6f6c6c6548#64
/-- The second word stored (`"orld\n"`). -/
abbrev rpK2 : BitVec 64 := 0xa646c726f#64

/-- The frame's cells from `.sp0`'s state `σ0`: the base saved, the frame
record kept. -/
def rdFr (σ0 σ : AS) : Prop :=
  σ.slot (-48) = σ0.regs.X0.toBitVec ∧ σ.slot (-16) = σ0.slot (-16) ∧ σ.slot (-8) = σ0.slot (-8)

/-- `.sp0`'s nodes. -/
inductive PN where
  | s0 | l1 | s1 | x1 | s2 | l2 | s3 | x2 | s4

/-- **`.sp0`'s nodes**, from the invariant `Jp` at `.sp0` and the source's
invariants `J1` … `J4` after each exchange's load and store (of `.sp0`'s
state and the control). -/
def pN (lab : Label → Int64) (Jp J1 J2 J3 J4 : AS → Ctl → Prop) : PN → ND
  | .s0 => ⟨lab ".L18_wc_rodata.sp0", ⟨-48, []⟩, Jp⟩
  | .l1 => ⟨lab ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 2), ⟨-48, []⟩, fun σ c => ∃ σ0, Jp σ0 c ∧
      rdFr σ0 σ ∧ σ.regs.X10 = σ0.regs.X0⟩
  | .s1 => ⟨lab ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 3), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J1 σ0 c ∧ rdFr σ0 σ⟩
  | .x1 => ⟨lab ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 9), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J1 σ0 c ∧ rdFr σ0 σ ∧ σ.regs.X9.toBitVec = rpK1 ∧ σ.regs.X10 = σ0.regs.X0⟩
  | .s2 => ⟨lab ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 10), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J2 σ0 c ∧ rdFr σ0 σ⟩
  | .l2 => ⟨lab ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 11), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J2 σ0 c ∧ rdFr σ0 σ ∧ σ.regs.X10 = σ0.regs.X0⟩
  | .s3 => ⟨lab ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 12), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J3 σ0 c ∧ rdFr σ0 σ⟩
  | .x2 => ⟨lab ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 17), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J3 σ0 c ∧ rdFr σ0 σ ∧ σ.regs.X9.toBitVec = rpK2 ∧ σ.regs.X10 = σ0.regs.X0⟩
  | .s4 => ⟨lab ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 18), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J4 σ0 c ∧ rdFr σ0 σ⟩

/-- **`wc_rodata`'s states from the allocator's return inside `W`**, none
moved by `K`: one obligation per node. -/
structure RdPostW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (Jp J1 J2 J3 J4 : AS → Ctl → Prop) : Prop where
  s0 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .s0) rpB0
  l1 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .l1)
  s1 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .s1) rpB1
  x1 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .x1)
  s2 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .s2) rpB2
  l2 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .l2)
  s3 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .s3) rpB3
  x2 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .x2)
  s4 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .s4) rpB4

/-- `wc_rodata` from the allocator's return is inside the trivial
predicate, with no outside moves. -/
theorem RdPostW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {Jp J1 J2 J3 J4 : AS → Ctl → Prop} :
    RdPostW (fun _ _ => True) (fun _ _ => False) exe endPc R F Jp J1 J2 J3 J4 :=
  ⟨BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv⟩

/-- An access's address `[x10, #i]` with `x10` the base `.sp0` started with. -/
theorem rAddr_x10_x0 {r r0 : Reg64s} (h : r.X10 = r0.X0) (i : Int64) : rAddr r .X10 i = rAddr r0 .X0 i := by
  simp [rAddr, Reg64s.getXReg, h]

section RpFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_rodata` from the allocator's return is one segment inside `W`**
in any valid layout of `hello1Prog`: from `.sp0` (invariant `Jp` of the
state `σ0` there, `sp` at `-48`) to the caller's node `x` (pc the saved
return address, `hra`; offsets `⟨0, []⟩`). The two words at the buffer's
base `x0` and `x0 + 8` are unmapped in private memory under `F`
(`hmem`). The source runs
the two exchanges: at each load the source is at an exchange site of the
word (`h1`, `h3`) and at each store it holds it and stores the built word
(`rpK1`, `rpK2`; `h2`, `h4`), its invariants `J1` … `J4` of `σ0` and the
control in between; at the return, `x`'s invariant holds after a local
run of every state with `x0` the base, `x1 = 0`, `x2 = 2`, `x3 = 13` and
`x29`/`x30` the saved record (`hedge`). Its states lie in `W`, none moved
by `K` (`hW`).
VACUOUS at .sp0 at `rodata`'s source: see A64Hello1RodataSetupG (`hand_sp0_empty`). -/
theorem hello1_rodata_post_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    {Jp J1 J2 J3 J4 : AS → Ctl → Prop} {x : ND} (ho : x.o = ⟨0, []⟩)
    (hW : RdPostW W K exe endPc R F Jp J1 J2 J3 J4)
    (hra : ∀ σ0 c, Jp σ0 c → x.pc = Int64.ofBitVec (σ0.slot (-8)))
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, F m → Mem.loadInt m.dmem (rAddr σ0.regs .X0 i) 8 = none)
    (h1 : ∀ σ0 c, Jp σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((rAddr σ0.regs .X0 0).toNat, w') })
    (h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (h3 : ∀ σ0 c, J2 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((rAddr σ0.regs .X0 8).toNat, w') })
    (h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hedge : ∀ σ0 c, J4 σ0 c → ∀ σ' : AS, σ'.regs.X0.toBitVec = σ0.regs.X0.toBitVec →
      σ'.regs.X1.toBitVec = 0#64 → σ'.regs.X2.toBitVec = 2#64 → σ'.regs.X3.toBitVec = 13#64 →
      σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
      ∃ c', LocalRun p c c' ∧ x.J σ' c') :
    SegW W K p lbl ms (At exe endPc R F (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .s0))
      (At exe endPc R F x) := by
  have hin := hello1_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  refine (fn_segW (N := pN lab Jp J1 J2 J3 J4) (E := fun _ : Unit => x) (fun i => ?_) PN.s0).mono_post
    fun _ _ ⟨_, h⟩ => h
  cases i
  case s0 =>
    refine seg_ndW (by simp [rpB0]) rpB0_ok hF hR hal hlo hhi (code_of hp hend c0 (ofNat4_zero _)) hW.s0
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.l1, ?_, ?_, σ, hJ, ?_⟩⟩
    · simp only [pN]; rw [rpB0_run]; simp only [Int64.add_assoc]; rfl
    · simp only [pN]; rw [rpB0_run]; rfl
    · simp only [pN]; rw [rpB0_run]
      exact ⟨⟨by simp [Spike.Lib.upd_apply], by simp [Spike.Lib.upd_apply], by simp [Spike.Lib.upd_apply]⟩, rfl⟩
  case l1 =>
    refine holdLd_ndW (t := .X9) (b := .X10) (i := 0) hF (code_of hp hend c1 rfl) hW.l1
      fun m σ c hA hD ⟨σ0, hJ, hfr, h10⟩ => ?_
    have hr := rAddr_x10_x0 h10 0
    have hm := hmem σ0 c hJ 0 (.inl rfl)
    obtain ⟨x, sa, u, v, e, hx, hv, hh, hk⟩ := h1 σ0 c hJ
    refine ⟨hr ▸ hm m hD, x, sa, u, v, e, hx, hr ▸ hv, hh, fun r w' hrd hrep =>
      .inl ⟨PN.s1, ?_, rfl, σ0, ⟨c, hJ⟩, hr ▸ hk r w' hrd hrep, hfr⟩⟩
    simp only [pN]; rw [Int64.add_assoc]; rfl
  case s1 =>
    refine seg_ndW (by simp [rpB1]) rpB1_ok hF hR hal hlo hhi (code_of hp hend c2 rfl) hW.s1
      fun σ c ⟨σ0, hJp, hJ, hfr⟩ => ⟨c, .refl c, .inl ⟨PN.x1, ?_, ?_, σ0, hJp, hJ, ?_⟩⟩
    · simp only [pN]; rw [rpB1_run]; simp only [Int64.add_assoc]; rfl
    · simp only [pN]; rw [rpB1_run]; rfl
    · simp only [pN]; rw [rpB1_run]
      refine ⟨⟨?_, ?_, ?_⟩, rfl, ?_⟩
      · simp only [Spike.Lib.upd_apply]; exact hfr.1
      · simp only [Spike.Lib.upd_apply]; exact hfr.2.1
      · simp only [Spike.Lib.upd_apply]; exact hfr.2.2
      · rw [hfr.1]
  case x1 =>
    refine xchgSt_ndW (t := .X9) (b := .X10) (i := 0) (code_of hp hend c3 rfl) hW.x1
      fun m σ c hA hD ⟨σ0, ⟨c0', hJp⟩, hJ, hfr, h9, h10⟩ => ?_
    have hr := rAddr_x10_x0 h10 0
    have hm := hmem σ0 c0' hJp 0 (.inl rfl)
    obtain ⟨x, sa, u, v, e, tv, wv, wold, hx, hv, hh, hev, hV, hk⟩ := h2 σ0 c hJ
    refine ⟨hr ▸ hm m hD, x, sa, u, v, e, tv, wv, wold, hx, hr ▸ hv, hr ▸ hh, hev,
      by rw [Ret0.getRegOrZr_x9, h9]; exact hV, .inl ⟨PN.s2, ?_, rfl, σ0, ⟨c0', hJp⟩, hk, hfr⟩⟩
    simp only [pN]; rw [Int64.add_assoc]; rfl
  case s2 =>
    refine seg_ndW (by simp [rpB2]) rpB2_ok hF hR hal hlo hhi (code_of hp hend c4 rfl) hW.s2
      fun σ c ⟨σ0, hJp, hJ, hfr⟩ => ⟨c, .refl c, .inl ⟨PN.l2, ?_, ?_, σ0, hJp, hJ, ?_⟩⟩
    · simp only [pN]; rw [rpB2_run]; simp only [Int64.add_assoc]; rfl
    · simp only [pN]; rw [rpB2_run]; rfl
    · simp only [pN]; rw [rpB2_run]
      refine ⟨hfr, ?_⟩
      rw [hfr.1]
  case l2 =>
    refine holdLd_ndW (t := .X9) (b := .X10) (i := 8) hF (code_of hp hend c5 rfl) hW.l2
      fun m σ c hA hD ⟨σ0, ⟨c0', hJp⟩, hJ, hfr, h10⟩ => ?_
    have hr := rAddr_x10_x0 h10 8
    have hm := hmem σ0 c0' hJp 8 (.inr rfl)
    obtain ⟨x, sa, u, v, e, hx, hv, hh, hk⟩ := h3 σ0 c hJ
    refine ⟨hr ▸ hm m hD, x, sa, u, v, e, hx, hr ▸ hv, hh, fun r w' hrd hrep =>
      .inl ⟨PN.s3, ?_, rfl, σ0, ⟨c0', hJp⟩, hr ▸ hk r w' hrd hrep, hfr⟩⟩
    simp only [pN]; rw [Int64.add_assoc]; rfl
  case s3 =>
    refine seg_ndW (by simp [rpB3]) rpB3_ok hF hR hal hlo hhi (code_of hp hend c6 rfl) hW.s3
      fun σ c ⟨σ0, hJp, hJ, hfr⟩ => ⟨c, .refl c, .inl ⟨PN.x2, ?_, ?_, σ0, hJp, hJ, ?_⟩⟩
    · simp only [pN]; rw [rpB3_run]; simp only [Int64.add_assoc]; rfl
    · simp only [pN]; rw [rpB3_run]; rfl
    · simp only [pN]; rw [rpB3_run]
      refine ⟨⟨?_, ?_, ?_⟩, rfl, ?_⟩
      · simp only [Spike.Lib.upd_apply]; exact hfr.1
      · simp only [Spike.Lib.upd_apply]; exact hfr.2.1
      · simp only [Spike.Lib.upd_apply]; exact hfr.2.2
      · rw [hfr.1]
  case x2 =>
    refine xchgSt_ndW (t := .X9) (b := .X10) (i := 8) (code_of hp hend c7 rfl) hW.x2
      fun m σ c hA hD ⟨σ0, ⟨c0', hJp⟩, hJ, hfr, h9, h10⟩ => ?_
    have hr := rAddr_x10_x0 h10 8
    have hm := hmem σ0 c0' hJp 8 (.inr rfl)
    obtain ⟨x, sa, u, v, e, tv, wv, wold, hx, hv, hh, hev, hV, hk⟩ := h4 σ0 c hJ
    refine ⟨hr ▸ hm m hD, x, sa, u, v, e, tv, wv, wold, hx, hr ▸ hv, hr ▸ hh, hev,
      by rw [Ret0.getRegOrZr_x9, h9]; exact hV, .inl ⟨PN.s4, ?_, rfl, σ0, ⟨c0', hJp⟩, hk, hfr⟩⟩
    simp only [pN]; rw [Int64.add_assoc]; rfl
  case s4 =>
    refine seg_ndW (by simp [rpB4]) rpB4_ok hF hR hal hlo hhi (code_of hp hend c8 rfl) hW.s4
      fun σ c ⟨σ0, ⟨c0', hJp⟩, hJ, hfr⟩ => ?_
    simp only [pN]
    obtain ⟨c', hr, hx⟩ := hedge σ0 c hJ
      (arun lab rpB4 ⟨lab ".L18_wc_rodata.sp0" + Int64.ofNat (4 * 18), ⟨-48, []⟩, σ⟩).σ
      (by rw [rpB4_run]; exact hfr.1) (by rw [rpB4_run]; rfl) (by rw [rpB4_run]; rfl) (by rw [rpB4_run]; rfl)
      (by rw [rpB4_run]; exact hfr.2.1) (by rw [rpB4_run]; exact hfr.2.2)
    refine ⟨c', hr, .inr ⟨(), ?_, ?_, hx⟩⟩
    · rw [rpB4_run, hra σ0 c0' hJp, hfr.2.2]
    · rw [rpB4_run, ho]; rfl

end RpFn

end Hello1

end Spike.Lib.A64.Flow
