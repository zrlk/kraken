/-
**`hello.w`'s `wc_rodata` on AArch64** (with the C2 target half), inside `W`, in
any valid layout of `helloProg` (`Spike/Lib/A64HelloCode.lean`), from checks decided once on the
program (`decide +kernel`). It is the twin of `Spike/Lib/A64Hello1Rodata.lean`, in the forms with
the source's local runs (`A64Hello1RodataS`, `A64Hello1RodataPostS`), at hello.w's labels
(`.L19_wc_rodata`); hello1's blocks are reused.

hello.w's `wc_rodata` is hello1.w's with one more instruction: a `dmb ishst` after the second
exchange's store. There the source publishes the buffer (`let s = publish b`, a `FenceRun.pub` row;
the source half is `Spike.Lib.HelloRodataSrc.rdC4_fence`).

- `hello_alloc`, `hello_rdPro`, `rdEIn`, `hello_rdEIn`, `rpIn`, `hello_rpIn`: the checks.
- `rN`, `rX`, `RdCtx`, `RdPreW`: the nodes up to the call (the entry block's at `J0`; the call's at
  `J1`, the source advanced in the block), the exits, the allocator's call context, and the
  states inside `W`.
- `hello_rodata_pre_runW`: from `wc_rodata`'s entry to the allocator's return at `.sp0`, or to its
  heap abort.
- `rXF`, `hello_rodata_pre_runWF`: the same at a level-ending call (hello's level 0): the heap abort is the
  only exit, the allocator's return being its allocation (`Flow.seg_alloc_ofW_atNR`).
- `PN`, `pN`, `RdPostW`: `.sp0`'s nodes and their states inside `W`. These are hello1's `pNL`
  nodes plus the fence `.f`, which sits between the second exchange's store and the last block.
- `hello_rodata_post_runW`: from `.sp0` to the caller's node. At the fence the source runs under
  `ms.pub` (`hfen`, the publish row).
-/
import Spike.Lib.A64Hello1RodataPostS
import Spike.Lib.A64WakeWcRes
import Spike.Lib.A64HelloCode
import Spike.Lib.A64HelloAllocEA
import Spike.Lib.A64AllocNR
import Spike.Lib.A64CodeAcross

namespace Spike.Lib.A64.Flow.HelloRd

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk)
open Spike.Lib.A64.Alloc (Call AllocW Ea Jfull)
open Spike.Lib.A64.Flow.Hello1 (rdE rdE_ok rdE_run rdJ AG RN RX aR rdFr rpB0 rpB0_ok rpB0_run rpB1 rpB1_ok
  rpB1_run rpB2 rpB2_ok rpB2_run rpB3 rpB3_ok rpB3_run rpB4 rpB4_ok rpB4_run rpK1 rpK2 rAddr_x10_x0)
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap blockAcross)

set_option linter.unusedSimpArgs false

/-! ## The checks -/

theorem hello_alloc : allocIn SccCode.helloProg = true := by decide +kernel

/-- `wc_rodata`'s prologue: frame 48, nothing spilled. -/
abbrev rdPro : Bool := prologueIn SccCode.helloProg "wc_rodata" ".L19_wc_rodata.stack_check"
  ".L19_wc_rodata.0_entry" 48 8 ".L19_wc_rodata.stack_grow" []

theorem hello_rdPro : rdPro = true := by decide +kernel

/-- **`wc_rodata`'s entry block in `prog`**, with `.sp0` right after the call. -/
def rdEIn (prog : List Directive) : Bool :=
  blockAt prog ".L19_wc_rodata.0_entry" 0 rdE && labelGap prog ".L19_wc_rodata.0_entry" ".L19_wc_rodata.sp0" 4

theorem hello_rdEIn : rdEIn SccCode.helloProg = true := by decide +kernel

/-- **`.sp0` in `prog`**: its blocks, the two exchanges' loads and stores at their offsets, and
the publish fence (`WakeWc.pubF`) before the last block. -/
def rpIn (prog : List Directive) : Bool :=
  blockAt prog ".L19_wc_rodata.sp0" 0 rpB0 && blockAt prog ".L19_wc_rodata.sp0" 2 [ldrDir .X9 .X10 0] &&
  blockAt prog ".L19_wc_rodata.sp0" 3 rpB1 && blockAt prog ".L19_wc_rodata.sp0" 9 [strDir .X9 .X10 0] &&
  blockAt prog ".L19_wc_rodata.sp0" 10 rpB2 && blockAt prog ".L19_wc_rodata.sp0" 11 [ldrDir .X9 .X10 8] &&
  blockAt prog ".L19_wc_rodata.sp0" 12 rpB3 && blockAt prog ".L19_wc_rodata.sp0" 17 [strDir .X9 .X10 8] &&
  blockAt prog ".L19_wc_rodata.sp0" 18 WakeWc.pubF &&
  blockAcross prog ".L19_wc_rodata.sp0" 19 (rpB4.take 7) ".L19_wc_rodata.x6" (rpB4.drop 7)

theorem hello_rpIn : rpIn SccCode.helloProg = true := by decide +kernel

/-! ## `wc_rodata` up to the allocator's return -/

section Rd

variable (ms : MemSide isaLSE2) (lab : Label → Int64) (lbl : WeakMem.AllocLabel → Option Nat)
  (J0 J1 : AS → Ctl → Prop)

/-- **The nodes**: `.0_entry` (at the entry's invariant `J0`) and the allocator's entry with its
arguments (at `J1`, the source advanced in the block). -/
def rN : RN → ND
  | .e => ⟨lab ".L19_wc_rodata.0_entry", ⟨-48, []⟩, rdJ J0⟩
  | .call => ⟨lab "scc_rt_alloc", ⟨-48, []⟩, fun σ c => rdJ J1 σ c ∧ σ.regs.X0.toBitVec = 257#64 ∧
      σ.regs.X1.toBitVec = 2#64 ∧ σ.regs.X2.toBitVec = 3#64 ∧
      σ.regs.X30.toBitVec = (lab ".L19_wc_rodata.sp0").toBitVec⟩

/-- **The exits**: the allocator's return at `.sp0` (its return's facts, with the frame record
kept), and its heap abort. -/
def rX : RX → ND
  | .sp0 => ⟨lab ".L19_wc_rodata.sp0", ⟨-48, []⟩, fun σ c => ∃ q : AG ms lab, rdJ J1 σ q.1.c0 ∧
      (Alloc.E lab ms q.1 lbl .ret).J σ c⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-208, []⟩, fun σ c => σ.regs.X0 = 2 ∧
      σ.regs.X30.toBitVec = (lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec ∧ ∃ q : AG ms lab, Jfull ms q.1 c ∧
      ∃ σe, J1 σe q.1.c0⟩

end Rd

/-- **The allocator's call context in `wc_rodata`'s region `R`** at the memory `m`
(`Hello1.RdCtx` at hello's call node). -/
def RdCtx (ms : MemSide isaLSE2) (lab : Label → Int64) (R : Region) (J0 J1 : AS → Ctl → Prop) (q : Call)
    (m : MachineData) : Prop :=
  ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧ (rN lab J0 J1 .call).J σC c ∧ (Alloc.N lab ms q .e).J (enter (-48) σC) c ∧
    CKept R (-48) (-160) 0 mC m

/-- **`wc_rodata`'s states up to the allocator's return inside `W`**, none moved by `K`: the
prologue's, the entry block's, and the allocator's in its region (`Hello1.RdPreW` at hello's
labels). -/
structure RdPreW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (J0 J1 : AS → Ctl → Prop) : Prop where
  pro : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_rodata") 48 8
    ".L19_wc_rodata.stack_grow" [] J0
  e : BlkW W K exe endPc R F (rN (_root_.Executable.labels exe).label J0 J1 .e) rdE
  alloc : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label →
    q.ra = ((_root_.Executable.labels exe).label ".L19_wc_rodata.sp0").toBitVec →
    AllocW ms q W K exe endPc (aR R)
      (fun m => F m ∧ CallerCells R (-48) (-160) 0 m ∧ RdCtx ms (_root_.Executable.labels exe).label R J0 J1 q m)

/-- `wc_rodata` up to the allocator's return is inside the trivial predicate, with no outside
moves. -/
theorem RdPreW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {J0 J1 : AS → Ctl → Prop} :
    RdPreW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 J1 :=
  ⟨ProW.triv, BlkW.triv, fun q _ _ => Alloc.AllocW.triv ms q⟩

section RdFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_rodata` up to the allocator's return is one segment inside `W`** in any valid layout of
`helloProg` (`Hello1.hello1_rodata_pre_runW` at hello's labels). It runs from the entry (invariant
`J0`, `sp` at the region's base, the limit word's facts for its frame of 48, `hlim`) to the
allocator's return at `.sp0`, or to its heap abort.
- The entry block takes a local run from each of `J0`'s controls to one of `J1` at the same state
  (`hloc`).
- At `J1` the source is at a buffer allocation the allocator's premises hold for: header `257`,
  two elements of three units (`hq`).
- The counter and the headers the allocator may store are unmapped in private memory under `F`
  (`hmem`).
- An allocation of a fresh label lands in `ms.xa` (`hxa`, for every frame condition the call hands
  the allocator).
- Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello_rodata_pre_runW {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
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
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧ (rN (_root_.Executable.labels exe).label J0 J1 .call).J σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧ CKept R (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR R) F' (Ea ms q.1 l b w) s c → ms.xa l b w s c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_rodata", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (rX ms (_root_.Executable.labels exe).label lbl J1 y) s c) := by
  have hin := hello_rdEIn
  simp only [rdEIn, Bool.and_eq_true] at hin
  obtain ⟨h0, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e4 : lab ".L19_wc_rodata.sp0" = lab ".L19_wc_rodata.0_entry" + Int64.ofNat (4 * 4) := label_labelGap hp hgap
  refine SegW.seq (prologue_seg_ofW hp hend hello_rdPro (nb := rN lab J0 J1 .e) (by decide) (by decide) hF hR hal
    (by show R.lo ≤ -48; omega) hhi (by decide) rfl (by show SO.le ⟨-48, []⟩ (oFr 48) = true; decide) hW.pro ?_)
    (fn_segW (N := rN lab J0 J1) (E := rX ms lab lbl J1) (fun i => ?_) RN.e)
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
    · simp only [rN]; rw [rdE_run]
    · simp only [rN]; rw [rdE_run]; rfl
    · simp only [rN]
      rw [rdE_run]
      refine ⟨⟨σe, hJ1, h16, h8⟩, rfl, rfl, rfl, ?_⟩
      rw [e4]
      show BitVec.ofInt 64 _ = _
      rw [Ret0.ofInt_bmod]
      simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
      rfl
  case call =>
    refine call_nd_FWK (KC := False) (lo' := -160) (hi' := 0) (M := fun _ => True)
      (Ne := fun g : AG ms lab => Alloc.N lab ms g.1 .e) (Ex := fun g : AG ms lab => Alloc.EX30 lab ms g.1 lbl)
      hR hal hF (by show R.lo ≤ -48 + -160; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
      (by show (-48 : Int) % 16 = 0; decide) (by decide) (by decide) (fun h => h.elim) (fun h => h.elim)
      (fun _ h _ => h)
      (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, -, -, h30⟩, ⟨-, -, h30', -⟩⟩ := hg
        have hra : g.1.ra = (lab ".L19_wc_rodata.sp0").toBitVec := by
          rw [← h30']; exact h30
        exact (seg_alloc_ofW_atA hp hend hello_alloc hF' hR' hal' hlo' hhi' g.2
          (fun a ha m hm => hmem g.1 g.2 a ha m (hFF m hm))
          (hxa g F' hFF hkeep)
          (allocW_mono (hW.alloc g.1 g.2 hra) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩) .e).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨σe, hJe, -, -⟩, h0, h1, h2, -⟩
      obtain ⟨q, hok, hc, hh, hk, hu⟩ := hq σe c hJe
      exact ⟨⟨{ q with x29 := σC.regs.X29.toBitVec, ra := σC.regs.X30.toBitVec }, { hok with }⟩, rfl,
        hc.symm, rfl, rfl, h0.trans hh.symm, h1.trans hk.symm, h2.trans hu.symm⟩
    · rintro g y σC c σx c' σR ⟨⟨σe, hJe, h16, h8⟩, -, -, -, h30⟩ ⟨hc, -, h30', -⟩ hx hreg - hsl
      cases y
      · refine .inr ⟨RX.sp0, ?_, rfl, g, ⟨σe, hc ▸ hJe, ?_, ?_⟩, ?_⟩
        · show lab ".L19_wc_rodata.sp0" = Int64.ofBitVec g.1.ra
          rw [← h30']
          show _ = Int64.ofBitVec σC.regs.X30.toBitVec
          rw [h30, int64_ofBitVec_toBitVec]
        · rw [hsl (-16) ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, rN]; omega), h16]
        · rw [hsl (-8) ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, rN]; omega), h8]
        · simp only [Alloc.E] at hx ⊢
          rw [hreg]; exact hx
      · obtain ⟨h2, h30a, hfull⟩ := hx
        refine .inr ⟨RX.abort, rfl, rfl, ?_, ?_, g, hfull, σe, hc ▸ hJe⟩
        · show σR.regs.X0 = 2
          rw [hreg]; exact h2
        · show σR.regs.X30.toBitVec = _
          rw [hreg]; exact h30a

end RdFn

/-- **The exits at a level-ending call**: `rX`'s, with no state at `.sp0` (the allocator's return is its
allocation, landing in `ms.xa`: `Alloc.ENR`). -/
def rXF (ms : MemSide isaLSE2) (lab : Label → Int64) (lbl : WeakMem.AllocLabel → Option Nat)
    (J1 : AS → Ctl → Prop) : RX → ND
  | .sp0 => ⟨lab ".L19_wc_rodata.sp0", ⟨-48, []⟩, fun _ _ => False⟩
  | .abort => rX ms lab lbl J1 .abort

section RdFnF

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_rodata` up to the allocator's call is one segment inside `W` whose only exit is the heap abort**
(`hello_rodata_pre_runW`'s twin at a level-ending allocation, hello's level 0): the same premises; the
allocator runs as `Flow.seg_alloc_ofW_atNR`, whose return is its allocation (landing in `ms.xa`, `hxa`), so
no state reaches `.sp0`. -/
theorem hello_rodata_pre_runWF {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
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
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧ (rN (_root_.Executable.labels exe).label J0 J1 .call).J σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧ CKept R (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR R) F' (Ea ms q.1 l b w) s c → ms.xa l b w s c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_rodata", ⟨0, []⟩, J0⟩)
      (At exe endPc R F (rX ms (_root_.Executable.labels exe).label lbl J1 .abort)) := by
  have hin := hello_rdEIn
  simp only [rdEIn, Bool.and_eq_true] at hin
  obtain ⟨h0, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e4 : lab ".L19_wc_rodata.sp0" = lab ".L19_wc_rodata.0_entry" + Int64.ofNat (4 * 4) := label_labelGap hp hgap
  refine (SegW.seq (prologue_seg_ofW hp hend hello_rdPro (nb := rN lab J0 J1 .e) (by decide) (by decide) hF hR hal
    (by show R.lo ≤ -48; omega) hhi (by decide) rfl (by show SO.le ⟨-48, []⟩ (oFr 48) = true; decide) hW.pro ?_)
    (fn_segW (N := rN lab J0 J1) (E := rXF ms lab lbl J1) (fun i => ?_) RN.e)).mono_post ?_
  · intro σ c hJ
    have hl := hlim σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs]
  · cases i
    case e =>
      refine seg_ndW (by simp [rdE]) rdE_ok hF hR hal hlo hhi (code_of hp hend h0 (ofNat4_zero _)) hW.e
        fun σ c hJ => ?_
      obtain ⟨σe, hJe, h16, h8⟩ := hJ
      obtain ⟨c', hr, hJ1⟩ := hloc σe c hJe
      refine ⟨c', hr, .inl ⟨RN.call, ?_, ?_, ?_⟩⟩
      · simp only [rN]; rw [rdE_run]
      · simp only [rN]; rw [rdE_run]; rfl
      · simp only [rN]
        rw [rdE_run]
        refine ⟨⟨σe, hJ1, h16, h8⟩, rfl, rfl, rfl, ?_⟩
        rw [e4]
        show BitVec.ofInt 64 _ = _
        rw [Ret0.ofInt_bmod]
        simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
        rfl
    case call =>
      refine call_nd_FWK (KC := False) (lo' := -160) (hi' := 0) (M := fun _ => True)
        (Ne := fun g : AG ms lab => Alloc.N lab ms g.1 .e) (Ex := fun g : AG ms lab => Alloc.ENR lab ms g.1 lbl)
        hR hal hF (by show R.lo ≤ -48 + -160; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
        (by show (-48 : Int) % 16 = 0; decide) (by decide) (by decide) (fun h => h.elim) (fun h => h.elim)
        (fun _ h _ => h)
        (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
          subst hR'e
          obtain ⟨σC, c, ⟨-, -, -, -, h30⟩, ⟨-, -, h30', -⟩⟩ := hg
          have hra : g.1.ra = (lab ".L19_wc_rodata.sp0").toBitVec := by
            rw [← h30']; exact h30
          exact (seg_alloc_ofW_atNR hp hend hello_alloc hF' hR' hal' hlo' hhi' g.2
            (fun a ha m hm => hmem g.1 g.2 a ha m (hFF m hm))
            (hxa g F' hFF hkeep)
            (allocW_mono (hW.alloc g.1 g.2 hra) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩) .e).mono_post
            fun _ _ h => ⟨.abort, h, trivial⟩)
        (fun _ => rfl) ?_ ?_
      · rintro σC c ⟨⟨σe, hJe, -, -⟩, h0, h1, h2, -⟩
        obtain ⟨q, hok, hc, hh, hk, hu⟩ := hq σe c hJe
        exact ⟨⟨{ q with x29 := σC.regs.X29.toBitVec, ra := σC.regs.X30.toBitVec }, { hok with }⟩, rfl,
          hc.symm, rfl, rfl, h0.trans hh.symm, h1.trans hk.symm, h2.trans hu.symm⟩
      · rintro g y σC c σx c' σR ⟨⟨σe, hJe, -, -⟩, -, -, -, -⟩ ⟨hc, -, -, -⟩ hx hreg - -
        cases y
        · exact hx.elim
        · obtain ⟨h2, h30a, hfull⟩ := hx
          refine .inr ⟨RX.abort, rfl, rfl, ?_, ?_, g, hfull, σe, hc ▸ hJe⟩
          · show σR.regs.X0 = 2
            rw [hreg]; exact h2
          · show σR.regs.X30.toBitVec = _
            rw [hreg]; exact h30a
  · rintro s c ⟨y, hy⟩
    cases y
    · obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := hy
      exact hJ.elim
    · exact hy

end RdFnF

/-! ## `wc_rodata` from the allocator's return -/

/-- `.sp0`'s nodes: hello1's, plus the publish fence `f`. -/
inductive PN where
  | s0 | l1 | s1 | x1 | s2 | l2 | s3 | x2 | f | s4

/-- **`.sp0`'s nodes**, from these invariants (each of `.sp0`'s state and the control):
- `Jp` at `.sp0`; the source runs locally in the first block to `Jp'` at the first load;
- `J1` after the first load; `J2` after the first store;
- the source runs locally in the third block to `J2'` at the second load;
- `J3` after the second load; `J4` after the second store, at the fence;
- `J5` after the fence's run (`Hello1.pNL` with the fence). -/
def pN (lab : Label → Int64) (Jp Jp' J1 J2 J2' J3 J4 J5 : AS → Ctl → Prop) : PN → ND
  | .s0 => ⟨lab ".L19_wc_rodata.sp0", ⟨-48, []⟩, Jp⟩
  | .l1 => ⟨lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 2), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      Jp' σ0 c ∧ rdFr σ0 σ ∧ σ.regs.X10 = σ0.regs.X0⟩
  | .s1 => ⟨lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 3), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J1 σ0 c ∧ rdFr σ0 σ⟩
  | .x1 => ⟨lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 9), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J1 σ0 c ∧ rdFr σ0 σ ∧ σ.regs.X9.toBitVec = rpK1 ∧ σ.regs.X10 = σ0.regs.X0⟩
  | .s2 => ⟨lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 10), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J2 σ0 c ∧ rdFr σ0 σ⟩
  | .l2 => ⟨lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 11), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J2' σ0 c ∧ rdFr σ0 σ ∧ σ.regs.X10 = σ0.regs.X0⟩
  | .s3 => ⟨lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 12), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J3 σ0 c ∧ rdFr σ0 σ⟩
  | .x2 => ⟨lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 17), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J3 σ0 c ∧ rdFr σ0 σ ∧ σ.regs.X9.toBitVec = rpK2 ∧ σ.regs.X10 = σ0.regs.X0⟩
  | .f => ⟨lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 18), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J4 σ0 c ∧ rdFr σ0 σ⟩
  | .s4 => ⟨lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 19), ⟨-48, []⟩, fun σ c => ∃ σ0, (∃ c0, Jp σ0 c0) ∧
      J5 σ0 c ∧ rdFr σ0 σ⟩

/-- **`wc_rodata`'s states from the allocator's return inside `W`**, none moved by `K`: one
obligation per node. -/
structure RdPostW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (Jp Jp' J1 J2 J2' J3 J4 J5 : AS → Ctl → Prop) : Prop where
  s0 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .s0) rpB0
  l1 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .l1)
  s1 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .s1) rpB1
  x1 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .x1)
  s2 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .s2) rpB2
  l2 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .l2)
  s3 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .s3) rpB3
  x2 : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .x2)
  f : NodeW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .f)
  s4 : BlkW W K exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .s4) rpB4

/-- `wc_rodata` from the allocator's return is inside the trivial predicate, with no outside
moves. -/
theorem RdPostW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {Jp Jp' J1 J2 J2' J3 J4 J5 : AS → Ctl → Prop} :
    RdPostW (fun _ _ => True) (fun _ _ => False) exe endPc R F Jp Jp' J1 J2 J2' J3 J4 J5 :=
  ⟨BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, NodeW.triv,
    BlkW.triv⟩

section RpFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_rodata` from the allocator's return is one segment inside `W`** in any valid layout of
`helloProg`: from `.sp0` (invariant `Jp` of the state `σ0` there, `sp` at `-48`) to the caller's
node `x` (pc the saved return address, `hra`; offsets `⟨0, []⟩`). This is
`Hello1.hello1_rodata_post_runW` at hello's labels, plus the publish fence.
- The buffer's two words at `x0` and `x0 + 8` are unmapped in private memory under `F` (`hmem`).
- The source runs locally in the first and third blocks (`hr0`, `hr2`), then the two exchanges
  (`h1` … `h4`, as in hello1).
- At the `dmb ishst` the source takes its run under `ms.pub` (`hfen`): `publish b`, then a local
  run.
- At the return, `x`'s invariant holds after a local run of every state with `x0` the base,
  `x1 = 0`, `x2 = 2`, `x3 = 13`, and `x29`/`x30` the saved record (`hedge`).
- Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello_rodata_post_runW {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    {Jp Jp' J1 J2 J2' J3 J4 J5 : AS → Ctl → Prop} {x : ND} (ho : x.o = ⟨0, []⟩)
    (hW : RdPostW W K exe endPc R F Jp Jp' J1 J2 J2' J3 J4 J5)
    (hra : ∀ σ0 c, Jp σ0 c → x.pc = Int64.ofBitVec (σ0.slot (-8)))
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, F m → Mem.loadInt m.dmem (rAddr σ0.regs .X0 i) 8 = none)
    (hr0 : ∀ σ0 c, Jp σ0 c → ∃ c', LocalRun p c c' ∧ Jp' σ0 c')
    (h1 : ∀ σ0 c, Jp' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((rAddr σ0.regs .X0 0).toNat, w') })
    (h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hr2 : ∀ σ0 c, J2 σ0 c → ∃ c', LocalRun p c c' ∧ J2' σ0 c')
    (h3 : ∀ σ0 c, J2' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((rAddr σ0.regs .X0 8).toNat, w') })
    (h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hfen : ∀ σ0 c, J4 σ0 c → ∃ c', FenceRun p ms.pub .st c c' ∧ J5 σ0 c')
    (hedge : ∀ σ0 c, J5 σ0 c → ∀ σ' : AS, σ'.regs.X0.toBitVec = σ0.regs.X0.toBitVec →
      σ'.regs.X1.toBitVec = 0#64 → σ'.regs.X2.toBitVec = 2#64 → σ'.regs.X3.toBitVec = 13#64 →
      σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
      ∃ c', LocalRun p c c' ∧ x.J σ' c') :
    SegW W K p lbl ms (At exe endPc R F (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .s0))
      (At exe endPc R F x) := by
  have hin := hello_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, cf⟩, c8⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  refine (fn_segW (N := pN lab Jp Jp' J1 J2 J2' J3 J4 J5) (E := fun _ : Unit => x) (fun i => ?_) PN.s0).mono_post
    fun _ _ ⟨_, h⟩ => h
  cases i
  case s0 =>
    refine seg_ndW (by simp [rpB0]) rpB0_ok hF hR hal hlo hhi (code_of hp hend c0 (ofNat4_zero _)) hW.s0
      fun σ c hJ => ?_
    obtain ⟨c', hr, hJ'⟩ := hr0 σ c hJ
    refine ⟨c', hr, .inl ⟨PN.l1, ?_, ?_, σ, ⟨c, hJ⟩, hJ', ?_⟩⟩
    · simp only [pN]; rw [rpB0_run]; simp only [Int64.add_assoc]; rfl
    · simp only [pN]; rw [rpB0_run]; rfl
    · simp only [pN]; rw [rpB0_run]
      exact ⟨⟨by simp [Spike.Lib.upd_apply], by simp [Spike.Lib.upd_apply], by simp [Spike.Lib.upd_apply]⟩, rfl⟩
  case l1 =>
    refine holdLd_ndW (t := .X9) (b := .X10) (i := 0) hF (code_of hp hend c1 rfl) hW.l1
      fun m σ c hA hD ⟨σ0, ⟨c0', hJp⟩, hJ, hfr, h10⟩ => ?_
    have hr := rAddr_x10_x0 h10 0
    have hm := hmem σ0 c0' hJp 0 (.inl rfl)
    obtain ⟨x, sa, u, v, e, hx, hv, hh, hk⟩ := h1 σ0 c hJ
    refine ⟨hr ▸ hm m hD, x, sa, u, v, e, hx, hr ▸ hv, hh, fun r w' hrd hrep =>
      .inl ⟨PN.s1, ?_, rfl, σ0, ⟨c0', hJp⟩, hr ▸ hk r w' hrd hrep, hfr⟩⟩
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
      fun σ c ⟨σ0, hJp, hJ, hfr⟩ => ?_
    obtain ⟨c', hr, hJ'⟩ := hr2 σ0 c hJ
    refine ⟨c', hr, .inl ⟨PN.l2, ?_, ?_, σ0, hJp, hJ', ?_⟩⟩
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
      by rw [Ret0.getRegOrZr_x9, h9]; exact hV, .inl ⟨PN.f, ?_, rfl, σ0, ⟨c0', hJp⟩, hk, hfr⟩⟩
    simp only [pN]; rw [Int64.add_assoc]; rfl
  case f =>
    -- the publish row: `dmb ishst`, the source's `publish b` (C2's target half)
    refine dmb_ndW (code_of hp hend (WakeWc.pubF_eq ▸ cf) rfl) hW.f fun σ c ⟨σ0, hJp, hJ, hfr⟩ => ?_
    obtain ⟨c', hr, hJ5⟩ := hfen σ0 c hJ
    refine ⟨c', hr, .inl ⟨PN.s4, ?_, rfl, σ0, hJp, hJ5, hfr⟩⟩
    show lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 19) = lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 18) + 4
    rw [Int64.add_assoc]; rfl
  case s4 =>
    refine seg_ndW (by simp [rpB4]) rpB4_ok hF hR hal hlo hhi
      (code_field_blockAcross hp hend c8 (List.take_append_drop _ _) rfl) hW.s4
      fun σ c ⟨σ0, ⟨c0', hJp⟩, hJ, hfr⟩ => ?_
    simp only [pN]
    obtain ⟨c', hr, hx⟩ := hedge σ0 c hJ
      (arun lab rpB4 ⟨lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 19), ⟨-48, []⟩, σ⟩).σ
      (by rw [rpB4_run]; exact hfr.1) (by rw [rpB4_run]; rfl) (by rw [rpB4_run]; rfl) (by rw [rpB4_run]; rfl)
      (by rw [rpB4_run]; exact hfr.2.1) (by rw [rpB4_run]; exact hfr.2.2)
    refine ⟨c', hr, .inr ⟨(), ?_, ?_, hx⟩⟩
    · rw [rpB4_run, hra σ0 c0' hJp, hfr.2.2]
    · rw [rpB4_run, ho]; rfl

end RpFn

end Spike.Lib.A64.Flow.HelloRd

/-- info: 'Spike.Lib.A64.Flow.HelloRd.hello_alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloRd.hello_alloc

/-- info: 'Spike.Lib.A64.Flow.HelloRd.hello_rpIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloRd.hello_rpIn

/--
info: 'Spike.Lib.A64.Flow.HelloRd.hello_rodata_pre_runW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloRd.hello_rodata_pre_runW

/--
info: 'Spike.Lib.A64.Flow.HelloRd.hello_rodata_post_runW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloRd.hello_rodata_post_runW

/--
info: 'Spike.Lib.A64.Flow.HelloRd.hello_rodata_pre_runWF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloRd.hello_rodata_pre_runWF
