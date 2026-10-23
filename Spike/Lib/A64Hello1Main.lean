/-
**`hello1.w`'s `scc_rt_main` on AArch64**, inside `W`, in any valid
layout of `hello1Prog` (`Spike/Lib/A64Hello1Code.lean`), from checks
decided once on the program (`decide +kernel`).

- `hello1_main_pre_segW`: from `scc_rt_main`'s entry (invariant `J`): its
  prologue, `bl wc_rodata`, and `wc_rodata` up to the allocator's return in
  the callee's region at the call (`at_enter`, then
  `hello1_rodata_pre_segW`; `wc_rodata`'s frame and the allocator's below
  `scc_rt_main`'s 80: the region reaches `-288`). Exits: `wc_rodata`'s, in
  its region, for some caller's state at the call.
- `hello1_main_post_segW`: from `wc_rodata`'s `.sp0` after the allocator
  (in `scc_rt_main`'s region at the call): the rest of `wc_rodata`, its
  return, `bl wc_main` (`hello1_wc_segW`), and `scc_rt_main`'s exit, to the
  label after `bl scc_rt_main`. Print's write stays the named `hsvc`; the
  source facts are named premises over the user's invariants.
- `hello1_main_segW`: the two composed, as two segments: from the entry to
  the aborts, and from `.sp0`'s states (the allocation's continuation
  `ms.xa` holds, `hpost`) to `print`'s abort.
- `hello1_main_xa_post`, `hello1_main_hxa_of_post`: the bridge between the
  two, from the allocator's fresh-label landing to `wc_rodata`'s `.sp0` of
  an invariant the landing implies; the choice of `ms.xa` stays the
  instance's.
-/
import Spike.Lib.A64Hello1Rodata

namespace Spike.Lib.A64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk seg_oneW)
open Spike.Lib.A64.Alloc (Call AllocW Ea Jfull)
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)

set_option linter.unusedSimpArgs false

/-! ## `scc_rt_main`'s blocks -/

/-- `scc_rt_main`'s `.0_entry` block: the call of `wc_rodata`. -/
def mB0 : List Directive := parseAArch64("bl wc_rodata")

/-- `scc_rt_main`'s `.sp0` block: `wc_rodata`'s results to the frame and
back, the call of `wc_main`. -/
def mB1 : List Directive := parseAArch64("str x0, [sp, #8]
str x1, [sp, #16]
str x2, [sp, #24]
str x3, [sp, #32]
ldr x0, [sp, #8]
ldr x1, [sp, #16]
ldr x2, [sp, #24]
ldr x3, [sp, #32]
ldr x4, [sp]
bl wc_main")

block_spec mB0 (-80) 0 (⟨-80, []⟩ : SO) mB0
block_spec mB1 (-80) 0 (⟨-80, []⟩ : SO) mB1

/-- **`scc_rt_main`'s blocks in `prog`**, each call's return label right
after it. -/
def mainIn (prog : List Directive) : Bool :=
  blockAt prog ".L1_scc_rt_main.0_entry" 0 mB0 && blockAt prog ".L1_scc_rt_main.sp0" 0 mB1 &&
    labelGap prog ".L1_scc_rt_main.0_entry" ".L1_scc_rt_main.sp0" 1 &&
    labelGap prog ".L1_scc_rt_main.sp0" ".L1_scc_rt_main.sp1" 10

theorem hello1_mainIn : mainIn SccCode.hello1Prog = true := by decide +kernel

/-- **`scc_rt_main`'s frame** as some entry state of `J` left it: the
record, the saved `x0`, `sp` 80 below, the thread pointer. -/
def mJ (J : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ σe, J σe c ∧ σ.slot (-16) = σe.regs.X29.toBitVec ∧ σ.slot (-8) = σe.regs.X30.toBitVec ∧
    σ.slot (-80) = σe.regs.X0.toBitVec ∧ σ.regs.SP.toBitVec = σe.regs.SP.toBitVec - (80 : Int64).toBitVec ∧
    σ.regs.TPIDR_EL0 = σe.regs.TPIDR_EL0

section MainNodes

variable (lab : Label → Int64) (J : AS → Ctl → Prop)

/-- `scc_rt_main`'s `.0_entry`. -/
def mN0 : ND := ⟨lab ".L1_scc_rt_main.0_entry", ⟨-80, []⟩, mJ J⟩

/-- The call of `wc_rodata`: the return address `.sp0`. -/
def mNC : ND := ⟨lab "wc_rodata", ⟨-80, []⟩, fun σ c => mJ J σ c ∧
  σ.regs.X30.toBitVec = (lab ".L1_scc_rt_main.sp0").toBitVec⟩

end MainNodes

/-- `wc_rodata`'s region at the call. -/
abbrev mR (R : Region) : Region := R.callee (-80) (-208) 0

/-- **`wc_rodata`'s frame condition at the call** from the caller's state
`m0`, `σC` (`at_enter`). -/
def mF (R : Region) (F : MachineData → Prop) (m0 : MachineData) (σC : AS) (m : MachineData) : Prop :=
  F m ∧ CKept R (-80) (-208) 0 m0 m ∧ Abs R ⟨-80, []⟩ m0 σC

/-- `wc_rodata`'s entry invariant from the caller's state `σC` at the call
node of invariant `Jc`. -/
def mRdJ0 (Jc : AS → Ctl → Prop) (σC : AS) (σ : AS) (c : Ctl) : Prop := σ = enter (-80) σC ∧ Jc σC c

/-- **`scc_rt_main`'s states up to `wc_rodata`'s allocator's return inside
`W`**, none moved by `K`: its prologue's, the call block's, and
`wc_rodata`'s in its region for every caller's state at the call. -/
structure MainPreW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (J : AS → Ctl → Prop) : Prop where
  pro : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") 80 8
    ".L1_scc_rt_main.stack_grow" [(.X0, 0)] J
  call : BlkW W K exe endPc R F (mN0 (_root_.Executable.labels exe).label J) mB0
  rd : ∀ m0 σC, RdPreW W K exe endPc (mR R) (mF R F m0 σC) ms
    (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC)

/-- `scc_rt_main` up to the allocator's return is inside the trivial
predicate, with no outside moves. -/
theorem MainPreW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {J : AS → Ctl → Prop} :
    MainPreW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J :=
  ⟨ProW.triv, BlkW.triv, fun _ _ => RdPreW.triv⟩

section MainPre

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- `wc_rodata`'s region at the call is a region, 16-aligned, its frame
condition stable. -/
theorem mR_ok (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    (m0 : MachineData) (σC : AS) :
    (mR R).OK ∧ (mR R).base.toNat % 16 = 0 ∧ FStable (mR R) (mF R F m0 σC) := by
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ -80 + -208 by omega) (by decide)
    (show (-80 : Int) < R.hi by omega)
  refine ⟨Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), ?_,
    fstable_enter hR hF (by omega) (by decide) (by omega) (by decide) (by decide) (by decide) (by decide)⟩
  have : (((mR R).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

/-- **`scc_rt_main` up to `wc_rodata`'s allocator's return is one segment
inside `W`** in any valid layout of `hello1Prog`: from its entry
(invariant `J`, `sp` at the region's base) to `wc_rodata`'s exits
(`hello1_rodata_pre_segW`) in its region at the call, for some caller's
state there. The limit word's facts hold for both frames (`hlimM`,
`hlimR`); the source at the entry is at `wc_rodata`'s allocation (`hq`);
`hmem`, `hxa` as for `hello1_rodata_pre_segW`, for every caller's state
at the call. Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_main_pre_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    {J : AS → Ctl → Prop} (hW : MainPreW W K exe endPc R F ms J)
    (hlimM : ∀ σ c, J σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (80 : Int64).toBitVec))
    (hlimR : ∀ σ c, J σ c → LimOk ms F exe endPc (tcbA σ.regs 8)
      (σ.regs.SP.toBitVec - (80 : Int64).toBitVec - (48 : Int64).toBitVec))
    (hq : ∀ σ c, J σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ms = 3#64)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ m0 σC, ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF R F m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
        (rN (_root_.Executable.labels exe).label
          (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) .call).J σ c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR R) (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR (mR R)) F' (Ea ms q.1 l b w) s c → ms.xa l b w s c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (fun s c => ∃ m0 σC y, At exe endPc (mR R) (mF R F m0 σC)
        (rX ms (_root_.Executable.labels exe).label lbl
          (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) y) s c) := by
  have hin := hello1_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨h0, -⟩, hg1⟩, -⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e1 : lab ".L1_scc_rt_main.sp0" = lab ".L1_scc_rt_main.0_entry" + Int64.ofNat (4 * 1) :=
    label_labelGap hp hg1
  refine SegW.seq (hello1_main_prologue_segW hp hend (nb := mN0 lab J) hF hR hal (by omega) hhi rfl
    (by show SO.le ⟨-80, []⟩ (oFr 80) = true; decide) hW.pro ?_)
    (SegW.seq (Q := At exe endPc R F (mNC lab J))
      (seg_oneW (seg_ndW (by simp [mB0]) mB0_ok hF hR hal (by omega) hhi
        (code_of hp hend h0 (ofNat4_zero _)) hW.call fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)) ?_)
  · -- the prologue
    intro σ c hJ
    have hl := hlimM σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, Ret0.setXReg_TPIDR]
  · simp only [mN0, mNC]; rw [mB0_run]
  · simp only [mN0, mNC]; rw [mB0_run]; rfl
  · simp only [mN0, mNC] at hJ ⊢
    rw [mB0_run]
    obtain ⟨σe, hJe, h16, h8, h80, hsp, htp⟩ := hJ
    refine ⟨⟨σe, hJe, h16, h8, h80, hsp, htp⟩, ?_⟩
    rw [e1]
    show BitVec.ofInt 64 _ = _
    rw [Ret0.ofInt_bmod]
    simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
    rfl
  · -- `wc_rodata` in its region
    refine SegW.mono_pre (P := fun s c => ∃ G : MachineData × AS, At exe endPc (mR R) (mF R F G.1 G.2)
      ⟨lab "wc_rodata", ⟨0, []⟩, mRdJ0 (mNC lab J).J G.2⟩ s c) (SegW.exists_pre fun G => ?_) ?_
    · obtain ⟨hR', hal', hF'⟩ := mR_ok hR hal hF hlo hhi G.1 G.2
      refine (hello1_rodata_pre_segW hp hend hF' hR' hal' (by show (-208 : Int) ≤ -208; decide)
        (by show (0 : Int) ≤ 0; decide) (hW.rd G.1 G.2) ?_ ?_ ?_ (hxa G.1 G.2)).mono_post
        fun s c ⟨y, h⟩ => ⟨G.1, G.2, y, h⟩
      · rintro σ c ⟨rfl, ⟨σe, hJe, -, -, -, hsp, htp⟩, -⟩
        have h := (hlimR σe c hJe).mono (F' := mF R F G.1 G.2) fun m h => h.1
        have ht : tcbA (enter (-80) G.2).regs 8 = tcbA σe.regs 8 := by
          simp only [tcbA, enter, htp]
        rw [ht]
        show LimOk ms _ exe endPc _ (G.2.regs.SP.toBitVec - _)
        rw [hsp]; exact h
      · rintro σ c ⟨-, ⟨σe, hJe, -⟩, -⟩
        exact hq σe c hJe
      · intro q hq' a ha
        exact fun m hm => hmem q hq' a ha m hm.1
    · intro s c h
      obtain ⟨m0, σC, he, hn, hdc, hpc, σ, hA, hD, hc, hσ, hJ⟩ := at_enter (lo' := -208) (hi' := 0)
        (by show R.lo ≤ -80 + -208; omega) (by show (-80 : Int) < R.hi; omega) (by decide)
        (by show (-80 : Int) % 8 = 0; decide) h
      exact ⟨(m0, σC), he, hn, hdc, hpc, σ, hA, hD, hσ, hc ▸ hJ⟩

end MainPre

/-! ## `scc_rt_main` from `wc_rodata`'s `.sp0` -/

section MainPostNodes

variable (lab : Label → Int64) (R : Region) (σC : AS) (Jr Jw : AS → Ctl → Prop)

/-- `scc_rt_main`'s `.sp0`, after `wc_rodata`'s return (of invariant `Jr`
in its region) left its region (`at_leave`, the caller's state `σC`). -/
def mS0 : ND := ⟨lab ".L1_scc_rt_main.sp0", ⟨-80, []⟩, fun σ c => ∃ σx, Jr σx c ∧ σ = leave (mR R) (-80) σC σx⟩

/-- **The call of `wc_main`**: its arguments `wc_rodata`'s results and the
saved `x0`, `sp` and the thread pointer as `wc_rodata` returned them, the
return address `.sp1`. -/
def mWC : ND := ⟨lab "wc_main", ⟨-80, []⟩, fun σ c => ∃ σx, Jr σx c ∧
  σ.regs.X0 = σx.regs.X0 ∧ σ.regs.X1 = σx.regs.X1 ∧ σ.regs.X2 = σx.regs.X2 ∧ σ.regs.X3 = σx.regs.X3 ∧
  σ.regs.X4.toBitVec = σC.slot (-80) ∧ σ.regs.SP = σx.regs.SP ∧ σ.regs.TPIDR_EL0 = σx.regs.TPIDR_EL0 ∧
  σ.regs.X30.toBitVec = (lab ".L1_scc_rt_main.sp1").toBitVec⟩

/-- `wc_main`'s entry invariant from the caller's state and control at the
call. -/
def wJ0 (g : AS × Ctl) (σ : AS) (c : Ctl) : Prop := σ = enter (-80) g.1 ∧ c = g.2 ∧ (mWC lab σC Jr).J g.1 g.2

/-- `wc_main`'s return to `.sp1` (invariant `Jw`). -/
def wXr : ND := ⟨lab ".L1_scc_rt_main.sp1", ⟨0, []⟩, Jw⟩

/-- `scc_rt_main`'s `.sp1`: the registers `wc_main` returned with. -/
def mS1 : ND := ⟨lab ".L1_scc_rt_main.sp1", ⟨-80, []⟩, fun σ c => ∃ σx, Jw σx c ∧ σ.regs = σx.regs⟩

/-- `print`'s abort under `wc_main` under `scc_rt_main`. -/
def mAb : ND := ⟨lab "scc_rt_abort", ⟨-224, []⟩, fun σ _ => σ.regs.X0 = 4⟩

end MainPostNodes

/-- `scc_rt_main`'s nodes from the call of `wc_main`. -/
def mPN (lab : Label → Int64) (σC : AS) (Jr Jw : AS → Ctl → Prop) : Bool → ND
  | false => mWC lab σC Jr
  | true => mS1 lab Jw

/-- `wc_main`'s region at the call. -/
abbrev wR (R : Region) : Region := R.callee (-80) (-144) 0

/-- **`scc_rt_main`'s states from `wc_rodata`'s `.sp0` inside `W`**, none
moved by `K`: `wc_rodata`'s from `.sp0` in its region, the `.sp0` block's,
`wc_main`'s in its region for every call returning to `.sp1` (the caller's
cells outside it holding values), and the `exit_group` tail's. -/
structure MainPostW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (m0 : MachineData) (σC : AS)
    (Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop) : Prop where
  rd : RdPostW W K exe endPc (mR R) (mF R F m0 σC) Jp J1 J2 J3 J4
  sp0 : BlkW W K exe endPc R F (mS0 (_root_.Executable.labels exe).label R σC Jr) mB1
  wc : ∀ g : AS × Ctl, Wc1W W K exe endPc (wR R) (fun m => F m ∧ CallerCells R (-80) (-144) 0 m) ms
    (wJ0 (_root_.Executable.labels exe).label σC Jr g)
  exit : ExitW W K exe endPc R F (mS1 (_root_.Executable.labels exe).label Jw) 40

/-- `scc_rt_main` from `.sp0` is inside the trivial predicate, with no
outside moves. -/
theorem MainPostW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {m0 : MachineData} {σC : AS} {Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop} :
    MainPostW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms m0 σC Jp J1 J2 J3 J4 Jr Jw :=
  ⟨RdPostW.triv, BlkW.triv, fun _ => Wc1W.triv, ExitW.triv⟩

/-- `Wc1W` under a weaker frame condition holds under a stronger one. -/
theorem Wc1W.mono {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F F' : MachineData → Prop} {ms : MemSide isaLSE2} {J0 : AS → Ctl → Prop}
    (h : Wc1W W K exe endPc R F ms J0) (hFF : ∀ m, F' m → F m) : Wc1W W K exe endPc R F' ms J0 :=
  ⟨Ret0.proW_mono h.pro hFF, ⟨Ret0.blkW_mono h.body.e hFF, fun g hg => printW_mono (h.body.print g hg)
    fun m hm => ⟨hFF m hm.1, hm.2⟩, Ret0.blkW_mono h.body.sp4 hFF⟩⟩

section MainPost

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from `wc_rodata`'s `.sp0` is one segment inside `W`**
in any valid layout of `hello1Prog`, for a caller's state `m0`, `σC` at
`wc_rodata`'s call: `wc_rodata` from `.sp0` in its region
(`hello1_rodata_post_segW` to `scc_rt_main`'s `.sp0`, of invariant `Jr`;
`hra`, `hmem`, `h1` … `h4`, `hedge` as there), leaving its region
(`at_leave`), the `.sp0` block, the call of `wc_main` (`call_nd_FWK`,
`hello1_wc_segW` from `wJ0` to `.sp1`, of invariant `Jw`: `hlimW`, `hsvc`,
`hedgeW` as there; `hedgeW` for every call), and the `exit_group` tail
(`hok`). The only exit is `print`'s abort. Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_main_post_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi) {m0 : MachineData} {σC : AS} {Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop}
    (hW : MainPostW W K exe endPc R F ms m0 σC Jp J1 J2 J3 J4 Jr Jw)
    (hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".L1_scc_rt_main.sp0" = Int64.ofBitVec (σ0.slot (-8)))
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (rAddr σ0.regs .X0 i) 8 = none)
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
      ∃ c', LocalRun p c c' ∧ Jr σ' c')
    (hlimW : ∀ σx c, Jr σx c → LimOk ms F exe endPc (tcbA σx.regs 8) (σx.regs.SP.toBitVec - (96 : Int64).toBitVec))
    (hsvc : ∀ F' : MachineData → Prop, FStable (pR (wR R)) F' →
      (∀ m, F' m → (F m ∧ CallerCells R (-80) (-144) 0 m) ∧ CallerCells (wR R) (-96) (-48) 0 m) →
      ∀ g' : PG, g'.2.2 = ((_root_.Executable.labels exe).label ".L19_wc_main.sp4").toBitVec →
      SegW W K p lbl ms
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .svc))
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .n5)))
    (hedgeW : ∀ g : AS × Ctl, ∀ σ c, wcJ (wJ0 (_root_.Executable.labels exe).label σC Jr g) σ c →
      ∀ σ' : AS, (∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σ'.slot k = wcSl σ k) →
      σ'.regs.X0.toBitVec = 0#64 → σ'.regs.X29.toBitVec = σ.slot (-16) → σ'.regs.X30.toBitVec = σ.slot (-8) →
      ∃ c', LocalRun p c c' ∧ Jw σ' c')
    (hok : ∀ s c σx, Jw σx c →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label ".L1_scc_rt_main.sp1" + 4 + 4 + 4, ⟨-80, []⟩,
        fun _ _ => True⟩ s c → SysOk p ms s c (.exitGroup σx.regs.X0.toNat)) :
    SegW W K p lbl ms (At exe endPc (mR R) (mF R F m0 σC) (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .s0))
      (At exe endPc R F (mAb (_root_.Executable.labels exe).label)) := by
  let lab := (_root_.Executable.labels exe).label
  have hin := hello1_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨-, hb1⟩, -⟩, hg2⟩ := hin
  have e2 : lab ".L1_scc_rt_main.sp1" = lab ".L1_scc_rt_main.sp0" + Int64.ofNat (4 * 10) :=
    label_labelGap hp hg2
  obtain ⟨hR', hal', hF'⟩ := mR_ok hR hal hF hlo hhi m0 σC
  refine SegW.seq (Q := At exe endPc R F (mS0 lab R σC Jr))
    ((hello1_rodata_post_segW hp hend hF' hR' hal' (by show (-208 : Int) ≤ -48; decide)
      (by show (0 : Int) ≤ 0; decide) (x := ⟨lab ".L1_scc_rt_main.sp0", ⟨0, []⟩, Jr⟩) rfl hW.rd hra hmem
      h1 h2 h3 h4 hedge).mono_post fun s c h => ?_)
    (SegW.seq (Q := At exe endPc R F (mWC lab σC Jr))
      (seg_oneW (seg_ndW (by simp [mB1]) mB1_ok hF hR hal (by omega) hhi
        (code_of hp hend hb1 (ofNat4_zero _)) hW.sp0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩))
      ((fn_segW (N := mPN lab σC Jr Jw) (E := fun _ : Unit => mAb lab) (fun i => ?_) false).mono_post
        fun _ _ ⟨_, h⟩ => h))
  · -- leaving `wc_rodata`'s region
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, σx, σC', hJ, rfl, hσ⟩ :=
      at_leave (P := fun σ => σ = σC) rfl (fun m hm => ⟨hm.1, m0, σC, ⟨-80, []⟩, hm.2.1, hm.2.2, rfl⟩) h
    exact ⟨he, hn, hdc, hpc, σ, hA, hD, σx, hJ, hσ⟩
  · simp only [mS0, mWC]; rw [mB1_run]
  · simp only [mS0, mWC]; rw [mB1_run]; rfl
  · simp only [mS0, mWC] at hJ ⊢
    obtain ⟨σx, hJr, rfl⟩ := hJ
    rw [mB1_run]
    refine ⟨σx, hJr, rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_⟩
    · show (leave (mR R) (-80) σC σx).slot (-80) = _
      simp only [leave]
      exact ite_eq_right (by simp only [Region.Off, Region.callee]; omega)
    · rw [e2]
      show BitVec.ofInt 64 _ = _
      rw [Ret0.ofInt_bmod]
      simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
      rfl
  · cases i
    case false =>
      refine call_nd_FWK (KC := False) (lo' := -144) (hi' := 0) (M := fun _ => True)
        (Ne := fun g : AS × Ctl => ⟨lab "wc_main", ⟨0, []⟩, wJ0 lab σC Jr g⟩)
        (Ex := fun g : AS × Ctl => wX lab (wcJ (wJ0 lab σC Jr g)) (wXr lab Jw))
        hR hal hF (by show R.lo ≤ -80 + -144; omega) (by decide) (by show (-80 : Int) < R.hi; omega) (by decide)
        (by show (-80 : Int) % 16 = 0; decide) (by decide) (by decide) (fun h => h.elim) (fun h => h.elim)
        (fun _ h _ => h)
        (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e hcc g _ _ => by
          subst hR'e
          refine (hello1_wc_segW hp hend hF' hR' hal' hlo' hhi' (x := wXr lab Jw) rfl
            ((hW.wc g).mono fun m h => ⟨hFF m h, hcc m h⟩) ?_ ?_
            (fun F'' hF'' hFF'' g' hg' => hsvc F'' hF''
              (fun m h => ⟨⟨hFF m (hFF'' m h).1, hcc m (hFF'' m h).1⟩, (hFF'' m h).2⟩) g' hg')
            (hedgeW g)).mono_post fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩
          · rintro σ c ⟨rfl, -, σx, hJr, -, -, -, -, -, hsp, htp, -⟩
            have h := (hlimW σx _ hJr).mono (F' := F') hFF
            have ht : tcbA (enter (-80) g.1).regs 8 = tcbA σx.regs 8 := by
              simp only [tcbA, enter, htp]
            rw [ht]
            show LimOk ms _ exe endPc _ (g.1.regs.SP.toBitVec - _)
            rw [hsp]; exact h
          · rintro σ c ⟨rfl, -, σx, -, -, -, -, -, -, -, -, h30⟩
            show lab ".L1_scc_rt_main.sp1" = Int64.ofBitVec g.1.regs.X30.toBitVec
            rw [h30, int64_ofBitVec_toBitVec])
        (fun _ => rfl) ?_ ?_
      · intro σC' c hJ
        exact ⟨(σC', c), rfl, rfl, rfl, hJ⟩
      · rintro _ y σC' c σx c' σR - - hx hreg - -
        cases y
        · exact .inl ⟨true, rfl, rfl, σx, hx, hreg⟩
        · refine .inr ⟨(), rfl, rfl, ?_⟩
          show σR.regs.X0 = 4
          rw [hreg]; exact hx.1
    case true =>
      refine hello1_main_exit_segW hp hend (n := mS1 lab Jw) rfl rfl hK hF hR hal (by omega) hhi hW.exit
        fun s c σ0 ⟨σx, hJ, hr⟩ hAt => ?_
      rw [hr]
      exact hok s c σx hJ hAt

end MainPost

/-! ## From the allocator's fresh-label landing to `scc_rt_main` after it

`hello1_main_pre_segW` ends at an allocation's continuation `ms.xa`
(`hxa`); `hello1_main_post_segW` starts at `wc_rodata`'s `.sp0` in its
region. The bridge leaves the allocator's region (`at_leave`) and lands at
`.sp0` for an invariant `Jp` the landing implies (`hJp`), so the choice of
`ms.xa` stays the instance's. -/

section MainBridge

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The allocator's fresh-label landing is at `wc_rodata`'s `.sp0`**, in
its region at `scc_rt_main`'s call (caller's state `m0`, `σC`): from the
continuation node `Ea` in the allocator's region, under a frame condition
`F'` the call hands it (as in `hello1_main_pre_segW`'s `hxa`), the state is
at `pN .s0` of an invariant `Jp` every landing's state left to `wc_rodata`
satisfies (`hJp`, of the allocator's state, `wc_rodata`'s at the call, and
the call's control). -/
theorem hello1_main_xa_post {J Jp J1 J2 J3 J4 : AS → Ctl → Prop} {m0 : MachineData} {σC : AS}
    {q : AG ms (_root_.Executable.labels exe).label} {F' : MachineData → Prop}
    {l : WeakMem.AllocLabel} {b w : Nat}
    (hFF : ∀ m, F' m → mF R F m0 σC m)
    (hkeep : ∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
      (rN (_root_.Executable.labels exe).label (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) .call).J
        σ c ∧
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c ∧ CKept (mR R) (-48) (-160) 0 mC m)
    (hJp : ∀ σx σ c0 c, (Ea ms q.1 l b w).J σx c →
      (rN (_root_.Executable.labels exe).label (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) .call).J
        σ c0 →
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0 →
      Jp (leave (aR (mR R)) (-48) σ σx) c)
    {s : State} {c : Ctl} (h : At exe endPc (aR (mR R)) F' (Ea ms q.1 l b w) s c) :
    At exe endPc (mR R) (mF R F m0 σC) (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .s0) s c := by
  have h' := at_leave (R := mR R) (kc := -48) (lo' := -160) (hi' := 0)
    (P := fun σ => ∃ c0,
      (rN (_root_.Executable.labels exe).label (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) .call).J
        σ c0 ∧ (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0)
    rfl (fun m hm => by
      obtain ⟨mC, σ, c0, hA, h1, h2, hK⟩ := hkeep m hm
      exact ⟨hFF m hm, mC, σ, _, hK, hA, c0, h1, h2⟩) h
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, σx, σ', hJx, ⟨c0, h1, h2⟩, rfl⟩ := h'
  refine ⟨he, hn, hdc, ?_, _, hA, hD, hJp σx σ' c0 c hJx h1 h2⟩
  rw [hpc]
  show Int64.ofBitVec q.1.ra = (_root_.Executable.labels exe).label ".L18_wc_rodata.sp0"
  rw [← h2.2.2.1]
  show Int64.ofBitVec σ'.regs.X30.toBitVec = _
  rw [h1.2.2.2.2, int64_ofBitVec_toBitVec]

/-- **`hello1_main_pre_segW`'s `hxa` from the landing at `.sp0`**: if
every state at `wc_rodata`'s `.sp0` in its region, for some caller's state
`m0`, `σC` at the call (of an invariant `Jp m0 σC` the landings imply,
`hJp`), is one a fresh label's allocation continues in (`hpost`), the
allocator's landings are (`hello1_main_xa_post`). -/
theorem hello1_main_hxa_of_post {J : AS → Ctl → Prop} {Jp J1 J2 J3 J4 : MachineData → AS → AS → Ctl → Prop}
    (hJp : ∀ m0 σC (q : AG ms (_root_.Executable.labels exe).label) l b w σx σ c0 c, (Ea ms q.1 l b w).J σx c →
      (rN (_root_.Executable.labels exe).label (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) .call).J
        σ c0 →
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0 →
      Jp m0 σC (leave (aR (mR R)) (-48) σ σx) c)
    (hpost : ∀ l b w s c, lbl l = none → (∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
      (pN (_root_.Executable.labels exe).label (Jp m0 σC) (J1 m0 σC) (J2 m0 σC) (J3 m0 σC) (J4 m0 σC) .s0) s c) →
      ms.xa l b w s c) :
    ∀ m0 σC, ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF R F m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
        (rN (_root_.Executable.labels exe).label
          (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) .call).J σ c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR R) (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR (mR R)) F' (Ea ms q.1 l b w) s c → ms.xa l b w s c :=
  fun m0 σC q _ hFF hkeep l b w _ _ hl h =>
    hpost l b w _ _ hl ⟨m0, σC, hello1_main_xa_post hFF hkeep (hJp m0 σC q l b w) h⟩

end MainBridge

/-! ## `scc_rt_main` as a whole

`hello1_main_pre_segW`, then `wc_rodata`'s `.sp0` (the allocator's return
exit, `hret`), then `hello1_main_post_segW`; the allocation's continuation
`ms.xa` holds `.sp0`'s states (`hpost`, through the bridge), which the
second segment covers. -/

/-- **`hello1_main_post_segW`'s premises** past the layout's, for a
caller's state `m0`, `σC` at `wc_rodata`'s call: the states inside `W`
(`hW`), and the source and frame facts named there. -/
structure MainPostP (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (m0 : MachineData) (σC : AS) (Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop) : Prop where
  hW : MainPostW W K exe endPc R F ms m0 σC Jp J1 J2 J3 J4 Jr Jw
  hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".L1_scc_rt_main.sp0" = Int64.ofBitVec (σ0.slot (-8))
  hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (rAddr σ0.regs .X0 i) 8 = none
  h1 : ∀ σ0 c, Jp σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((rAddr σ0.regs .X0 0).toNat, w') }
  h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  h3 : ∀ σ0 c, J2 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((rAddr σ0.regs .X0 8).toNat, w') }
  h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  hedge : ∀ σ0 c, J4 σ0 c → ∀ σ' : AS, σ'.regs.X0.toBitVec = σ0.regs.X0.toBitVec →
      σ'.regs.X1.toBitVec = 0#64 → σ'.regs.X2.toBitVec = 2#64 → σ'.regs.X3.toBitVec = 13#64 →
      σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
      ∃ c', LocalRun p c c' ∧ Jr σ' c'
  hlimW : ∀ σx c, Jr σx c → LimOk ms F exe endPc (tcbA σx.regs 8) (σx.regs.SP.toBitVec - (96 : Int64).toBitVec)
  hsvc : ∀ F' : MachineData → Prop, FStable (pR (wR R)) F' →
      (∀ m, F' m → (F m ∧ CallerCells R (-80) (-144) 0 m) ∧ CallerCells (wR R) (-96) (-48) 0 m) →
      ∀ g' : PG, g'.2.2 = ((_root_.Executable.labels exe).label ".L19_wc_main.sp4").toBitVec →
      SegW W K p lbl ms
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .svc))
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .n5))
  hedgeW : ∀ g : AS × Ctl, ∀ σ c, wcJ (wJ0 (_root_.Executable.labels exe).label σC Jr g) σ c →
      ∀ σ' : AS, (∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σ'.slot k = wcSl σ k) →
      σ'.regs.X0.toBitVec = 0#64 → σ'.regs.X29.toBitVec = σ.slot (-16) → σ'.regs.X30.toBitVec = σ.slot (-8) →
      ∃ c', LocalRun p c c' ∧ Jw σ' c'
  hok : ∀ s c σx, Jw σx c →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label ".L1_scc_rt_main.sp1" + 4 + 4 + 4, ⟨-80, []⟩,
        fun _ _ => True⟩ s c → SysOk p ms s c (.exitGroup σx.regs.X0.toNat)

section MainAll

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` is two segments inside `W`** in any valid layout of
`hello1Prog`, for invariants at `wc_rodata`'s `.sp0` and after indexed by
the caller's state `m0`, `σC` at its call. First, from its entry
(invariant `J`) to `print`'s abort or the allocator's heap abort
(`hello1_main_pre_segW`: `hlimM`, `hlimR`, `hq`, `hmem`; the allocator's
return at `.sp0` continuing by `hret` into `hello1_main_post_segW`, of
premises `hP`). Second, from `.sp0`'s states (of `Jp`) to `print`'s abort:
the states an allocation of a fresh label continues in. The allocation's
continuation `ms.xa` stays the instance's: it holds `.sp0`'s states
(`hpost`), which every landing is (`hJp`, `hello1_main_hxa_of_post`). -/
theorem hello1_main_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi)
    {J : AS → Ctl → Prop} {Jp J1 J2 J3 J4 Jr Jw : MachineData → AS → AS → Ctl → Prop}
    (hW : MainPreW W K exe endPc R F ms J)
    (hlimM : ∀ σ c, J σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (80 : Int64).toBitVec))
    (hlimR : ∀ σ c, J σ c → LimOk ms F exe endPc (tcbA σ.regs 8)
      (σ.regs.SP.toBitVec - (80 : Int64).toBitVec - (48 : Int64).toBitVec))
    (hq : ∀ σ c, J σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ms = 3#64)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hJp : ∀ m0 σC (q : AG ms (_root_.Executable.labels exe).label) l b w σx σ c0 c, (Ea ms q.1 l b w).J σx c →
      (rN (_root_.Executable.labels exe).label (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) .call).J σ c0 →
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0 →
      Jp m0 σC (leave (aR (mR R)) (-48) σ σx) c)
    (hpost : ∀ l b w s c, lbl l = none → (∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
      (pN (_root_.Executable.labels exe).label (Jp m0 σC) (J1 m0 σC) (J2 m0 σC) (J3 m0 σC) (J4 m0 σC) .s0) s c) →
      ms.xa l b w s c)
    (hret : ∀ m0 σC σ c,
      (rX ms (_root_.Executable.labels exe).label lbl
        (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) .sp0).J σ c →
      Jp m0 σC σ c)
    (hP : ∀ m0 σC, MainPostP W K p lbl ms exe endPc R F m0 σC (Jp m0 σC) (J1 m0 σC) (J2 m0 σC) (J3 m0 σC)
      (J4 m0 σC) (Jr m0 σC) (Jw m0 σC)) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (fun s c => At exe endPc R F (mAb (_root_.Executable.labels exe).label) s c ∨
        ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
          (rX ms (_root_.Executable.labels exe).label lbl
            (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) .abort) s c) ∧
    SegW W K p lbl ms
      (fun s c => ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
        (pN (_root_.Executable.labels exe).label (Jp m0 σC) (J1 m0 σC) (J2 m0 σC) (J3 m0 σC) (J4 m0 σC) .s0) s c)
      (At exe endPc R F (mAb (_root_.Executable.labels exe).label)) := by
  have hS : SegW W K p lbl ms
      (fun s c => ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
        (pN (_root_.Executable.labels exe).label (Jp m0 σC) (J1 m0 σC) (J2 m0 σC) (J3 m0 σC) (J4 m0 σC) .s0) s c)
      (At exe endPc R F (mAb (_root_.Executable.labels exe).label)) :=
    SegW.exists_pre fun m0 => SegW.exists_pre fun σC =>
      let h := hP m0 σC
      hello1_main_post_segW hp hend hF hR hal hlo hhi hK h.hW h.hra h.hmem h.h1 h.h2 h.h3 h.h4 h.hedge h.hlimW
        h.hsvc h.hedgeW h.hok
  refine ⟨SegW.seq_left ((hello1_main_pre_segW hp hend hF hR hal hlo hhi hW hlimM hlimR hq hmem
    (hello1_main_hxa_of_post hJp hpost)).mono_post ?_) hS, hS⟩
  rintro s c ⟨m0, σC, y, h⟩
  cases y
  · obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
    exact .inl ⟨m0, σC, he, hn, hdc, hpc, σ, hA, hD, hret m0 σC σ c hJ⟩
  · exact .inr ⟨m0, σC, h⟩

end MainAll

end Spike.Lib.A64.Flow.Hello1
