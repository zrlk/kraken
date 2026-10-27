/-
**`hello1.w`'s `scc_rt_main` on x64**, inside `W`, in any valid layout of
`hello1Cells` (`Spike/Lib/X64Hello1Code.lean`), from checks decided once on
the cells (`decide +kernel`): the x64 twin of
`Spike/Lib/A64Hello1Main.lean`. Offsets are from `%rsp` at
`scc_rt_main`'s entry; `%rbp` is at `-8`, the frame's base at `-72`.

- `hello1_main_pre_segW`: from `scc_rt_main`'s entry (invariant `J`): its
  prologue, `call wc_rodata`, and `wc_rodata` up to the allocator's return
  in the callee's region at the call (`at_enter`, then
  `hello1_rodata_pre_segW`; the region based at the pushed return address,
  `-80`: `wc_rodata`'s frame and the allocator's below reach `-288`).
  Exits: `wc_rodata`'s, in its region, for some caller's state at the call.
- `hello1_main_post_segW`: from `wc_rodata`'s `.x13` after the allocator
  (in `scc_rt_main`'s region at the call): the rest of `wc_rodata`, its
  return (`at_leave`), the `.x2` block, `call wc_main` (`hello1_wc_segW`),
  and `scc_rt_main`'s `exit_group` tail. `print`'s write stays the given
  segment `hsvc`; the source facts are named premises over the user's
  invariants, as are `%rbp`'s offset at the two returns (`hbpr`, `hbpw`).
- `hello1_main_segW`: the two composed, as two segments: from the entry to
  the aborts, and from `.x13`'s states (the allocation's continuation
  `ms.xa` holds, `hpost`) to `print`'s abort.
- `hello1_main_xa_post`, `hello1_main_hxa_of_post`: the bridge between the
  two, from the allocator's fresh-label landing to `wc_rodata`'s `.x13` of
  an invariant the landing implies; the choice of `ms.xa` stays the
  instance's.
-/
import Spike.Lib.X64Hello1Rodata

namespace Spike.Lib.X64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells LimOk seg_oneW blkW_mono nodeW_mono proW_mono)
open Spike.Lib.X64.Alloc (Call AllocW Ea Jfull)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## `scc_rt_main`'s blocks -/

/-- `scc_rt_main`'s body offsets: `%rsp` at the frame's base, `%rbp` at the
saved `%rbp`. -/
abbrev mO : SO := ⟨-72, [(.rbp, -8)]⟩

/-- `scc_rt_main`'s `.entry` block: the call of `wc_rodata`. -/
def mB0 : List (Directive × Nat) := (parse("call wc_rodata")).zip [5]

/-- `scc_rt_main`'s `.x2` block: `wc_rodata`'s results to the frame and
back as `wc_main`'s arguments, the thread pointer the fifth, the call of
`wc_main`. -/
def mB1 : List (Directive × Nat) := (parse("movq %rax, -16(%rbp)
movq %rdx, -24(%rbp)
movq %rcx, -32(%rbp)
movq %rsi, -40(%rbp)
movq -16(%rbp), %rdi
movq -24(%rbp), %rsi
movq -32(%rbp), %rdx
movq -40(%rbp), %rcx
movq -8(%rbp), %r8
call wc_main")).zip [4, 4, 4, 4, 4, 4, 4, 4, 4, 5]

block_spec mB0 (-288) 8 mO mB0
block_spec mB1 (-288) 8 mO mB1

/-- **`scc_rt_main`'s blocks in `cells`**, each call's return label right
after it. -/
def mainIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lscc_rt_main.entry" 0 mB0 && blockAtB cells ".Lscc_rt_main.x2" 0 mB1 &&
    labelGapB cells ".Lscc_rt_main.entry" ".Lscc_rt_main.x2" 5 &&
    labelGapB cells ".Lscc_rt_main.x2" ".Lscc_rt_main.x3" 41

theorem hello1_mainIn : mainIn SccCode.hello1Cells = true := by decide +kernel

/-- **`scc_rt_main`'s frame** as some entry state of `J` left it: the
return address, the saved `%rbp`, the saved `%rdi` (the thread pointer),
`%rsp` 72 below, the thread pointer register. -/
def mJ (J : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ σe, J σe c ∧ σ.slot 0 = σe.slot 0 ∧ σ.slot (-8) = σe.regs.rbp.toBitVec ∧
    σ.slot (-16) = σe.regs.rdi.toBitVec ∧ σ.regs.rsp.toBitVec = σe.regs.rsp.toBitVec - 8#64 - 64#64 ∧
    σ.regs.fsBase = σe.regs.fsBase

section MainNodes

variable (lab : Label → Int64) (R : Region) (J : AS → Ctl → Prop)

/-- `scc_rt_main`'s `.entry`, `%rbp` at the saved `%rbp`. -/
def mN0 : ND := ⟨lab ".Lscc_rt_main.entry", mO, wJ R (mJ J)⟩

/-- **The call of `wc_rodata`**: the frame as at `.entry`, `%rsp` past the
pushed return address `.x2`. -/
def mNC : ND := ⟨lab "wc_rodata", ⟨-80, []⟩, fun σ c => ∃ σe, J σe c ∧ σ.slot 0 = σe.slot 0 ∧
  σ.slot (-8) = σe.regs.rbp.toBitVec ∧ σ.slot (-16) = σe.regs.rdi.toBitVec ∧
  σ.regs.rsp.toBitVec = σe.regs.rsp.toBitVec - 8#64 - 64#64 - 8#64 ∧ σ.regs.fsBase = σe.regs.fsBase ∧
  σ.regs.get64 .rbp = R.addr (-8) ∧ σ.slot (-80) = (lab ".Lscc_rt_main.x2").toBitVec⟩

end MainNodes

/-- `wc_rodata`'s region at the call: based at the pushed return address. -/
abbrev mR (R : Region) : Region := R.callee (-80) (-208) 8

/-- **`wc_rodata`'s frame condition at the call** from the caller's state
`m0`, `σC` (`at_enter`). -/
def mF (R : Region) (F : MachineData → Prop) (m0 : MachineData) (σC : AS) (m : MachineData) : Prop :=
  F m ∧ CKept R (-80) (-208) 8 m0 m ∧ Abs R ⟨-80, []⟩ m0 σC

/-- `wc_rodata`'s entry invariant from the caller's state `σC` at the call
node of invariant `Jc`. -/
def mRdJ0 (Jc : AS → Ctl → Prop) (σC : AS) (σ : AS) (c : Ctl) : Prop := σ = enter (-80) σC ∧ Jc σC c

/-- **`scc_rt_main`'s states up to `wc_rodata`'s allocator's return inside
`W`**, none moved by `K`: its prologue's, the call block's, and
`wc_rodata`'s in its region for every caller's state at the call. -/
structure MainPreW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (J : AS → Ctl → Prop) : Prop where
  pro : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") 64 8
    ".Lscc_rt_main.stk" 5 9 3 2 4 [(.rdi, -8, 4)] J
  call : BlkW W K exe endPc R F (mN0 (_root_.Executable.labels exe).label R J) mB0
  rd : ∀ m0 σC, RdPreW W K exe endPc (mR R) (mF R F m0 σC) ms
    (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC)
    (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC)

/-- `scc_rt_main` up to the allocator's return is inside the trivial
predicate, with no outside moves. -/
theorem MainPreW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {J : AS → Ctl → Prop} :
    MainPreW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J :=
  ⟨XProW.triv, BlkW.triv, fun _ _ => RdPreW.triv⟩

section MainPre

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

omit [Executable.ValidLayout exe] in
/-- `wc_rodata`'s region at the call is a region, its frame condition
stable. -/
theorem mR_ok (hR : R.OK) (hF : FStable R F) (hlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi) (m0 : MachineData) (σC : AS) :
    (mR R).OK ∧ FStable (mR R) (mF R F m0 σC) :=
  ⟨Region.callee_ok hR (by omega) (by decide) (by omega) (by omega),
    fstable_enter hR hF (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) (by decide)⟩

/-- **`scc_rt_main` up to `wc_rodata`'s allocator's return is one segment
inside `W`** in any valid layout of `hello1Cells`: from its entry
(invariant `J`, `%rsp` at the region's offset 0) to `wc_rodata`'s exits
(`hello1_rodata_pre_segW`) in its region at the call, for some caller's
state there. The limit word's facts hold for both frames (`hlimM`,
`hlimR`); the source at the entry is at `wc_rodata`'s allocation (`hq`);
`hmem`, `hxa` as for `hello1_rodata_pre_segW`, for every caller's state
at the call. Its states lie in `W`, none moved by `K` (`hW`).
VACUOUS at the entry at `rodata`'s source (`hq` at `rdC0`): see X64Hello1RodataSetupG (`rdC0_not_call`). -/
theorem hello1_main_pre_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} (hW : MainPreW W K exe endPc R F ms J)
    (hlimM : ∀ σ c, J σ c → LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec))
    (hlimR : ∀ σ c, J σ c → LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - 64#64 - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hq : ∀ σ c, J σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ms = 3#64)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ m0 σC, ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF R F m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
        (rN (_root_.Executable.labels exe).label (mR R)
          (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC) .call).J σ c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR R) (-48) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR (mR R)) F' (Ea ms q.1 l b w) s c → ms.xa l b w s c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (fun s c => ∃ m0 σC y, At exe endPc (mR R) (mF R F m0 σC)
        (rX ms (_root_.Executable.labels exe).label lbl (mR R)
          (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC) y) s c) := by
  have hin := hello1_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨h0, -⟩, hg1⟩, -⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e5 : lab ".Lscc_rt_main.x2" = lab ".Lscc_rt_main.entry" + Int64.ofNat 5 := label_labelGapB hp hg1
  refine SegW.seq (hello1_main_prologue_segW hp hend (nb := ⟨lab ".Lscc_rt_main.entry", mO, mJ J⟩) hF hR
    (by omega) (by omega) rfl (by show SO.le mO (oF 64) = true; decide) hW.pro ?_)
    (SegW.seq (Q := At exe endPc R F (mNC lab R J))
      ((seg_oneW (seg_ndW (n := mN0 lab R J) (by simp [mB0]) mB0_ok hF hR hlo hhi
        (code_field hp hend h0 (ofNat_zero' _)) hW.call fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
        fun _ _ h => At.reg_addr (r := .rbp) (k := -8) rfl h) ?_)
  · -- the prologue
    intro σ c hJ
    have hl := hlimM σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64]
  · simp only [mN0, mNC]; rw [mB0_run]
  · simp only [mN0, mNC]; rw [mB0_run]; rfl
  · simp only [mN0, mNC] at hJ ⊢
    rw [mB0_run]
    obtain ⟨⟨σe, hJe, h0', h8, h16, hsp, hfs⟩, hb⟩ := hJ
    refine ⟨σe, hJe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [upd_apply]; exact h0'
    · simp only [upd_apply]; exact h8
    · simp only [upd_apply]; exact h16
    · simp [Reg64s.set64, hsp]
    · simp [Reg64s.set64, hfs]
    · rw [Reg64s.get64_set64_ne _ (by decide)]; exact hb
    · rw [e5]
      simp only [upd_apply, ↓reduceIte, Int64.toBitVec_add]
      rfl
  · -- `wc_rodata` in its region
    refine SegW.mono_pre (P := fun s c => ∃ G : MachineData × AS, At exe endPc (mR R) (mF R F G.1 G.2)
      ⟨lab "wc_rodata", ⟨0, []⟩, mRdJ0 (mNC lab R J).J G.2⟩ s c) (SegW.exists_pre fun G => ?_) ?_
    · obtain ⟨hR', hF'⟩ := mR_ok hR hF hlo hhi G.1 G.2
      refine (hello1_rodata_pre_segW hp hend hF' hR' (by show (-208 : Int) ≤ -208; decide)
        (by show (8 : Int) ≤ 8; decide) (hW.rd G.1 G.2) ?_ ?_ ?_ (hxa G.1 G.2)).mono_post
        fun s c ⟨y, h⟩ => ⟨G.1, G.2, y, h⟩
      · rintro σ c ⟨rfl, ⟨σe, hJe, -, -, -, hsp, hfs, -, -⟩⟩
        have h := (hlimR σe c hJe).mono (F' := mF R F G.1 G.2) fun m h => h.1
        show LimOk ms _ (G.2.regs.fsBase.toBitVec + _) (G.2.regs.rsp.toBitVec - _ - _)
        rw [hfs, hsp]; exact h
      · rintro σ c ⟨-, ⟨σe, hJe, -⟩⟩
        exact hq σe c hJe
      · intro q hq' a ha
        exact fun m hm => hmem q hq' a ha m hm.1
    · intro s c h
      obtain ⟨m0, σC, he, hn, hdc, hpc, σ, hA, hD, hc, hσ, hJ⟩ := at_enter (e0 := 0) (lo' := -208) (hi' := 8)
        (by show R.lo ≤ -80 - 0 + -208; omega) (by show (-80 : Int) - 0 + 8 ≤ R.hi; omega)
        (by show ((-80 : Int) - 0) % 8 = 0; decide) h
      exact ⟨(m0, σC), he, hn, hdc, hpc, σ, hA, hD, hσ, hc ▸ hJ⟩

end MainPre

/-! ## `scc_rt_main` from `wc_rodata`'s `.x13` -/

section MainPostNodes

variable (lab : Label → Int64) (R : Region) (σC : AS) (Jr Jw : AS → Ctl → Prop)

/-- `wc_rodata`'s `.x13` for the invariant `Jp` (offsets as the allocator's
return left them). -/
def rdX13 (Jp : AS → Ctl → Prop) : ND := ⟨lab ".Lwc_rodata.x13", ⟨-40, []⟩, Jp⟩

/-- `scc_rt_main`'s `.x2`, after `wc_rodata`'s return (of invariant `Jr`
in its region) left its region (`at_leave`, the caller's state `σC`). -/
def mS0 : ND := ⟨lab ".Lscc_rt_main.x2", mO, fun σ c => ∃ σx, Jr σx c ∧ σ = leave (mR R) (-80) σC σx⟩

/-- **The call of `wc_main`**: its arguments `wc_rodata`'s results and the
saved thread pointer, `%rsp` past the pushed return address `.x3`, `%rbp`
and the thread pointer register as `wc_rodata` returned them. -/
def mWC : ND := ⟨lab "wc_main", ⟨-80, []⟩, fun σ c => ∃ σx, Jr σx c ∧
  σ.regs.rdi = σx.regs.rax ∧ σ.regs.rsi = σx.regs.rdx ∧ σ.regs.rdx = σx.regs.rcx ∧ σ.regs.rcx = σx.regs.rsi ∧
  σ.regs.r8.toBitVec = σC.slot (-16) ∧ σ.regs.rsp.toBitVec = σx.regs.rsp.toBitVec - 8#64 ∧
  σ.regs.fsBase = σx.regs.fsBase ∧ σ.regs.rbp = σx.regs.rbp ∧
  σ.slot (-80) = (lab ".Lscc_rt_main.x3").toBitVec⟩

/-- `wc_main`'s entry invariant from the caller's state and control at the
call. -/
def wJ0 (g : AS × Ctl) (σ : AS) (c : Ctl) : Prop := σ = enter (-80) g.1 ∧ c = g.2 ∧ (mWC lab σC Jr).J g.1 g.2

/-- `wc_main`'s return to `.x3` (invariant `Jw`). -/
def wXr : ND := ⟨lab ".Lscc_rt_main.x3", ⟨8, []⟩, Jw⟩

/-- `scc_rt_main`'s `.x3`: the registers `wc_main` returned with. -/
def mS1 : ND := ⟨lab ".Lscc_rt_main.x3", ⟨-72, []⟩, fun σ c => ∃ σx, Jw σx c ∧ σ.regs = σx.regs⟩

/-- `.x3` with `%rbp` at the saved `%rbp`: the `exit_group` tail's node. -/
def mS1R : ND := ⟨lab ".Lscc_rt_main.x3", mO, (mS1 lab Jw).J⟩

/-- `print`'s abort under `wc_main` under `scc_rt_main`. -/
def mAb : ND := ⟨lab "scc_rt_abort", ⟨-224, []⟩, fun σ _ => σ.regs.get64 .rdi = 4⟩

end MainPostNodes

/-- `scc_rt_main`'s nodes from the call of `wc_main`. -/
def mPN (lab : Label → Int64) (σC : AS) (Jr Jw : AS → Ctl → Prop) : Bool → ND
  | false => mWC lab σC Jr
  | true => mS1 lab Jw

/-- `wc_main`'s region at the call: based at the pushed return address. -/
abbrev wR (R : Region) : Region := R.callee (-80) (-144) 8

/-- **`scc_rt_main`'s states from `wc_rodata`'s `.x13` inside `W`**, none
moved by `K`: `wc_rodata`'s from `.x13` in its region, the `.x2` block's,
`wc_main`'s in its region for every call (the caller's cells outside it
holding values), and the `exit_group` tail's. -/
structure MainPostW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (m0 : MachineData) (σC : AS)
    (Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop) : Prop where
  rd : RdPostW W K exe endPc (mR R) (mF R F m0 σC) Jp J1 J2 J3 J4
  x2 : BlkW W K exe endPc R F (mS0 (_root_.Executable.labels exe).label R σC Jr) mB1
  wc : ∀ g : AS × Ctl, Wc1W W K exe endPc (wR R) (fun m => F m ∧ CallerCells R (-80) (-144) 8 m) ms
    (wJ0 (_root_.Executable.labels exe).label σC Jr g)
  exit : XExitW W K exe endPc R F (mS1R (_root_.Executable.labels exe).label Jw) (-72) (-8) (-48) 4 4 5

/-- `scc_rt_main` from `.x13` is inside the trivial predicate, with no
outside moves. -/
theorem MainPostW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {m0 : MachineData} {σC : AS} {Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop} :
    MainPostW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms m0 σC Jp J1 J2 J3 J4 Jr Jw :=
  ⟨RdPostW.triv, BlkW.triv, fun _ => Wc1W.triv, XExitW.triv⟩

/-- `Wc1W` under a weaker frame condition holds under a stronger one. -/
theorem Wc1W.mono {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F F' : MachineData → Prop} {ms : MemSide isa} {J0 : AS → Ctl → Prop}
    (h : Wc1W W K exe endPc R F ms J0) (hFF : ∀ m, F' m → F m) : Wc1W W K exe endPc R F' ms J0 :=
  ⟨proW_mono h.pro hFF, ⟨blkW_mono h.body.e hFF, nodeW_mono h.body.mul hFF, blkW_mono h.body.e2 hFF,
    fun g hg => printW_mono (h.body.print g hg) fun m hm => ⟨hFF m hm.1, hm.2⟩, blkW_mono h.body.x15 hFF⟩⟩

section MainPost

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from `wc_rodata`'s `.x13` is one segment inside `W`**
in any valid layout of `hello1Cells`, for a caller's state `m0`, `σC` at
`wc_rodata`'s call: `wc_rodata` from `.x13` in its region
(`hello1_rodata_post_segW` to `scc_rt_main`'s `.x2`, of invariant `Jr`;
`hbp`, `hra`, `hmem`, `h1` … `h4`, `hedge` as there), leaving its region
(`at_leave`; `%rbp` at the saved `%rbp`, `hbpr`), the `.x2` block, the call
of `wc_main` (`call_nd_FWK`, `hello1_wc_segW` from `wJ0` to `.x3`, of
invariant `Jw`: `hlimW`, `hsvc`, `hedgeW` as there; `hedgeW` for every
call), and the `exit_group` tail (`%rbp` at the saved `%rbp`, `hbpw`;
`hok`). The only exit is `print`'s abort. Its states lie in `W`, none moved
by `K` (`hW`).
VACUOUS at .x13 at `rodata`'s source: see X64Hello1RodataSetupG (`hand_x13_empty`). -/
theorem hello1_main_post_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) {m0 : MachineData} {σC : AS} {Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop}
    (hW : MainPostW W K exe endPc R F ms m0 σC Jp J1 J2 J3 J4 Jr Jw)
    (hbp : ∀ σ0 c, Jp σ0 c → σ0.regs.get64 .rbp = (mR R).addr (-8))
    (hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".Lscc_rt_main.x2" = Int64.ofBitVec (σ0.slot 0))
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (bAddr σ0.regs .rax i) 8 = none)
    (h1 : ∀ σ0 c, Jp σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((bAddr σ0.regs .rax 0).toNat, w') })
    (h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (h3 : ∀ σ0 c, J2 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((bAddr σ0.regs .rax 8).toNat, w') })
    (h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hedge : ∀ σ0 c, J4 σ0 c → ∀ σ' : AS, σ'.regs.rax.toBitVec = σ0.regs.rax.toBitVec →
      σ'.regs.rdx.toBitVec = 0#64 → σ'.regs.rcx.toBitVec = 2#64 → σ'.regs.rsi.toBitVec = 13#64 →
      σ'.regs.rbp.toBitVec = σ0.slot (-8) → σ'.regs.rsp.toBitVec = σ0.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ Jr σ' c')
    (hbpr : ∀ σx c, Jr σx c → σx.regs.get64 .rbp = R.addr (-8))
    (hlimW : ∀ σx c, Jr σx c → LimOk ms F (σx.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σx.regs.rsp.toBitVec - 8#64 - 8#64 - (80 : Int64).toBitVec))
    (hsvc : ∀ F' : MachineData → Prop, FStable (pR (wR R)) F' →
      (∀ m, F' m → ((F m ∧ CallerCells R (-80) (-144) 8 m) ∧ CallerCells (wR R) (-96 - 8) (-40) 16 m) ∧
        Spike.Lib.X64.Rt.WcRa (wR R) ((_root_.Executable.labels exe).label ".Lscc_rt_main.x3") m ∧
        Spike.Lib.X64.Rt.WcFp (wR R) (R.addr (-8)) m) →
      ∀ g' : PG, g'.2.2 = ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec →
      g'.2.1 = (wR R).addr (-8) →
      SegW W K p lbl ms
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .sys))
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .n5)))
    (hedgeW : ∀ g : AS × Ctl, ∀ σ c, wcJ (wJ0 (_root_.Executable.labels exe).label σC Jr g) σ c →
      σ.regs.get64 .rbp = (wR R).addr (-8) → ∀ σ' : AS,
      (∀ k, -88 ≤ k → k < 8 → k % 8 = 0 → σ'.slot k = wcSl (_root_.Executable.labels exe).label σ k) →
      σ'.regs.rax.toBitVec = 0#64 → σ'.regs.rbp.toBitVec = σ.slot (-8) →
      σ'.regs.rsp.toBitVec = σ.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ Jw σ' c')
    (hbpw : ∀ σx c, Jw σx c → σx.regs.get64 .rbp = R.addr (-8))
    (hok : ∀ s c σx, Jw σx c →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lscc_rt_main.x3" + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, mO, fun _ _ => True⟩ s c → SysOk p ms s c (.exitGroup σx.regs.rax.toNat)) :
    SegW W K p lbl ms (At exe endPc (mR R) (mF R F m0 σC) (rdX13 (_root_.Executable.labels exe).label Jp))
      (At exe endPc R F (mAb (_root_.Executable.labels exe).label)) := by
  let lab := (_root_.Executable.labels exe).label
  have hin := hello1_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨-, hb1⟩, -⟩, hg2⟩ := hin
  have e41 : lab ".Lscc_rt_main.x3" = lab ".Lscc_rt_main.x2" + Int64.ofNat 41 := label_labelGapB hp hg2
  obtain ⟨hR', hF'⟩ := mR_ok hR hF hlo hhi m0 σC
  refine SegW.seq (Q := At exe endPc R F (mS0 lab R σC Jr))
    ((hello1_rodata_post_segW hp hend hF' hR' (by show (-208 : Int) ≤ -40; decide)
      (by show (8 : Int) ≤ 8; decide) (x := ⟨lab ".Lscc_rt_main.x2", ⟨8, []⟩, Jr⟩) rfl hW.rd hbp hra
      hmem h1 h2 h3 h4 hedge).mono_post fun s c h => ?_)
    (SegW.seq (Q := At exe endPc R F (mWC lab σC Jr))
      (seg_oneW (seg_ndW (by simp [mB1]) mB1_ok hF hR hlo hhi
        (code_field hp hend hb1 (ofNat_zero' _)) hW.x2 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩))
      ((fn_segW (N := mPN lab σC Jr Jw) (E := fun _ : Unit => mAb lab) (fun i => ?_) false).mono_post
        fun _ _ ⟨_, h⟩ => h))
  · -- leaving `wc_rodata`'s region
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, σx, σC', hJ, rfl, hσ⟩ :=
      at_leave (P := fun σ => σ = σC) rfl (fun m hm => ⟨hm.1, m0, σC, ⟨-80, []⟩, hm.2.1, hm.2.2, rfl⟩) h
    refine At.rbp_addr (J := (mS0 lab R σC' Jr).J) ⟨he, hn, hdc, hpc, σ, hA, hD, σx, hJ, hσ⟩ ?_
    rintro σ c ⟨σx, hJ, rfl⟩
    exact hbpr σx c hJ
  · simp only [mS0, mWC]; rw [mB1_run]
  · simp only [mS0, mWC]; rw [mB1_run]; rfl
  · simp only [mS0, mWC] at hJ ⊢
    obtain ⟨σx, hJr, rfl⟩ := hJ
    rw [mB1_run]
    refine ⟨σx, hJr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Reg64s.set64, leave]
    · simp [Reg64s.set64, leave]
    · simp [Reg64s.set64, leave]
    · simp [Reg64s.set64, leave]
    · simp only [Reg64s.set64]
      show (leave (mR R) (-80) σC σx).slot (-16) = _
      simp only [leave]
      exact ite_eq_right (by simp only [Region.Off, Region.callee]; omega)
    · simp [Reg64s.set64, leave]
    · simp [Reg64s.set64, leave]
    · simp [Reg64s.set64, leave]
    · rw [e41]
      simp only [upd_apply, ↓reduceIte, Int64.toBitVec_add]
      rfl
  · cases i
    case false =>
      refine call_nd_FWK (KC := False) (e0 := 0) (lo' := -144) (hi' := 8) (M := fun _ => True)
        (Ne := fun g : AS × Ctl => ⟨lab "wc_main", ⟨0, []⟩, wJ0 lab σC Jr g⟩)
        (Ex := fun g : AS × Ctl => wX lab (wcJ (wJ0 lab σC Jr g)) (wXr lab Jw))
        hR hF (by show R.lo ≤ -80 - 0 + -144; omega) (by decide) (by show (-80 : Int) - 0 < R.hi; omega)
        (by show (-80 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-80 : Int) - 0) % 8 = 0; decide) (by decide)
        (by decide) (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
        (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc g _ _ => by
          subst hR'e
          refine (hello1_wc_segW hp hend hF' hR' hlo' hhi' (x := wXr lab Jw) rfl
            ((hW.wc g).mono fun m h => ⟨hFF m h, hcc m h⟩) ?_ ?_ (fp := R.addr (-8)) ?_
            (fun F'' hF'' hFF'' g' hg' hg1 => hsvc F'' hF''
              (fun m h => ⟨⟨⟨hFF m (hFF'' m h).1.1, hcc m (hFF'' m h).1.1⟩, (hFF'' m h).1.2⟩, (hFF'' m h).2⟩)
              g' hg' hg1)
            (hedgeW g)).mono_post fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩
          · rintro σ c ⟨rfl, -, σx, hJr, -, -, -, -, -, hsp, hfs, -, -⟩
            have h := (hlimW σx _ hJr).mono (F' := F') hFF
            show LimOk ms F' (g.1.regs.fsBase.toBitVec + _) (g.1.regs.rsp.toBitVec - _ - _)
            rw [hfs, hsp]; exact h
          · rintro σ c ⟨rfl, -, σx, -, -, -, -, -, -, -, -, -, h80⟩
            show lab ".Lscc_rt_main.x3" = Int64.ofBitVec (g.1.slot (-80 + 0))
            rw [show (-80 : Int) + 0 = -80 by decide, h80, int64_ofBitVec_toBitVec]
          · rintro σ c ⟨rfl, -, σx, hJr, -, -, -, -, -, -, -, hbp, -⟩
            show g.1.regs.get64 .rbp = _
            simp only [Reg64s.get64] at hbpr ⊢
            rw [hbp]; exact hbpr σx _ hJr)
        (fun _ => rfl) ?_ ?_
      · intro σC' c hJ
        exact ⟨(σC', c), rfl, rfl, rfl, hJ⟩
      · rintro _ y σC' c σx c' σR - - hx hreg - - -
        cases y
        · exact .inl ⟨true, rfl, by show SO.le ⟨-72, []⟩ ⟨-80 - 0 + 8, []⟩ = true; decide, σx, hx, hreg⟩
        · refine .inr ⟨(), rfl, by show SO.le ⟨-224, []⟩ ⟨-80 - 0 + -144, []⟩ = true; decide, ?_⟩
          show σR.regs.get64 .rdi = 4
          rw [hreg]; exact hx.1
    case true =>
      refine (hello1_main_exit_segW hp hend (n := mS1R lab Jw) rfl rfl hK hF hR (by omega) (by omega) hW.exit
        fun s c σ0 hJ0 hAt => ?_).mono_pre
        fun _ _ h => At.rbp_addr h fun σ c hJ0 => by
          obtain ⟨σx, hJ, hr⟩ := hJ0
          show σ.regs.get64 .rbp = _
          simp only [Reg64s.get64, hr]
          exact hbpw σx c hJ
      obtain ⟨σx, hJ, hr⟩ := hJ0
      rw [hr]
      exact hok s c σx hJ hAt

end MainPost

/-! ## From the allocator's fresh-label landing to `scc_rt_main` after it

`hello1_main_pre_segW` ends at an allocation's continuation `ms.xa`
(`hxa`); `hello1_main_post_segW` starts at `wc_rodata`'s `.x13` in its
region. The bridge leaves the allocator's region (`at_leave`) and lands at
`.x13` for an invariant `Jp` the landing implies (`hJp`), so the choice of
`ms.xa` stays the instance's. -/

section MainBridge

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The allocator's fresh-label landing is at `wc_rodata`'s `.x13`**, in
its region at `scc_rt_main`'s call (caller's state `m0`, `σC`): from the
continuation node `Ea` in the allocator's region, under a frame condition
`F'` the call hands it (as in `hello1_main_pre_segW`'s `hxa`), the state is
at `rdX13` of an invariant `Jp` every landing's state left to `wc_rodata`
satisfies (`hJp`, of the allocator's state, `wc_rodata`'s at the call, and
the call's control). -/
theorem hello1_main_xa_post {J Jp : AS → Ctl → Prop} {m0 : MachineData} {σC : AS}
    {q : AG ms (_root_.Executable.labels exe).label} {F' : MachineData → Prop}
    {l : WeakMem.AllocLabel} {b w : Nat}
    (hFF : ∀ m, F' m → mF R F m0 σC m)
    (hkeep : ∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
      (rN (_root_.Executable.labels exe).label (mR R)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC) .call).J σ c ∧
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c ∧
      CKept (mR R) (-48) (-160) 8 mC m)
    (hJp : ∀ σx σ c0 c, (Ea ms q.1 l b w).J σx c →
      (rN (_root_.Executable.labels exe).label (mR R)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC) .call).J σ c0 →
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0 →
      Jp (leave (aR (mR R)) (-48) σ σx) c)
    {s : State} {c : Ctl} (h : At exe endPc (aR (mR R)) F' (Ea ms q.1 l b w) s c) :
    At exe endPc (mR R) (mF R F m0 σC) (rdX13 (_root_.Executable.labels exe).label Jp) s c := by
  have h' := at_leave (R := mR R) (kb := -48) (lo' := -160) (hi' := 8)
    (P := fun σ => ∃ c0,
      (rN (_root_.Executable.labels exe).label (mR R)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC) .call).J σ c0 ∧
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0)
    rfl (fun m hm => by
      obtain ⟨mC, σ, c0, hA, h1, h2, hK⟩ := hkeep m hm
      exact ⟨hFF m hm, mC, σ, _, hK, hA, c0, h1, h2⟩) h
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, σx, σ', hJx, ⟨c0, h1, h2⟩, rfl⟩ := h'
  refine ⟨he, hn, hdc, ?_, _, hA, hD, hJp σx σ' c0 c hJx h1 h2⟩
  rw [hpc]
  show Int64.ofBitVec q.1.ra = (_root_.Executable.labels exe).label ".Lwc_rodata.x13"
  rw [← h2.2.2.1]
  show Int64.ofBitVec (σ'.slot (-48 + 0)) = _
  rw [show (-48 : Int) + 0 = -48 by decide, h1.2.2.2.2.2, int64_ofBitVec_toBitVec]

/-- **`hello1_main_pre_segW`'s `hxa` from the landing at `.x13`**: if
every state at `wc_rodata`'s `.x13` in its region, for some caller's state
`m0`, `σC` at the call (of an invariant `Jp m0 σC` the landings imply,
`hJp`), is one a fresh label's allocation continues in (`hpost`), the
allocator's landings are (`hello1_main_xa_post`). -/
theorem hello1_main_hxa_of_post {J : AS → Ctl → Prop} {Jp : MachineData → AS → AS → Ctl → Prop}
    (hJp : ∀ m0 σC (q : AG ms (_root_.Executable.labels exe).label) l b w σx σ c0 c, (Ea ms q.1 l b w).J σx c →
      (rN (_root_.Executable.labels exe).label (mR R)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC) .call).J σ c0 →
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0 →
      Jp m0 σC (leave (aR (mR R)) (-48) σ σx) c)
    (hpost : ∀ l b w s c, lbl l = none → (∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
      (rdX13 (_root_.Executable.labels exe).label (Jp m0 σC)) s c) → ms.xa l b w s c) :
    ∀ m0 σC, ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF R F m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
        (rN (_root_.Executable.labels exe).label (mR R)
          (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC) .call).J σ c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR R) (-48) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR (mR R)) F' (Ea ms q.1 l b w) s c → ms.xa l b w s c :=
  fun m0 σC q _ hFF hkeep l b w _ _ hl h =>
    hpost l b w _ _ hl ⟨m0, σC, hello1_main_xa_post hFF hkeep (hJp m0 σC q l b w) h⟩

end MainBridge

/-! ## `scc_rt_main` as a whole

`hello1_main_pre_segW`, then `wc_rodata`'s `.x13` (the allocator's return
exit, `hret`), then `hello1_main_post_segW`; the allocation's continuation
`ms.xa` holds `.x13`'s states (`hpost`, through the bridge), which the
second segment covers. -/

/-- **`hello1_main_post_segW`'s premises** past the layout's, for a
caller's state `m0`, `σC` at `wc_rodata`'s call: the states inside `W`
(`hW`), and the source and frame facts named there. -/
structure MainPostP (W : Frag isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (m0 : MachineData) (σC : AS) (Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop) : Prop where
  hW : MainPostW W K exe endPc R F ms m0 σC Jp J1 J2 J3 J4 Jr Jw
  hbp : ∀ σ0 c, Jp σ0 c → σ0.regs.get64 .rbp = (mR R).addr (-8)
  hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".Lscc_rt_main.x2" = Int64.ofBitVec (σ0.slot 0)
  hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (bAddr σ0.regs .rax i) 8 = none
  h1 : ∀ σ0 c, Jp σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((bAddr σ0.regs .rax 0).toNat, w') }
  h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  h3 : ∀ σ0 c, J2 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((bAddr σ0.regs .rax 8).toNat, w') }
  h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  hedge : ∀ σ0 c, J4 σ0 c → ∀ σ' : AS, σ'.regs.rax.toBitVec = σ0.regs.rax.toBitVec →
      σ'.regs.rdx.toBitVec = 0#64 → σ'.regs.rcx.toBitVec = 2#64 → σ'.regs.rsi.toBitVec = 13#64 →
      σ'.regs.rbp.toBitVec = σ0.slot (-8) → σ'.regs.rsp.toBitVec = σ0.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ Jr σ' c'
  hbpr : ∀ σx c, Jr σx c → σx.regs.get64 .rbp = R.addr (-8)
  hlimW : ∀ σx c, Jr σx c → LimOk ms F (σx.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σx.regs.rsp.toBitVec - 8#64 - 8#64 - (80 : Int64).toBitVec)
  hsvc : ∀ F' : MachineData → Prop, FStable (pR (wR R)) F' →
      (∀ m, F' m → ((F m ∧ CallerCells R (-80) (-144) 8 m) ∧ CallerCells (wR R) (-96 - 8) (-40) 16 m) ∧
        Spike.Lib.X64.Rt.WcRa (wR R) ((_root_.Executable.labels exe).label ".Lscc_rt_main.x3") m ∧
        Spike.Lib.X64.Rt.WcFp (wR R) (R.addr (-8)) m) →
      ∀ g' : PG, g'.2.2 = ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec →
      g'.2.1 = (wR R).addr (-8) →
      SegW W K p lbl ms
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .sys))
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .n5))
  hedgeW : ∀ g : AS × Ctl, ∀ σ c, wcJ (wJ0 (_root_.Executable.labels exe).label σC Jr g) σ c →
      σ.regs.get64 .rbp = (wR R).addr (-8) → ∀ σ' : AS,
      (∀ k, -88 ≤ k → k < 8 → k % 8 = 0 → σ'.slot k = wcSl (_root_.Executable.labels exe).label σ k) →
      σ'.regs.rax.toBitVec = 0#64 → σ'.regs.rbp.toBitVec = σ.slot (-8) →
      σ'.regs.rsp.toBitVec = σ.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ Jw σ' c'
  hbpw : ∀ σx c, Jw σx c → σx.regs.get64 .rbp = R.addr (-8)
  hok : ∀ s c σx, Jw σx c →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lscc_rt_main.x3" + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, mO, fun _ _ => True⟩ s c → SysOk p ms s c (.exitGroup σx.regs.rax.toNat)

section MainAll

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` is two segments inside `W`** in any valid layout of
`hello1Cells`, for invariants at `wc_rodata`'s `.x13` and after indexed by
the caller's state `m0`, `σC` at its call. First, from its entry
(invariant `J`) to `print`'s abort or the allocator's heap abort
(`hello1_main_pre_segW`: `hlimM`, `hlimR`, `hq`, `hmem`; the allocator's
return at `.x13` continuing by `hret` into `hello1_main_post_segW`, of
premises `hP`). Second, from `.x13`'s states (of `Jp`) to `print`'s abort:
the states an allocation of a fresh label continues in. The allocation's
continuation `ms.xa` stays the instance's: it holds `.x13`'s states
(`hpost`), which every landing is (`hJp`, `hello1_main_hxa_of_post`).
VACUOUS at .x13 at `rodata`'s source: see X64Hello1RodataSetupG (`hand_x13_empty`). -/
theorem hello1_main_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi)
    {J : AS → Ctl → Prop} {Jp J1 J2 J3 J4 Jr Jw : MachineData → AS → AS → Ctl → Prop}
    (hW : MainPreW W K exe endPc R F ms J)
    (hlimM : ∀ σ c, J σ c → LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec))
    (hlimR : ∀ σ c, J σ c → LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - 64#64 - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hq : ∀ σ c, J σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ms = 3#64)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hJp : ∀ m0 σC (q : AG ms (_root_.Executable.labels exe).label) l b w σx σ c0 c, (Ea ms q.1 l b w).J σx c →
      (rN (_root_.Executable.labels exe).label (mR R)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC) .call).J σ c0 →
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0 →
      Jp m0 σC (leave (aR (mR R)) (-48) σ σx) c)
    (hpost : ∀ l b w s c, lbl l = none → (∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
      (rdX13 (_root_.Executable.labels exe).label (Jp m0 σC)) s c) → ms.xa l b w s c)
    (hret : ∀ m0 σC σ c,
      (rX ms (_root_.Executable.labels exe).label lbl (mR R)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC) .x13).J σ c →
      Jp m0 σC σ c)
    (hP : ∀ m0 σC, MainPostP W K p lbl ms exe endPc R F m0 σC (Jp m0 σC) (J1 m0 σC) (J2 m0 σC) (J3 m0 σC)
      (J4 m0 σC) (Jr m0 σC) (Jw m0 σC)) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (fun s c => At exe endPc R F (mAb (_root_.Executable.labels exe).label) s c ∨
        ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
          (rX ms (_root_.Executable.labels exe).label lbl (mR R)
            (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC) .abort) s c) ∧
    SegW W K p lbl ms
      (fun s c => ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
        (rdX13 (_root_.Executable.labels exe).label (Jp m0 σC)) s c)
      (At exe endPc R F (mAb (_root_.Executable.labels exe).label)) := by
  have hS : SegW W K p lbl ms
      (fun s c => ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
        (rdX13 (_root_.Executable.labels exe).label (Jp m0 σC)) s c)
      (At exe endPc R F (mAb (_root_.Executable.labels exe).label)) :=
    SegW.exists_pre fun m0 => SegW.exists_pre fun σC =>
      let h := hP m0 σC
      hello1_main_post_segW hp hend hF hR hlo hhi hK h.hW h.hbp h.hra h.hmem h.h1 h.h2 h.h3 h.h4 h.hedge h.hbpr
        h.hlimW h.hsvc h.hedgeW h.hbpw h.hok
  refine ⟨SegW.seq_left ((hello1_main_pre_segW hp hend hF hR hlo hhi hW hlimM hlimR hq hmem
    (hello1_main_hxa_of_post hJp hpost)).mono_post ?_) hS, hS⟩
  rintro s c ⟨m0, σC, y, h⟩
  cases y
  · obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
    exact .inl ⟨m0, σC, he, hn, hdc, hpc, σ, hA, hD, hret m0 σC σ c hJ⟩
  · exact .inr ⟨m0, σC, h⟩

end MainAll

end Spike.Lib.X64.Flow.Hello1
