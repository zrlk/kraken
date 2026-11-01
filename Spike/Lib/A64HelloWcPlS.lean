/-
**hello.w's `wc_main` placed up to the box's store, at the state** (AArch64; the
state-dependent twin of `A64HelloWcPl`, as `RdPlS` is of `RdPl`): `MainWcPS.hWp`'s/`hWs`'s placement `hpl`
at level 1 (`MainWcL1Wp.hWp_L1G`/`hWs_L1G`), at no frame.

`wc_main`'s controls up to the box's store are not one control placed at every state (`WcPl`'s route): from its
entry to the entry block's call they are `wc_rodata`'s return's, the setup continuation on rodata's slice
(`setupCont`, free variables `r`, `me`); from the allocator on, `c0H`'s (free variables `z`, `sl`, `me`; `z` the
layout's immediate `0`). Their words live at the state:
- the slice `[loc l, 2, 13]` in `x0`, `x2`, `x3` at the entry (`HelloJr1.SlRegs`), kept by the prologue, spilled at
  `-144`, `-128`, `-120` (`HelloWc.wcJH`), no later block storing there;
- `me` in `x4` at the entry (`mWC`: the caller's slot `-80`), spilled at `-112`;
- in the allocator, the caller's slots, outside its region (`CKept`, `DFrame`; `allocW_placedS`, the all-slots
  variant of `PlacedAlloc.allocW_placedG`).

- `placedSE_cont`, `placedSE_c0H`: the two controls placed at any four places of their words.
- `entry_wcJ0`: `wc_main`'s entry registers are the caller's `Jr`-state's, `x4` the caller's slot `-80`.
- `PlE`, `plE_cont`, `plE_c0H`: an entry invariant's controls placed wherever four places read its state's `x0`,
  `x2`, `x3`, `x4`; at `J0` (the setup continuation) and `J1` (`c0H`).
- `plE_regs`, `plE_slots`, `off_spills`: placed at the registers as the entry's, at the spills `-144`, `-128`,
  `-120`, `-112`.
- `proW_pl`: the prologue (it writes none of the four registers).
- `allocW_placedS`, `allocW_placedS_wcH`: the allocator's states placed, given the call state's slots.
- `hplP_S`, `hplS_S`: `WcPreWH`/`WcSp0WH` inside the placement.

No absolute address appears in this file.
-/
import Spike.Lib.A64HelloPlacedAlloc
import Spike.Lib.A64HelloWcSp0
import Spike.Lib.A64HelloJr1
import Spike.Lib.A64HelloRdCf
import Spike.Lib.A64WakeSrcCtl
import Spike.Lib.A64WakeMainW
import Spike.Lib.A64WakeWcWf

namespace Spike.Lib.A64.HelloPh.WcPlS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (Region Ctl MemSide)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND BlkW NodeW)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcJ0)
open Spike.Lib.A64.Flow.HelloWc (WcPreWH WcSp0WH wARH WcCtxH wcJH wNH sNH wcEH wcS0H)
open Spike.Lib.A64.Flow.HelloJr1 (SlRegs)
open Spike.Lib.A64.Alloc (Call AllocW N)
open Spike.Lib.A64WakeMainW (M1 placeVal_x placeVal_cell)
open Spike.Lib.WakeSrcCtl (keepsSlot arun_slot_keep placeVal_slot_abs)
open Spike.Lib.HelloMainPreSrc (c0H newTerm)
open Spike.Lib.HelloRdCf (slW)
open Spike.Lib.A64.WakePh.PlacedAlloc (placedSE_congr allocN_ctl)

/-- The machine's places. -/
local notation "PlM" => Place M1.I.RegId

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State}

/-! ## The two controls at any places -/

/-- **The setup continuation on rodata's slice placed**: `r`'s words `slW l` at `p0`, `p2`, `p3` (the slice's
`x0`, `x2`, `x3`), `me`'s word `mw` at `pm`. -/
theorem placedSE_cont {l : WeakMem.AllocLabel} {env : TermRun.Env} {ty : Ty} {mw : TermRun.Word}
    {h : Option (Nat × TermRun.Word)} (hmeE : TermRun.lookupE env "me" = some (.tid, [mw])) (p0 p2 p3 pm : PlM)
    (h0 : ∃ v, placeVal (machine (kernel 1)) s p0 = some v ∧ lbl l = some v)
    (h2 : placeVal (machine (kernel 1)) s p2 = some 2) (h3 : placeVal (machine (kernel 1)) s p3 = some 13)
    (hm : ∃ v, placeVal (machine (kernel 1)) s pm = some v ∧ ValRep lbl mw.val v) :
    PlacedSE Λ lbl s ⟨SrcCalls.setupCont, ("r", ty, slW l) :: env, h⟩ [] := by
  have hr : TermRun.lookupE (("r", ty, slW l) :: env) "r" = some (ty, slW l) := by simp [TermRun.lookupE]
  have hme : TermRun.lookupE (("r", ty, slW l) :: env) "me" = some (.tid, [mw]) := by
    unfold TermRun.lookupE at hmeE ⊢; rw [List.find?_cons_of_neg (by simp)]; exact hmeE
  refine Spike.Lib.WakeSrcCtl.placedSE_of_tbl [("r", [.one p0, .one p2, .one p3]), ("me", [.one pm])] ?_ ?_ ?_
  · intro x hx ty' ws hl
    rw [show exprFv SrcCalls.setupCont = ["r", "me"] by decide] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [hr] at hl; cases hl; exact ⟨_, rfl, by simp [slW]⟩
    · rw [hme] at hl; cases hl; exact ⟨_, rfl, by simp⟩
  · intro x pls ty' ws hpl hl k wp wd hwp hwd
    by_cases er : x = "r"
    · subst er; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      rw [hr] at hl; cases hl
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact Spike.Lib.WakeSrcCtl.rep_at h0
      | 1, hwp, hwd => cases hwp; cases hwd; exact ⟨_, h2, by decide, rfl⟩
      | 2, hwp, hwd => cases hwp; cases hwd; exact ⟨_, h3, by decide, rfl⟩
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      rw [hme] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact hm
    · simp [List.lookup, beq_false_of_ne er, beq_false_of_ne em] at hpl
  · intro x pls k n hpl hn
    by_cases er : x = "r"
    · subst er; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      match k, hn with
      | 0, hn => cases hn
      | 1, hn => cases hn
      | 2, hn => cases hn
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      match k, hn with | 0, hn => cases hn
    · simp [List.lookup, beq_false_of_ne er, beq_false_of_ne em] at hpl

/-- **`c0H` placed**: `z` at the layout's immediate `0` (`hz`), `sl`'s words at `p0`, `p2`, `p3`, `me`'s at `pm`. -/
theorem placedSE_c0H {w0 w1 w2 mw : TermRun.Word} (hz : Λ.imms newTerm "z" 0 = some 0) (p0 p2 p3 pm : PlM)
    (h0 : ∃ v, placeVal (machine (kernel 1)) s p0 = some v ∧ ValRep lbl w0.val v)
    (h1 : ∃ v, placeVal (machine (kernel 1)) s p2 = some v ∧ ValRep lbl w1.val v)
    (h2 : ∃ v, placeVal (machine (kernel 1)) s p3 = some v ∧ ValRep lbl w2.val v)
    (hm : ∃ v, placeVal (machine (kernel 1)) s pm = some v ∧ ValRep lbl mw.val v) :
    PlacedSE Λ lbl s (c0H w0 w1 w2 mw) [] := by
  have hzl : TermRun.lookupE (c0H w0 w1 w2 mw).env "z" = some (.int, [TermRun.cst (.num 0)]) := rfl
  have hsl : TermRun.lookupE (c0H w0 w1 w2 mw).env "sl" =
      some (Spike.Lib.HelloMainPreSrc.slTy, [w0, w1, w2]) := rfl
  have hme : TermRun.lookupE (c0H w0 w1 w2 mw).env "me" = some (.tid, [mw]) := rfl
  refine Spike.Lib.WakeSrcCtl.placedSE_of_tbl
    [("z", [.imm 0]), ("sl", [.one p0, .one p2, .one p3]), ("me", [.one pm])] ?_ ?_ ?_
  · intro x hx ty ws hl
    rw [show (c0H w0 w1 w2 mw).term = newTerm from rfl,
      show exprFv newTerm = ["z", "sl", "me"] by decide] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [hzl] at hl; cases hl; exact ⟨_, rfl, by simp⟩
    · rw [hsl] at hl; cases hl; exact ⟨_, rfl, by simp⟩
    · rw [hme] at hl; cases hl; exact ⟨_, rfl, by simp⟩
  · intro x pls ty ws hpl hl k wp wd hwp hwd
    by_cases ez : x = "z"
    · subst ez; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      rw [hzl] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact ⟨by decide, rfl⟩
    by_cases es : x = "sl"
    · subst es; simp [List.lookup] at hpl; subst hpl
      rw [hsl] at hl; cases hl
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact h0
      | 1, hwp, hwd => cases hwp; cases hwd; exact h1
      | 2, hwp, hwd => cases hwp; cases hwd; exact h2
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      rw [hme] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact hm
    · simp [List.lookup, beq_false_of_ne ez, beq_false_of_ne es, beq_false_of_ne em] at hpl
  · intro x pls k n hpl hn
    by_cases ez : x = "z"
    · subst ez; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      match k, hn with | 0, hn => cases hn; exact hz
    by_cases es : x = "sl"
    · subst es; simp [List.lookup] at hpl; subst hpl
      match k, hn with
      | 0, hn => cases hn
      | 1, hn => cases hn
      | 2, hn => cases hn
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      match k, hn with | 0, hn => cases hn
    · simp [List.lookup, beq_false_of_ne ez, beq_false_of_ne es, beq_false_of_ne em] at hpl

/-! ## At `wc_main`'s entry -/

/-- **`wc_main`'s entry registers**: those of a state of the caller's `Jr` at the same control, `x4` the caller's
slot `-80` (`mWC`). -/
theorem entry_wcJ0 {lab : Label → Int64} {σC σ1 : Flow.AS} {Jx : Flow.AS → Ctl → Prop} {σ : Flow.AS} {c : Ctl}
    (h : wcJ0 (mWC lab σC Jx).J σ1 σ c) :
    ∃ σx, Jx σx c ∧ σ.regs.X0 = σx.regs.X0 ∧ σ.regs.X2 = σx.regs.X2 ∧ σ.regs.X3 = σx.regs.X3 ∧
      σ.regs.X4.toBitVec = σC.slot (-80) := by
  obtain ⟨rfl, σx, hJ, h0, -, h2, h3, h4, -⟩ := h
  exact ⟨σx, hJ, h0, h2, h3, h4⟩

/-- **A control placed at an entry state's four registers**: each control of `J` is placed wherever four places
read its state's `x0`, `x2`, `x3`, `x4`. -/
def PlE (Λ : Scc.Sem.Layout) (lbl : Lbl) (J : Flow.AS → Ctl → Prop) : Prop :=
  ∀ σ c, J σ c → ∀ (s : State) (p0 p2 p3 p4 : PlM), placeVal M1 s p0 = some σ.regs.X0.toBitVec.toNat →
    placeVal M1 s p2 = some σ.regs.X2.toBitVec.toNat → placeVal M1 s p3 = some σ.regs.X3.toBitVec.toNat →
    placeVal M1 s p4 = some σ.regs.X4.toBitVec.toNat → PlacedSE Λ lbl s c []

section Entry

variable {lab : Label → Int64} {σC σ1 : Flow.AS} {l : WeakMem.AllocLabel} {mw : TermRun.Word}

/-- **The setup continuation at `wc_main`'s entry placed** (`PlE`): the caller's `Jr` is at the continuation on
`slW l` with the slice's registers (`hJr`), `me`'s word represented by the caller's slot `-80` (`hme`). -/
theorem plE_cont {Jr : Flow.AS → Ctl → Prop} {env : TermRun.Env}
    (hmeE : TermRun.lookupE env "me" = some (.tid, [mw])) (hme : ValRep lbl mw.val (σC.slot (-80)).toNat)
    (hJr : ∀ σ c, Jr σ c → c = ⟨SrcCalls.setupCont, ("r", Spike.Lib.HelloMainPreSrc.slTy, slW l) :: env, none⟩ ∧
      SlRegs lbl l σ) :
    PlE Λ lbl (wcJ0 (mWC lab σC Jr).J σ1) := by
  intro σ c hj s p0 p2 p3 p4 r0 r2 r3 r4
  obtain ⟨σx, hJx, e0, e2, e3, e4⟩ := entry_wcJ0 hj
  obtain ⟨rfl, hl, -, hx2, hx3⟩ := hJr σx c hJx
  exact placedSE_cont hmeE p0 p2 p3 p4 ⟨_, r0, by rw [e0]; exact hl⟩ (by rw [r2, e2, hx2]) (by rw [r3, e3, hx3])
    ⟨_, r4, by rw [e4]; exact hme⟩

/-- **`c0H` at `wc_main`'s entry placed** (`PlE`): the caller's `Jr1` is at `c0H` on `slW l`'s words and `mw`
with the slice's registers (`hJ1`, `Land.Jr1LH`). -/
theorem plE_c0H {Jr1 : Flow.AS → Ctl → Prop} (hz : Λ.imms newTerm "z" 0 = some 0)
    (hme : ValRep lbl mw.val (σC.slot (-80)).toNat)
    (hJ1 : ∀ σ c, Jr1 σ c → c = c0H (TermRun.cst (.loc ⟨l, 0⟩ 0)) (TermRun.cst (.num 2)) (TermRun.cst (.num 13)) mw ∧
      SlRegs lbl l σ) :
    PlE Λ lbl (wcJ0 (mWC lab σC Jr1).J σ1) := by
  intro σ c hj s p0 p2 p3 p4 r0 r2 r3 r4
  obtain ⟨σx, hJx, e0, e2, e3, e4⟩ := entry_wcJ0 hj
  obtain ⟨rfl, hl, -, hx2, hx3⟩ := hJ1 σx c hJx
  exact placedSE_c0H hz p0 p2 p3 p4 (Spike.Lib.WakeSrcCtl.rep_at ⟨_, r0, by rw [e0]; exact hl⟩)
    ⟨_, r2, by decide, by rw [e2, hx2]⟩ ⟨_, r3, by decide, by rw [e3, hx3]⟩ ⟨_, r4, by rw [e4]; exact hme⟩

end Entry

/-! ## Reading the entry's words -/

/-- The four registers the placement reads. -/
def KR (r : XReg) : Prop := r = .X0 ∨ r = .X2 ∨ r = .X3 ∨ r = .X4

/-- **Placed at registers as the entry's**: at a state whose `x0`, `x2`, `x3`, `x4` are an entry state's. -/
theorem plE_regs {J : Flow.AS → Ctl → Prop} (hP : PlE Λ lbl J) {σ : Flow.AS} {c : Ctl} (hJ : J σ c) (s : State)
    (h : ∀ r, KR r → s.st.1.regs.getXReg r = σ.regs.getXReg r) : PlacedSE Λ lbl s c [] :=
  hP σ c hJ s _ _ _ _ (by rw [placeVal_x, h _ (.inl rfl)]; try rfl)
    (by rw [placeVal_x, h _ (.inr (.inl rfl))]; try rfl) (by rw [placeVal_x, h _ (.inr (.inr (.inl rfl)))]; try rfl)
    (by rw [placeVal_x, h _ (.inr (.inr (.inr rfl)))]; try rfl)

/-- `wc_main`'s spill slots of the entry's `x0`, `x2`, `x3`, `x4`. -/
abbrev spills : List Int := [-144, -128, -120, -112]

/-- **Placed at the spills**: at a state whose cells at the spill slots are a frame's (`wcJH`). -/
theorem plE_slots {J : Flow.AS → Ctl → Prop} (hP : PlE Λ lbl J) {R : Region} {σ : Flow.AS} {c : Ctl}
    (hJ : wcJH J σ c) (s : State)
    (h : ∀ k ∈ spills, placeVal M1 s (.slot (R.addr k).toNat) = some (σ.slot k).toNat) : PlacedSE Λ lbl s c [] := by
  obtain ⟨σe, hJe, -, -, h144, -, h128, h120, h112⟩ := hJ
  exact hP σe c hJe s _ _ _ _ (by rw [h (-144) (by simp), h144]) (by rw [h (-128) (by simp), h128])
    (by rw [h (-120) (by simp), h120]) (by rw [h (-112) (by simp), h112])

/-- The spill slots are in a region reaching `-144`, at or above the frame's bottom. -/
theorem off_spills {R : Region} (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) : ∀ k ∈ spills, R.Off k ∧ -144 ≤ k := by
  intro k hk
  simp only [spills, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> exact ⟨⟨by decide, by omega, by omega⟩, by decide⟩

/-! ## The prologue -/

section Pro

set_option linter.unusedSimpArgs false

open Spike.Lib.A64.Flow (AM chkHead chkBr frameSet frSetup spStr chkRegs ldStep ProW arun_take_reg)

variable {lab : Label → Int64}

/-- `KR` kept by the stack check's head. -/
theorem keep_chkHead (Z : Int64) (r : XReg) (hr : KR r) :
    ∀ d ∈ chkHead Z, ∀ am : AM, (Spike.Lib.A64.Flow.dstep lab am d).σ.regs.getXReg r = am.σ.regs.getXReg r := by
  simp only [chkHead, List.mem_cons, List.not_mem_nil, or_false]
  rcases hr with rfl | rfl | rfl | rfl <;> rintro d (rfl | rfl) ⟨pc, o, σ⟩ <;> dstep_keep <;>
    (try simp [Spike.Lib.rm, Spike.Lib.A64.Flow.regDst])

/-- `KR` kept by the stack check's branch. -/
theorem keep_chkBr (L : Label) (r : XReg) (hr : KR r) :
    ∀ d ∈ chkBr L, ∀ am : AM, (Spike.Lib.A64.Flow.dstep lab am d).σ.regs.getXReg r = am.σ.regs.getXReg r := by
  simp only [chkBr, List.mem_cons, List.not_mem_nil, or_false]
  rcases hr with rfl | rfl | rfl | rfl <;> rintro d (rfl | rfl) ⟨pc, o, σ⟩ <;> dstep_keep <;>
    (try simp [Spike.Lib.rm, Spike.Lib.A64.Flow.regDst])

/-- `KR` kept by the frame's set-up and the parameters' stores. -/
theorem keep_frameSet (Z : Int64) (ps : List (XReg × Int64)) (r : XReg) (hr : KR r) :
    ∀ d ∈ frameSet Z ps, ∀ am : AM, (Spike.Lib.A64.Flow.dstep lab am d).σ.regs.getXReg r = am.σ.regs.getXReg r := by
  intro d hd am
  simp only [frameSet, List.mem_append, List.mem_map] at hd
  rcases hd with hd | ⟨q, -, rfl⟩
  · simp only [frSetup, List.mem_cons, List.not_mem_nil, or_false] at hd
    obtain ⟨pc, o, σ⟩ := am
    rcases hd with rfl | rfl | rfl | rfl
    all_goals
      simp only [Spike.Lib.A64.Flow.dstep, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly,
      Spike.Lib.A64.Flow.AI.so, Spike.Lib.A64.Flow.AI.step, Spike.Lib.A64.Flow.AI.tgt, Spike.Lib.A64.Flow.soReg,
      Spike.Lib.A64.Flow.regRes, spStr, Reg64s.getRegOrZr_X, Operation.interp, MachineData.setRegOrSp,
      Reg64s.setRegOrSp, Reg64s.setRegOrSp64, ConstExpr.interp, Spike.Lib.A64.Flow.SO.set, ExtOrImmReg.interp,
      Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, Spike.Lib.A64.Flow.SO.get, MachineData.setRegOrZr,
      Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Spike.Lib.A64.Flow.zrB, Spike.Lib.A64.Flow.SO.write,
      Spike.Lib.A64.Flow.SO.kill, Spike.Lib.A64.Flow.SO.killZ, Spike.Lib.rm, Spike.Lib.A64.Flow.regDst]
    all_goals rcases hr with rfl | rfl | rfl | rfl <;> rfl
  · obtain ⟨pc, o, σ⟩ := am
    rw [Spike.Lib.A64.Flow.dstep_spStr]

theorem keep_chkRegs (Z : Int64) (rr : Reg64s) (r : XReg) (hr : KR r) :
    (chkRegs Z rr).getXReg r = rr.getXReg r := by
  rcases hr with rfl | rfl | rfl | rfl <;> rfl

theorem keep_ldStep (v : BitVec 64) (σ : Flow.AS) (r : XReg) (hr : KR r) :
    (ldStep .X10 v σ).regs.getXReg r = σ.regs.getXReg r := by
  rcases hr with rfl | rfl | rfl | rfl <;> rfl

/-- **A prologue inside the placement** from its entry's (`PlE`): the prologue writes none of `x0`, `x2`, `x3`,
`x4` (`chkRegs`, the limit's load into `x10`, the check's branch, the frame's set-up). -/
theorem proW_pl {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)} {J : Flow.AS → Ctl → Prop}
    (hP : PlE Λ lbl J) :
    ProW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps J := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
    refine ⟨plE_regs hP hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.getXReg _ = _
    rw [hA'.regs, arun_take_reg r (keep_chkHead Z r hr) k]
  · rintro s c ⟨-, -, -, -, σ1, hA, -, σ, hJ, rfl⟩
    refine ⟨plE_regs hP hJ _ fun r hr => ?_, fun _ h => h⟩
    rw [hA.regs]
    exact keep_chkRegs Z σ.regs r hr
  · rintro s σ2 c _ _ _ _ _ _ ⟨σ, v, hJ, -, rfl⟩ k _ m hA' _
    refine ⟨plE_regs hP hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.getXReg _ = _
    rw [hA'.regs, arun_take_reg r (keep_chkBr L r hr) k, keep_ldStep _ _ r hr]
    exact keep_chkRegs Z σ.regs r hr
  · rintro s σ3 c _ _ _ _ _ _ ⟨σ, v, hJ, -, he, -⟩ k _ m hA' _
    refine ⟨plE_regs hP hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.getXReg _ = _
    rw [hA'.regs, arun_take_reg r (keep_frameSet Z ps r hr) k, he, keep_ldStep _ _ r hr]
    exact keep_chkRegs Z σ.regs r hr

end Pro

/-! ## The allocator, at the call state's slots -/

section Alloc

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2}
  {q : Call} {fr : Int}

set_option hygiene false in
/-- The placement at the labels `lbl`, no frame. -/
local notation "PL" => fun s c => PlacedSE Λ lbl s c []

/-- **The caller's source placed at every node of `scc_rt_alloc`**, called at frame `fr`, given every caller
slot at or above the frame's bottom (the all-slots variant of `PlacedAlloc.allocW_placedG`). -/
theorem allocW_placedS {Jn : Flow.AS → Ctl → Prop} (hR : R.OK) (hlo : R.lo ≤ fr) (hfr : fr < 0) (hhi : 0 ≤ R.hi)
    (hP : ∀ σC, (∃ mC, Flow.Abs R ⟨fr, []⟩ mC σC) → Jn σC q.c0 → ∀ s : State,
      (∀ k, R.Off k → fr ≤ k → placeVal M1 s (.slot (R.addr k).toNat) = some (σC.slot k).toNat) →
        PlacedSE Λ lbl s q.c0 []) :
    AllocW ms q (PL) (fun _ _ => False) exe endPc (R.callee fr (-160) 0)
      (fun m => F m ∧ Spike.Lib.A64.Flow.Ret0.CallerCells R fr (-160) 0 m ∧
        PlacedAlloc.CtxG ms (_root_.Executable.labels exe).label R fr Jn q m) := by
  have hin : ∀ {m' : MachineData}, (F m' ∧ Spike.Lib.A64.Flow.Ret0.CallerCells R fr (-160) 0 m' ∧
      PlacedAlloc.CtxG ms (_root_.Executable.labels exe).label R fr Jn q m') → ∀ {s : State},
      Flow.DFrame (R.callee fr (-160) 0) m' s.st.1 → PlacedSE Λ lbl s q.c0 [] := by
    intro m' hF s hD
    obtain ⟨-, -, mC, σC, c, hA, hJ, ⟨rfl, -⟩, hK⟩ := hF
    exact hP σC ⟨mC, hA⟩ hJ s fun k hk hk' => PlacedAlloc.placeVal_slot_keptG hA hK hD hR hlo hfr hhi hk hk'
  have hB : ∀ i blk, BlkW (PL) (fun _ _ => False) exe endPc (R.callee fr (-160) 0)
      (fun m => F m ∧ Spike.Lib.A64.Flow.Ret0.CallerCells R fr (-160) 0 m ∧
        PlacedAlloc.CtxG ms (_root_.Executable.labels exe).label R fr Jn q m)
      (N (_root_.Executable.labels exe).label ms q i) blk := by
    intro i blk s σ c _ _ _ _ _ hF hj _ _ m _ hD
    obtain ⟨ht, he⟩ := allocN_ctl i σ c hj
    exact ⟨placedSE_congr ht he (hin (s := { s with st := (m, _) }) hF hD), fun _ h => h⟩
  have hN : ∀ i, NodeW (PL) (fun _ _ => False) exe endPc (R.callee fr (-160) 0)
      (fun m => F m ∧ Spike.Lib.A64.Flow.Ret0.CallerCells R fr (-160) 0 m ∧
        PlacedAlloc.CtxG ms (_root_.Executable.labels exe).label R fr Jn q m)
      (N (_root_.Executable.labels exe).label ms q i) := by
    rintro i s c ⟨-, -, -, -, σ, -, hF, hj⟩
    obtain ⟨ht, he⟩ := allocN_ctl i σ c hj
    exact ⟨placedSE_congr ht he (hin hF (Flow.DFrame.refl _ _)), fun _ h => h⟩
  exact ⟨hB _ _, hB _ _, hB _ _, hN _, hN _, hB _ _, hN _, hB _ _, hB _ _, hB _ _, hB _ _, hB _ _, hB _ _, hN _,
    hN _, hB _ _, hN _, hB _ _, hN _⟩

/-- **`wc_main`'s box call placed** (frame 144): the call's controls are `J1`'s, placed at the spills (`PlE`). -/
theorem allocW_placedS_wcH {J0 J1 : Flow.AS → Ctl → Prop} (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (hP : PlE Λ lbl J1) :
    AllocW ms q (PL) (fun _ _ => False) exe endPc (wARH R)
      (fun m => F m ∧ Spike.Lib.A64.Flow.Ret0.CallerCells R (-144) (-160) 0 m ∧
        WcCtxH ms (_root_.Executable.labels exe).label R J0 J1 q m) :=
  allocW_placedS hR hlo (by decide) hhi fun _ _ hJ s hsl =>
    plE_slots hP hJ.1 s fun k hk => hsl k (off_spills hlo hhi k hk).1 (off_spills hlo hhi k hk).2

end Alloc

/-! ## `wc_main` up to the box's store -/

/-- `wc_main`'s entry block keeps the spills. -/
theorem keeps_wcEH : ∀ k ∈ spills, keepsSlot k ⟨-144, []⟩ wcEH = true := by decide +kernel

/-- `.sp0`'s block keeps the spills. -/
theorem keeps_wcS0H : ∀ k ∈ spills, keepsSlot k ⟨-144, []⟩ wcS0H = true := by decide +kernel

section Wc

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2}

set_option hygiene false in
/-- The placement at the labels `lbl`, no frame. -/
local notation "PL" => fun s c => PlacedSE Λ lbl s c []

/-- **`wc_main` up to the allocator's return inside the placement** (`WcWfS.wcPreW_WSH`'s `hpl`): the entry's
controls placed at its four registers (`hP0`), the call's (`hP1`); the prologue keeps the registers, the entry
block and the allocator the spills. -/
theorem hplP_S {J0 J1 : Flow.AS → Ctl → Prop} (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (hP0 : PlE Λ lbl J0) (hP1 : PlE Λ lbl J1) : WcPreWH (PL) (fun _ _ => False) exe endPc R F ms J0 J1 := by
  refine ⟨proW_pl hP0, ?_, fun q _ _ => allocW_placedS_wcH hR hlo hhi hP1⟩
  intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
  refine ⟨plE_slots (R := R) hP0 hJ _ fun j hj => ?_, fun _ h => h⟩
  rw [placeVal_cell hA' (off_spills hlo hhi j hj).1 _ rfl]
  exact congrArg (fun v : BitVec 64 => some v.toNat) (arun_slot_keep _ j wcEH ⟨_, ⟨-144, []⟩, σ⟩ k (keeps_wcEH j hj))

/-- **`.sp0` inside the placement** (`WcWfS.wcSp0W_WSH`'s `hpl`): the call's controls placed at its four
registers (`hP1`), so `.sp0`'s, the hold aside, at the spills, kept by `.sp0`'s block. -/
theorem hplS_S {J1 : Flow.AS → Ctl → Prop} (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) (hP1 : PlE Λ lbl J1) :
    WcSp0WH (PL) (fun _ _ => False) exe endPc R F ms J1 := by
  refine ⟨?_, ?_⟩
  · intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
    obtain ⟨q, hw, o, rfl, -⟩ := hJ
    refine ⟨plE_slots (R := R) hP1 hw _ fun j hj => ?_, fun _ h => h⟩
    rw [placeVal_cell hA' (off_spills hlo hhi j hj).1 _ rfl]
    exact congrArg (fun v : BitVec 64 => some v.toNat)
      (arun_slot_keep _ j wcS0H ⟨_, ⟨-144, []⟩, σ⟩ k (keeps_wcS0H j hj))
  · rintro s c ⟨-, -, -, -, σ, hA, -, q, o, hw, rfl, -⟩
    exact ⟨plE_slots (R := R) hP1 hw _ fun j hj => placeVal_slot_abs hA (off_spills hlo hhi j hj).1, fun _ h => h⟩

end Wc

end Spike.Lib.A64.HelloPh.WcPlS

/-- info: 'Spike.Lib.A64.HelloPh.WcPlS.placedSE_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPlS.placedSE_cont

/-- info: 'Spike.Lib.A64.HelloPh.WcPlS.placedSE_c0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPlS.placedSE_c0H

/-- info: 'Spike.Lib.A64.HelloPh.WcPlS.entry_wcJ0' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPlS.entry_wcJ0

/-- info: 'Spike.Lib.A64.HelloPh.WcPlS.plE_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPlS.plE_cont

/-- info: 'Spike.Lib.A64.HelloPh.WcPlS.plE_c0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPlS.plE_c0H

/-- info: 'Spike.Lib.A64.HelloPh.WcPlS.plE_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPlS.plE_regs

/-- info: 'Spike.Lib.A64.HelloPh.WcPlS.plE_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPlS.plE_slots

/-- info: 'Spike.Lib.A64.HelloPh.WcPlS.off_spills' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPlS.off_spills

/-- info: 'Spike.Lib.A64.HelloPh.WcPlS.proW_pl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPlS.proW_pl

/-- info: 'Spike.Lib.A64.HelloPh.WcPlS.allocW_placedS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPlS.allocW_placedS

/-- info: 'Spike.Lib.A64.HelloPh.WcPlS.allocW_placedS_wcH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPlS.allocW_placedS_wcH

/-- info: 'Spike.Lib.A64.HelloPh.WcPlS.keeps_wcEH' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPlS.keeps_wcEH

/-- info: 'Spike.Lib.A64.HelloPh.WcPlS.keeps_wcS0H' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPlS.keeps_wcS0H

/-- info: 'Spike.Lib.A64.HelloPh.WcPlS.hplP_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPlS.hplP_S

/-- info: 'Spike.Lib.A64.HelloPh.WcPlS.hplS_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPlS.hplS_S
