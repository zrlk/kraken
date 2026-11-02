/-
**hello.w's `wc_main` placed up to the box's store, at the state** (x86-64; the twin of
`Spike/Lib/A64HelloWcPlS.lean`): `WcPreWH`'s and `WcSp0WH`'s placement `hpl` (the source placed at no frame,
`PlacedSE … []`), at the entry invariants `wc_main` is reached with.

`wc_main`'s controls up to the box's store are not one control placed at every state: from its entry to the entry
block's call they are `wc_rodata`'s return's, the setup continuation on rodata's slice (`setupCont`, free
variables `r`, `me`); from the allocator on, `c0H`'s (free variables `z`, `sl`, `me`; `z` the layout's immediate
`0`). Their words live at the state:
- the slice `[loc l, 2, 13]` in `%rdi`, `%rdx`, `%rcx` at the entry (`scc_rt_main` moved `wc_rodata`'s `%rax`,
  `%rcx`, `%rsi` there, `Hello1.mWC`; `HelloJr1.SlRegs`), kept by the prologue, spilled at `-16`, `-32`, `-40`
  (`HelloWc.wcJH`), no later block storing there;
- `me` in `%r8` at the entry (`mWC`: the caller's slot `-16`), spilled at `-48`;
- in the allocator, the caller's slots, outside its region (`CKept`, `DFrame`; `allocW_placedS`, the all-slots
  variant of `PlacedAlloc.allocW_placedG`).

- `placedSE_cont`, `placedSE_c0H`: the two controls placed at any four places of their words.
- `entry_wcJ0`: `wc_main`'s entry registers are the caller's `Jr`-state's, `%r8` the caller's slot `-16`.
- `PlE`, `plE_cont`, `plE_c0H`: an entry invariant's controls placed wherever four places read its state's `%rdi`,
  `%rdx`, `%rcx`, `%r8`; at the setup continuation and at `c0H`.
- `KR`, `plE_regs`, `spills`, `plE_slots`, `off_spills`: placed at the registers as the entry's, at the spills
  `-16`, `-32`, `-40`, `-48`.
- `wcPsH`, `keepK_pro`, `keepK_xS1`, `keepK_xS2`, `keepK_xS3`, `proW_pl`: the prologue (it writes none of the
  four registers).
- `allocW_placedS`, `allocW_placedS_wcH`: the allocator's states placed, given the call state's slots.
- `keeps_wcEH`, `keeps_wcS0H`, `hplP_S`, `hplS_S`: `WcPreWH`/`WcSp0WH` inside the placement.

No absolute address appears in this file.

## Differences from the AArch64 version

- The four registers are `%rdi`, `%rdx`, `%rcx`, `%r8` (AArch64: `x0`, `x2`, `x3`, `x4`; `%rsi` holds the slice's
  `0`, as `x1`), and `me` is the caller's slot `-16` (AArch64: `-80`).
- The spills are `wc_main`'s argument stores below the saved `%rbp`, the region's `-16`, `-32`, `-40`, `-48`
  (AArch64: `-144`, `-128`, `-120`, `-112` at the frame's base); a region reaching `-48` holds them.
- The prologue is x86-64's five-node `XProW` at `wc_main`'s frame (128, five stores); its blocks' prefixes keep the
  registers by one concrete lemma (`keepK_pro`, as `PlacedZ.keepA_pro`), the nodes' states by `keepK_xS1` ..
  `keepK_xS3` (AArch64: `keep_chkHead`, `keep_chkBr`, `keep_frameSet`, `keep_chkRegs`, `keep_ldStep`).
- The allocator's region reaches a word above the call node (`R.callee (-144) (-160) 8`), so the kept caller slots
  are those at `-136` or above (AArch64: `R.callee fr (-160) 0`, slots at `fr` or above); the nodes' controls come
  from `X64SetupPlaced.allocW_of_ctl`.
- The entry block's node is `Hello1.wJ R (wcJH J0)` (with `%rbp`'s fact) and its offsets `oWRH`; `.x22`'s exit
  carries `%rbp`'s fact before the allocator's return.
-/
import Spike.Lib.X64HelloPlacedAlloc
import Spike.Lib.X64HelloWcSp0
import Spike.Lib.X64HelloJr1
import Spike.Lib.X64HelloMain
import Spike.Lib.X64WakeSrcCtl
import Spike.Lib.X64WakeMainW

namespace Spike.Lib.X64.HelloPh.WcPlS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region Ctl MemSide)
open Spike.Lib.X64 (SO AS Abs ND BlkW NodeW arun)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64.Flow (XProW xProN1 xProN2 xProN3 xProN4 xHead xLea xCmp xFr xSt xS1 xS2 xS3 hdRegs)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.Flow.HelloM (wcJ0)
open Spike.Lib.X64.Flow.HelloWc (WcPreWH WcSp0WH wARH WcCtxH wcJH wNH sNH oWRH wcEH wcS0H)
open Spike.Lib.X64.Flow.HelloJr1 (SlRegs)
open Spike.Lib.X64.Alloc (Call AllocW)
open Spike.Lib.X64WakeMainW (M1 placeVal_reg placeVal_cell)
open Spike.Lib.X64.WakeSrcCtl (keepsSlot arun_slot_keep placeVal_slot_abs)
open Spike.Lib.X64HelloMainPreSrc (c0H newTerm)
open Spike.Lib.X64HelloRdCf (slW)
open Spike.Lib.X64.HelloPh.PlacedAlloc (CtxG placeVal_slot_keptG)

/-- The machine's places. -/
local notation "PlM" => Place M1.I.RegId

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State}

/-! ## The two controls at any places -/

/-- **The setup continuation on rodata's slice placed**: `r`'s words `slW l` at `p0`, `p2`, `p3` (the slice's
`%rdi`, `%rdx`, `%rcx` at `wc_main`'s entry), `me`'s word `mw` at `pm`. -/
theorem placedSE_cont {l : WeakMem.AllocLabel} {env : TermRun.Env} {ty : Ty} {mw : TermRun.Word}
    {h : Option (Nat × TermRun.Word)} (hmeE : TermRun.lookupE env "me" = some (.tid, [mw])) (p0 p2 p3 pm : PlM)
    (h0 : ∃ v, placeVal M1 s p0 = some v ∧ lbl l = some v)
    (h2 : placeVal M1 s p2 = some 2) (h3 : placeVal M1 s p3 = some 13)
    (hm : ∃ v, placeVal M1 s pm = some v ∧ ValRep lbl mw.val v) :
    PlacedSE Λ lbl s ⟨SrcCalls.setupCont, ("r", ty, slW l) :: env, h⟩ [] := by
  have hr : TermRun.lookupE (("r", ty, slW l) :: env) "r" = some (ty, slW l) := by simp [TermRun.lookupE]
  have hme : TermRun.lookupE (("r", ty, slW l) :: env) "me" = some (.tid, [mw]) := by
    unfold TermRun.lookupE at hmeE ⊢; rw [List.find?_cons_of_neg (by simp)]; exact hmeE
  refine Spike.Lib.X64.WakeSrcCtl.placedSE_of_tbl [("r", [.one p0, .one p2, .one p3]), ("me", [.one pm])] ?_ ?_ ?_
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
      | 0, hwp, hwd => cases hwp; cases hwd; exact Spike.Lib.X64.WakeSrcCtl.rep_at h0
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
    (h0 : ∃ v, placeVal M1 s p0 = some v ∧ ValRep lbl w0.val v)
    (h1 : ∃ v, placeVal M1 s p2 = some v ∧ ValRep lbl w1.val v)
    (h2 : ∃ v, placeVal M1 s p3 = some v ∧ ValRep lbl w2.val v)
    (hm : ∃ v, placeVal M1 s pm = some v ∧ ValRep lbl mw.val v) :
    PlacedSE Λ lbl s (c0H w0 w1 w2 mw) [] := by
  have hzl : TermRun.lookupE (c0H w0 w1 w2 mw).env "z" = some (.int, [TermRun.cst (.num 0)]) := rfl
  have hsl : TermRun.lookupE (c0H w0 w1 w2 mw).env "sl" =
      some (Spike.Lib.X64HelloSplit.slTy, [w0, w1, w2]) := rfl
  have hme : TermRun.lookupE (c0H w0 w1 w2 mw).env "me" = some (.tid, [mw]) := rfl
  refine Spike.Lib.X64.WakeSrcCtl.placedSE_of_tbl
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

/-- **`wc_main`'s entry registers**: those of a state of the caller's `Jr` at the same control, moved as
`scc_rt_main` moves them (`%rdi ← %rax`, `%rdx ← %rcx`, `%rcx ← %rsi`), `%r8` the caller's slot `-16` (`mWC`). -/
theorem entry_wcJ0 {lab : Label → Int64} {σC σ1 : AS} {Jx : AS → Ctl → Prop} {σ : AS} {c : Ctl}
    (h : wcJ0 (mWC lab σC Jx).J σ1 σ c) :
    ∃ σx, Jx σx c ∧ σ.regs.rdi = σx.regs.rax ∧ σ.regs.rdx = σx.regs.rcx ∧ σ.regs.rcx = σx.regs.rsi ∧
      σ.regs.r8.toBitVec = σC.slot (-16) := by
  obtain ⟨rfl, σx, hJ, h0, -, h2, h3, h4, -⟩ := h
  exact ⟨σx, hJ, h0, h2, h3, h4⟩

/-- **A control placed at an entry state's four registers**: each control of `J` is placed wherever four places
read its state's `%rdi`, `%rdx`, `%rcx`, `%r8`. -/
def PlE (Λ : Scc.Sem.Layout) (lbl : Lbl) (J : AS → Ctl → Prop) : Prop :=
  ∀ σ c, J σ c → ∀ (s : State) (p0 p2 p3 p4 : PlM), placeVal M1 s p0 = some σ.regs.rdi.toBitVec.toNat →
    placeVal M1 s p2 = some σ.regs.rdx.toBitVec.toNat → placeVal M1 s p3 = some σ.regs.rcx.toBitVec.toNat →
    placeVal M1 s p4 = some σ.regs.r8.toBitVec.toNat → PlacedSE Λ lbl s c []

section Entry

variable {lab : Label → Int64} {σC σ1 : AS} {l : WeakMem.AllocLabel} {mw : TermRun.Word}

/-- **The setup continuation at `wc_main`'s entry placed** (`PlE`): the caller's `Jr` is at the continuation on
`slW l` with the slice's registers (`hJr`), `me`'s word represented by the caller's slot `-16` (`hme`). -/
theorem plE_cont {Jr : AS → Ctl → Prop} {env : TermRun.Env}
    (hmeE : TermRun.lookupE env "me" = some (.tid, [mw])) (hme : ValRep lbl mw.val (σC.slot (-16)).toNat)
    (hJr : ∀ σ c, Jr σ c → c = ⟨SrcCalls.setupCont, ("r", Spike.Lib.X64HelloSplit.slTy, slW l) :: env, none⟩ ∧
      SlRegs lbl l σ) :
    PlE Λ lbl (wcJ0 (mWC lab σC Jr).J σ1) := by
  intro σ c hj s p0 p2 p3 p4 r0 r2 r3 r4
  obtain ⟨σx, hJx, e0, e2, e3, e4⟩ := entry_wcJ0 hj
  obtain ⟨rfl, hl, -, hx2, hx3⟩ := hJr σx c hJx
  exact placedSE_cont hmeE p0 p2 p3 p4 ⟨_, r0, by rw [e0]; exact hl⟩ (by rw [r2, e2, hx2]) (by rw [r3, e3, hx3])
    ⟨_, r4, by rw [e4]; exact hme⟩

/-- **`c0H` at `wc_main`'s entry placed** (`PlE`): the caller's `Jr1` is at `c0H` on `slW l`'s words and `mw`
with the slice's registers (`hJ1`, `HelloJr1.Jr1H`). -/
theorem plE_c0H {Jr1 : AS → Ctl → Prop} (hz : Λ.imms newTerm "z" 0 = some 0)
    (hme : ValRep lbl mw.val (σC.slot (-16)).toNat)
    (hJ1 : ∀ σ c, Jr1 σ c → c = c0H (TermRun.cst (.loc ⟨l, 0⟩ 0)) (TermRun.cst (.num 2)) (TermRun.cst (.num 13)) mw ∧
      SlRegs lbl l σ) :
    PlE Λ lbl (wcJ0 (mWC lab σC Jr1).J σ1) := by
  intro σ c hj s p0 p2 p3 p4 r0 r2 r3 r4
  obtain ⟨σx, hJx, e0, e2, e3, e4⟩ := entry_wcJ0 hj
  obtain ⟨rfl, hl, -, hx2, hx3⟩ := hJ1 σx c hJx
  exact placedSE_c0H hz p0 p2 p3 p4 (Spike.Lib.X64.WakeSrcCtl.rep_at ⟨_, r0, by rw [e0]; exact hl⟩)
    ⟨_, r2, by decide, by rw [e2, hx2]⟩ ⟨_, r3, by decide, by rw [e3, hx3]⟩ ⟨_, r4, by rw [e4]; exact hme⟩

end Entry

/-! ## Reading the entry's words -/

/-- The four registers the placement reads. -/
def KR (r : Reg64) : Prop := r = .rdi ∨ r = .rdx ∨ r = .rcx ∨ r = .r8

/-- **Placed at registers as the entry's**: at a state whose `%rdi`, `%rdx`, `%rcx`, `%r8` are an entry
state's. -/
theorem plE_regs {J : AS → Ctl → Prop} (hP : PlE Λ lbl J) {σ : AS} {c : Ctl} (hJ : J σ c) (s : State)
    (h : ∀ r, KR r → s.st.1.regs.get64 r = σ.regs.get64 r) : PlacedSE Λ lbl s c [] :=
  hP σ c hJ s (.reg (.r .rdi)) (.reg (.r .rdx)) (.reg (.r .rcx)) (.reg (.r .r8))
    (by rw [placeVal_reg, h _ (.inl rfl)]; rfl) (by rw [placeVal_reg, h _ (.inr (.inl rfl))]; rfl)
    (by rw [placeVal_reg, h _ (.inr (.inr (.inl rfl)))]; rfl)
    (by rw [placeVal_reg, h _ (.inr (.inr (.inr rfl)))]; rfl)

/-- `wc_main`'s spill slots of the entry's `%rdi`, `%rdx`, `%rcx`, `%r8`. -/
abbrev spills : List Int := [-16, -32, -40, -48]

/-- **Placed at the spills**: at a state whose cells at the spill slots are a frame's (`wcJH`). -/
theorem plE_slots {J : AS → Ctl → Prop} (hP : PlE Λ lbl J) {R : Region} {σ : AS} {c : Ctl}
    (hJ : wcJH J σ c) (s : State)
    (h : ∀ k ∈ spills, placeVal M1 s (.slot (R.addr k).toNat) = some (σ.slot k).toNat) : PlacedSE Λ lbl s c [] := by
  obtain ⟨σe, hJe, -, -, h16, -, h32, h40, h48⟩ := hJ
  exact hP σe c hJe s _ _ _ _ (by rw [h (-16) (by simp), h16]) (by rw [h (-32) (by simp), h32])
    (by rw [h (-40) (by simp), h40]) (by rw [h (-48) (by simp), h48])

/-- The spill slots are in a region reaching `-48`, at or above the allocator's region's top (`-136`). -/
theorem off_spills {R : Region} (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) : ∀ k ∈ spills, R.Off k ∧ -136 ≤ k := by
  intro k hk
  simp only [spills, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> exact ⟨⟨by decide, by omega, by omega⟩, by decide⟩

/-! ## The prologue -/

section Pro

set_option linter.unusedSimpArgs false

/-- The abstract run's simp set over concrete blocks (as in `PlacedZ.keepA_pro`). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Spike.Lib.X64.arun, Spike.Lib.X64.dstep, Spike.Lib.X64.classify, Spike.Lib.X64.RegOnly,
    Spike.Lib.X64.AI.so, Spike.Lib.X64.soReg,
    Spike.Lib.X64.regDst, Spike.Lib.X64.regRes, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp, AddrExpr.interp, Spike.Lib.X64.SO.get,
    Spike.Lib.X64.SO.set, Spike.Lib.X64.SO.kill, Spike.Lib.X64.SO.write, Spike.Lib.lk, Spike.Lib.rm, Reg.base,
    Spike.Lib.upd_apply,
    Spike.Lib.X64.Reg64s.get_low64, Spike.Lib.X64.BlockSpec.AI.step_ld',
    Spike.Lib.X64.BlockSpec.AI.step_st', Spike.Lib.X64.BlockSpec.AI.step_push',
    Spike.Lib.X64.BlockSpec.AI.step_pop', Spike.Lib.X64.BlockSpec.AI.step_reg',
    Spike.Lib.X64.BlockSpec.AI.step_jmp', Spike.Lib.X64.BlockSpec.AI.step_jcc',
    Spike.Lib.X64.BlockSpec.AI.step_call', Spike.Lib.X64.Reg64s.get64_set64_ne,
    Spike.Lib.X64.Reg64s.get64_set64_self])

/-- `wc_main`'s five argument registers, spilled at `-8 .. -40(%rbp)`, with their sizes. -/
abbrev wcPsH : List (Reg64 × Int64 × Nat) :=
  [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4)]

/-- **Every prefix of `wc_main`'s prologue blocks keeps `KR`.** -/
theorem keepK_pro (l : String → Int64) (pc : Int64) (o : SO) (σ : AS) (Z : Int64) (L : String) (z2 : Nat)
    {blk : List (Directive × Nat)}
    (hb : blk = xHead ∨ blk = xLea Z 5 ∨ blk = xCmp L 3 z2 ∨ blk = xFr Z 7 wcPsH)
    {k : Nat} (hk : k < blk.length) (r : Reg64) (hr : KR r) :
    (arun l (blk.take k) ⟨pc, o, σ⟩).σ.regs.get64 r = σ.regs.get64 r := by
  rcases hr with rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [xHead, xLea, xCmp, xFr, xSt, wcPsH, List.map_cons, List.map_nil, List.length_cons,
      List.length_nil] at hk ⊢ <;>
    rcases k with _|_|_|_|_|_|_|k <;> (try omega) <;> arun_simp

theorem keepK_xS1 (σ : AS) (r : Reg64) (hr : KR r) : (xS1 σ).regs.get64 r = σ.regs.get64 r := by
  simp only [xS1, hdRegs]
  rcases hr with rfl | rfl | rfl | rfl <;>
    rw [Spike.Lib.X64.Reg64s.get64_set64_ne _ (by decide), Spike.Lib.X64.Reg64s.get64_set64_ne _ (by decide)]

theorem keepK_xS2 (Z : Int64) (σ : AS) (r : Reg64) (hr : KR r) : (xS2 Z σ).regs.get64 r = σ.regs.get64 r := by
  simp only [xS2]
  rw [Spike.Lib.X64.Reg64s.get64_set64_ne _ (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
  exact keepK_xS1 σ r hr

theorem keepK_xS3 (Z : Int64) (v : BitVec 64) (σ : AS) (r : Reg64) (hr : KR r) :
    (xS3 Z v σ).regs.get64 r = σ.regs.get64 r := by
  simp only [xS3, Spike.Lib.X64.fsStep]
  rw [Spike.Lib.X64.Reg64s.get64_set64_ne _ (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
  exact keepK_xS2 Z σ r hr

/-- **`wc_main`'s prologue inside the placement** from its entry's (`PlE`): the prologue writes none of `%rdi`,
`%rdx`, `%rcx`, `%r8` (the head, the check's `leaq`, the limit's load into `%r11`, the check, the frame's set-up and
the argument stores). -/
theorem proW_pl {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {pc0 Z lim : Int64} {L : String} {z2 : Nat} {J : AS → Ctl → Prop} (hP : PlE Λ lbl J) :
    XProW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F ms pc0 Z lim L 5 9 3 z2 7 wcPsH J := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    refine ⟨plE_regs hP hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs, keepK_pro (_root_.Executable.labels exe).label pc0 ⟨0, []⟩ σ Z L z2 (.inl rfl) hk r hr]
  · rintro s σ1 c _ _ _ _ _ _ ⟨σ, hJ, rfl⟩ k hk m hA' _
    refine ⟨plE_regs hP hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs, keepK_pro (_root_.Executable.labels exe).label (xProN1 pc0 J).pc (xProN1 pc0 J).o (xS1 σ) Z L
      z2 (.inr (.inl rfl)) hk r hr, keepK_xS1 σ r hr]
  · rintro s c ⟨-, -, -, -, σ2, hA, -, σ, hJ, rfl⟩
    refine ⟨plE_regs hP hJ _ fun r hr => ?_, fun _ h => h⟩
    rw [hA.regs, keepK_xS2 Z σ r hr]
  · rintro s σ3 c _ _ _ _ _ _ ⟨σ, v, hJ, -, rfl⟩ k hk m hA' _
    refine ⟨plE_regs hP hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs, keepK_pro (_root_.Executable.labels exe).label (xProN3 ms pc0 5 9 Z lim J).pc
      (xProN3 ms pc0 5 9 Z lim J).o (xS3 Z (v.setWidth 64) σ) Z L z2 (.inr (.inr (.inl rfl))) hk r hr,
      keepK_xS3 Z _ σ r hr]
  · rintro s σ4 c _ _ _ _ _ _ ⟨σ, v, hJ, -, hreg, -⟩ k hk m hA' _
    refine ⟨plE_regs hP hJ _ fun r hr => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs, keepK_pro (_root_.Executable.labels exe).label (xProN4 ms pc0 5 9 3 z2 Z lim J).pc
      (xProN4 ms pc0 5 9 3 z2 Z lim J).o σ4 Z L z2 (.inr (.inr (.inr rfl))) hk r hr,
      show σ4.regs.get64 r = _ from congrArg (·.get64 r) hreg, keepK_xS3 Z _ σ r hr]

end Pro

/-! ## The allocator, at the call state's slots -/

section Alloc

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ms : MemSide isa}
  {q : Call} {fr : Int}

set_option hygiene false in
/-- The placement at the labels `lbl`, no frame. -/
local notation "PL" => fun s c => PlacedSE Λ lbl s c []

/-- **The caller's source placed at every node of `scc_rt_alloc`**, called at offset `fr`, given every caller
slot a word above the call node (the all-slots variant of `PlacedAlloc.allocW_placedG`). -/
theorem allocW_placedS {Jn : AS → Ctl → Prop} (hR : R.OK) (hlo : R.lo ≤ fr) (hfr : fr < 0) (hhi : 0 ≤ R.hi)
    (hP : ∀ σC, (∃ mC, Abs R ⟨fr, []⟩ mC σC) → Jn σC q.c0 → ∀ s : State,
      (∀ k, R.Off k → fr + 8 ≤ k → placeVal M1 s (.slot (R.addr k).toNat) = some (σC.slot k).toNat) →
        PlacedSE Λ lbl s q.c0 []) :
    AllocW ms q (PL) (fun _ _ => False) exe endPc (R.callee fr (-160) 8)
      (fun m => F m ∧ CallerCells R fr (-160) 8 m ∧ CtxG ms (_root_.Executable.labels exe).label R fr Jn q m) := by
  refine Spike.Lib.X64SetupPlaced.allocW_of_ctl fun m0 hF s c hD hc => ?_
  obtain ⟨-, -, mC, σC, c', hA, hJ, hN, hK⟩ := hF
  have hq0 : c' = q.c0 := hN.1
  subst hq0
  have h := hP σC ⟨mC, hA⟩ hJ s fun k hk hk' => placeVal_slot_keptG hA hK hD hR hlo hfr hhi hk hk'
  rcases hc with rfl | ⟨o, rfl⟩
  · exact h
  · exact h

/-- **`wc_main`'s box call placed** (call node at `-144`): the call's controls are `J1`'s, placed at the spills
(`PlE`). -/
theorem allocW_placedS_wcH {J0 J1 : AS → Ctl → Prop} (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (hP : PlE Λ lbl J1) :
    AllocW ms q (PL) (fun _ _ => False) exe endPc (wARH R)
      (fun m => F m ∧ CallerCells R (-144) (-160) 8 m ∧
        WcCtxH ms (_root_.Executable.labels exe).label R J0 J1 q m) :=
  allocW_placedS hR hlo (by decide) hhi fun _ _ hJ s hsl =>
    plE_slots hP hJ.1 s fun k hk => hsl k (off_spills (by omega) hhi k hk).1 (off_spills (by omega) hhi k hk).2

end Alloc

/-! ## `wc_main` up to the box's store -/

/-- `wc_main`'s entry block keeps the spills. -/
theorem keeps_wcEH : ∀ k ∈ spills, keepsSlot k oWRH wcEH = true := by decide +kernel

/-- `.x22`'s block keeps the spills. -/
theorem keeps_wcS0H : ∀ k ∈ spills, keepsSlot k oWRH wcS0H = true := by decide +kernel

section Wc

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ms : MemSide isa}

set_option hygiene false in
/-- The placement at the labels `lbl`, no frame. -/
local notation "PL" => fun s c => PlacedSE Λ lbl s c []

/-- **`wc_main` up to the allocator's return inside the placement** (`WcPreWH`'s `hpl`): the entry's controls
placed at its four registers (`hP0`), the call's (`hP1`); the prologue keeps the registers, the entry block and
the allocator the spills. -/
theorem hplP_S {J0 J1 : AS → Ctl → Prop} (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (hP0 : PlE Λ lbl J0) (hP1 : PlE Λ lbl J1) : WcPreWH (PL) (fun _ _ => False) exe endPc R F ms J0 J1 := by
  refine ⟨proW_pl hP0, ?_, fun q _ _ => allocW_placedS_wcH hR hlo hhi hP1⟩
  intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
  refine ⟨plE_slots (R := R) hP0 hJ.1 _ fun j hj => ?_, fun _ h => h⟩
  rw [placeVal_cell hA' (off_spills (by omega) hhi j hj).1 _ rfl]
  exact congrArg (fun v : BitVec 64 => some v.toNat) (arun_slot_keep _ j wcEH ⟨_, oWRH, σ⟩ k (keeps_wcEH j hj))

/-- **`.x22` inside the placement** (`WcSp0WH`'s `hpl`): the call's controls placed at its four registers
(`hP1`), so `.x22`'s, the hold aside, at the spills, kept by `.x22`'s block. -/
theorem hplS_S {J1 : AS → Ctl → Prop} (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hP1 : PlE Λ lbl J1) :
    WcSp0WH (PL) (fun _ _ => False) exe endPc R F ms J1 := by
  refine ⟨?_, ?_⟩
  · intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
    obtain ⟨q, hw, -, o, rfl, -⟩ := hJ
    refine ⟨plE_slots (R := R) hP1 hw _ fun j hj => ?_, fun _ h => h⟩
    rw [placeVal_cell hA' (off_spills hlo hhi j hj).1 _ rfl]
    exact congrArg (fun v : BitVec 64 => some v.toNat)
      (arun_slot_keep _ j wcS0H ⟨_, oWRH, σ⟩ k (keeps_wcS0H j hj))
  · rintro s c ⟨-, -, -, -, σ, hA, -, q, o, hw, rfl, -⟩
    exact ⟨plE_slots (R := R) hP1 hw _ fun j hj => placeVal_slot_abs hA (off_spills hlo hhi j hj).1, fun _ h => h⟩

end Wc

end Spike.Lib.X64.HelloPh.WcPlS

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.placedSE_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.placedSE_cont

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.placedSE_c0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.placedSE_c0H

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.entry_wcJ0' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.entry_wcJ0

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.plE_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.plE_cont

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.plE_c0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.plE_c0H

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.plE_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.plE_regs

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.plE_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.plE_slots

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.off_spills' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.off_spills

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.keepK_pro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.keepK_pro

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.keepK_xS1' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.keepK_xS1

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.keepK_xS2' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.keepK_xS2

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.keepK_xS3' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.keepK_xS3

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.proW_pl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.proW_pl

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.allocW_placedS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.allocW_placedS

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.allocW_placedS_wcH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.allocW_placedS_wcH

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.keeps_wcEH' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.keeps_wcEH

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.keeps_wcS0H' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.keeps_wcS0H

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.hplP_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.hplP_S

/-- info: 'Spike.Lib.X64.HelloPh.WcPlS.hplS_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcPlS.hplS_S
