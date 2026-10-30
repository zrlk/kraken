import Scc.Emit.A64
import Scc.Lower.SpecA64
import Scc.Lower.InvProg

/-!
# AArch64 frame slots of the emitter

Facts about where the AArch64 emitter (`Scc/Emit/A64.lean`) keeps a
function's IR registers, for the per-construct code lemmas:

* `fnCtx_slots`, `fnCtx_out`, `fnCtx_frame`: the context of a function has
  its registers (`funcRegs`, in order of first occurrence) as slots, above an
  outgoing argument area of `outWords` words, in a frame of
  `8 * out + align16 (8 * slots.length + 16)` bytes;
* `slotOff_ok`: a register of the slots is at offset `8 * (out + i)` from
  `sp`, `i` its index among the slots; `slotOff_inj`: different registers
  are at different offsets;
* `slotOff_bounds`: in a frame of that size the offset is non-negative, a
  multiple of 8, and the slot ends at least 16 bytes below the frame's top
  (the saved `x29`/`x30` pair);
* `slotOff_scaled`, `getReg_eq`, `setReg_eq`: in a frame of at most 32 KiB
  the scaled unsigned-offset form applies, so reading a register is one
  `ldr` and writing it one `str`;
* `inst_addChk`: the code of `addChk d a b`; `term_ret1`: the code of
  `ret [v]`; `leave_eq`: the frame's exit (two `ldr`, freeing the frame);
* `lowerAll?_low_a64`: `lowerAll?`'s IR is `lowerIR`'s;
  `lowerAll_accepted0_a64`: on an `Accepted0` program `lowerAll`'s IR is the
  runtime functions, then `func0 main r` (`Scc/Lower/InvProg.lean`);
* `funcRegs_mainThread0`, `mainThreadF_frame`, `mainThreadF_spill`: the
  slots of the main-thread runtime function (`Inv.mainThread0`), its frame
  `A64.mainFrame` and the slot of `main`'s result `A64.mainSpill`;
* `frame_le_of_frames`: the bound `c.frame ≤ 32768` for the context
  `A64.ctxOf p fi f` of each function, from the emitted frame sizes
  `Emitted.frames` (a placement-check fact).

## Machine-block boundaries around `addChk`

`inst_addChk` emits the operands' loads, `adds x9, x9, x10`,
`b.cs <function prefix>abort_overflow`, then `str x9` into `d`'s slot. The
conditional branch ends a machine block: the `str` of `d` (the next
instruction, the fall-through successor) begins the next one. On `ret0.w`
the block table of the emitted text accordingly starts the second block of
`main` at the `str` of `y%0`.
-/

namespace Scc.Lower.InvA64

open Scc.Emit.A64

/-! ## The context of a function -/

section
variable (abortFn : String) (growth : Option IR.Growth) (areas : List (IR.Sym × Nat))
  (fi : Nat) (f : IR.Func)

theorem fnCtx_slots : (fnCtx abortFn growth areas fi f).slots = funcRegs f := rfl

theorem fnCtx_out : (fnCtx abortFn growth areas fi f).out = outWords areas f := rfl

theorem fnCtx_frame :
    (fnCtx abortFn growth areas fi f).frame =
      8 * (fnCtx abortFn growth areas fi f).out +
        align16 (8 * (fnCtx abortFn growth areas fi f).slots.length + 16) := rfl

end

/-! ## Slot offsets -/

/-- A frame of the size `fnCtx` gives. -/
def FrameOk (c : FnCtx) : Prop := c.frame = 8 * c.out + align16 (8 * c.slots.length + 16)

theorem fnCtx_frameOk (abortFn : String) (growth : Option IR.Growth)
    (areas : List (IR.Sym × Nat)) (fi : Nat) (f : IR.Func) :
    FrameOk (fnCtx abortFn growth areas fi f) := rfl

theorem slotOff_ok {c : FnCtx} {r : IR.Reg} (h : r ∈ c.slots) :
    ∃ i, ∃ hi : i < c.slots.length, c.slots[i] = r ∧
      c.slotOff r = .ok (8 * ((c.out : Int) + (i : Int))) := by
  cases hx : c.slots.idxOf? r with
  | none => exact absurd h (List.idxOf?_eq_none_iff.mp hx)
  | some i =>
    obtain ⟨hi, hr, -⟩ := List.idxOf?_eq_some_iff.mp hx
    exact ⟨i, hi, hr, by simp [FnCtx.slotOff, hx]⟩

/-- What a successful `slotOff` says: the register's index among the slots. -/
theorem slotOff_index {c : FnCtx} {r : IR.Reg} {off : Int} (h : c.slotOff r = .ok off) :
    ∃ i, ∃ hi : i < c.slots.length, c.slots[i] = r ∧ off = 8 * ((c.out : Int) + (i : Int)) := by
  unfold FnCtx.slotOff at h
  split at h
  · rename_i i hx
    obtain ⟨hi, hr, -⟩ := List.idxOf?_eq_some_iff.mp hx
    cases h
    exact ⟨i, hi, hr, rfl⟩
  · cases h

/-- Different registers are at different offsets. -/
theorem slotOff_inj {c : FnCtx} {r r' : IR.Reg} {off : Int} (h : c.slotOff r = .ok off)
    (h' : c.slotOff r' = .ok off) : r = r' := by
  obtain ⟨i, hi, hr, ho⟩ := slotOff_index h
  obtain ⟨j, hj, hr', ho'⟩ := slotOff_index h'
  have : i = j := by omega
  subst this
  exact hr.symm.trans hr'

theorem le_align16 (n : Nat) : n ≤ align16 n := by
  unfold align16; omega

theorem align16_mod (n : Nat) : align16 n % 16 = 0 := by
  unfold align16; omega

theorem slotOff_bounds {c : FnCtx} (hf : FrameOk c) {r : IR.Reg} {off : Int}
    (h : c.slotOff r = .ok off) :
    0 ≤ off ∧ off % 8 = 0 ∧ off + 8 ≤ (c.frame : Int) - 16 := by
  obtain ⟨i, hi, -, rfl⟩ := slotOff_index h
  have ha := le_align16 (8 * c.slots.length + 16)
  unfold FrameOk at hf
  refine ⟨by omega, by omega, by omega⟩

theorem slotOff_scaled {c : FnCtx} (hf : FrameOk c) (hs : c.frame ≤ 32768) {r : IR.Reg}
    {off : Int} (h : c.slotOff r = .ok off) : scaledOk 8 off = true := by
  obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf h
  simp only [scaledOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨h0, by omega⟩, by omega⟩

/-! ## Register reads and writes -/

theorem ldrOff_scaled {w : RegWidth} {rt : XReg} {base : RegOrSp .W64} {off : Int}
    (h : scaledOk w.bytes off = true) :
    ldrOff w rt base off = [ins (.LDR (rz w rt) (.addr ⟨base, .imm ⟨i64 off, none⟩⟩))] := by
  simp [ldrOff, h]

theorem strOff_scaled {w : RegWidth} {rt : XReg} {base : RegOrSp .W64} {off : Int}
    (h : scaledOk w.bytes off = true) :
    strOff w rt base off = [ins (.STR (rz w rt) ⟨base, .imm ⟨i64 off, none⟩⟩)] := by
  simp [strOff, h]

/-- Reading IR register `r` into `t` is one `ldr t, [sp, #off]`. -/
theorem getReg_eq {c : FnCtx} (hf : FrameOk c) (hs : c.frame ≤ 32768) {r : IR.Reg} {off : Int}
    (h : c.slotOff r = .ok off) (t : XReg) :
    c.getReg t r = .ok [ins (.LDR (rz .W64 t) (.addr ⟨spW64, .imm ⟨i64 off, none⟩⟩))] := by
  simp only [FnCtx.getReg, h, bind, Except.bind, pure, Except.pure]
  rw [ldrOff_scaled (w := .W64) (slotOff_scaled hf hs h)]

/-- Writing `t` into IR register `r` is one `str t, [sp, #off]`. -/
theorem setReg_eq {c : FnCtx} (hf : FrameOk c) (hs : c.frame ≤ 32768) {r : IR.Reg} {off : Int}
    (h : c.slotOff r = .ok off) (t : XReg) :
    c.setReg r t = .ok [ins (.STR (rz .W64 t) ⟨spW64, .imm ⟨i64 off, none⟩⟩)] := by
  simp only [FnCtx.setReg, h, bind, Except.bind, pure, Except.pure]
  rw [strOff_scaled (w := .W64) (slotOff_scaled hf hs h)]

/-- **The code of `addChk d a b`**: load `a` into `x9` and `b` into `x10`,
`adds x9, x9, x10`, `b.cs` to the function's overflow abort, store `x9`
into `d`'s slot. -/
theorem inst_addChk {c : FnCtx} (hf : FrameOk c) (hs : c.frame ≤ 32768) (k : Nat)
    {d : IR.Reg} {a b : IR.Operand} {la lb : List Item} {off : Int}
    (ha : c.getOp .X9 a = .ok la) (hb : c.getOp .X10 b = .ok lb) (hd : c.slotOff d = .ok off) :
    c.inst k (.addChk d a b) = .ok (la ++ lb ++ addChecked .X9 .X9 .X10 (c.local "abort_overflow") ++
      [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 off, none⟩⟩)]) := by
  simp only [FnCtx.inst, ha, hb, setReg_eq hf hs hd, bind, Except.bind, pure, Except.pure]

/-- **The frame's exit** in a frame of at most 32 KiB: reload `x29` and `x30`
with one `ldr` each, then free the frame. -/
theorem leave_eq {c : FnCtx} (hf : FrameOk c) (hs : c.frame ≤ 32768) :
    c.leave = [ins (.LDR (rz .W64 .X29) (.addr ⟨spW64, .imm ⟨i64 ((c.frame : Int) - 16), none⟩⟩)),
      ins (.LDR (rz .W64 .X30) (.addr ⟨spW64, .imm ⟨i64 ((c.frame : Int) - 8), none⟩⟩))] ++
      addImm spW64 spW64 c.frame := by
  have ha := le_align16 (8 * c.slots.length + 16)
  have hm := align16_mod (8 * c.slots.length + 16)
  unfold FrameOk at hf
  unfold FnCtx.leave
  rw [ldrOff_scaled (w := .W64), ldrOff_scaled (w := .W64)]
  · rfl
  all_goals
    have hb : RegWidth.W64.bytes = 8 := rfl
    simp only [scaledOk, hb, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨by omega, by omega⟩, by omega⟩

/-- **The code of `ret [v]`** (one result word, as an `Accepted0` body
returns): `v` into `x0`, then the frame's exit `c.leave` and `ret`. -/
theorem term_ret1 {c : FnCtx} (k : Nat) {v : IR.Operand} {l : List Item}
    (hv : c.getOp .X0 v = .ok l) : c.term k (.ret [v]) = .ok (l ++ c.leave ++ [ret]) := by
  have ha : argRegs = .X0 :: argRegs.tail := rfl
  simp only [FnCtx.term]
  rw [ha]
  simp [hv, IR.maxRets, bind, Except.bind, pure, Except.pure, forIn, ForIn.forIn]

/-! ## `lowerAll`'s IR -/

section
open CoreTerm Scc.IR Scc.Lower Scc.Lower.Inv

/-- `lowerAll?`'s IR (AArch64) is `lowerIR`'s. -/
theorem lowerAll?_low_a64 {cfg : Config} {p : Prog} {e : Scc.Lower.A64.Emitted}
    (h : Scc.Lower.A64.lowerAll? cfg p = .ok e) : lowerIR cfg p = .ok e.low := by
  unfold Scc.Lower.A64.lowerAll? at h
  cases hl : lowerIR cfg p with
  | error m => simp only [hl, bind, Except.bind] at h; cases h
  | ok l =>
    simp only [hl, bind, Except.bind, Scc.Lower.A64.emitAll] at h
    cases hi : Scc.Emit.A64.emitItemsMaps l.ir with
    | error m => simp only [hi] at h; cases h
    | ok v => simp only [hi, pure, Except.pure] at h; cases h; rfl

/-- **`lowerAll`'s IR on an `Accepted0` program** (AArch64), when the
lowering and emission succeed: the runtime functions, then `func0 main r`. -/
theorem lowerAll_accepted0_a64 (cfg : Config) {d : Decl} (hd : Accepted0 [d] = true)
    {e : Scc.Lower.A64.Emitted} (h : Scc.Lower.A64.lowerAll? cfg [d] = .ok e) :
    ∃ r rt, lower0 [(d.arg, .unit, [])] 0 d.body = some r ∧
      rtFuncs cfg.arch cfg.layout ⟨.unit, true⟩ 0 = .ok rt ∧
      (Scc.Lower.A64.lowerAll cfg [d]).low.ir = progOf cfg.layout rt [func0 (Names.user "main") r] := by
  obtain ⟨r, rt, hr, hrt, hir, -⟩ := lowerIR_accepted0 cfg hd (lowerAll?_low_a64 h)
  refine ⟨r, rt, hr, hrt, ?_⟩
  simp only [Scc.Lower.A64.lowerAll, h]
  exact hir

/-! ## The main-thread runtime function -/

/-- `funcRegs`'s step: keep a register's first occurrence. -/
def dstep (acc : List Reg) (r : Reg) : List Reg := if acc.contains r then acc else acc ++ [r]

/-- `main`'s result register in the main-thread runtime function, if it returns an `Int`. -/
def mainVs (e : Frontend.Entry) (sw : Nat) : List Reg :=
  if e.retInt then [Inv.regName "v" (mainSetup e sw)] else []

/-- The `exit_group` result register of the main-thread runtime function. -/
def mainR (e : Frontend.Entry) (sw : Nat) : Reg :=
  Inv.regName "r" (mainSetup e sw + if e.retInt then 1 else 0)

/-- The registers among `main`'s arguments in the main-thread runtime function. -/
def mainArgRegs (e : Frontend.Entry) (sw : Nat) : List Reg :=
  match e.arg with
  | .unit => []
  | .tid => ["tcb"]
  | .setupTid => mainDs e sw ++ ["tcb"]

/-- `funcRegs` of the main-thread runtime function, before removing repeats. -/
theorem funcRegs_mainThread0_foldl (e : Frontend.Entry) (sw : Nat) :
    funcRegs (mainThread0 e sw) =
      (["tcb"] ++ mainDs e sw ++ (mainVs e sw ++ mainArgRegs e sw) ++ (mainR e sw :: mainVs e sw)).foldl dstep [] := by
  unfold funcRegs
  show List.foldl dstep [] _ = _
  congr 1
  obtain ⟨arg, ret⟩ := e
  have e1 : (Frontend.EntryArg.unit == .setupTid) = false := rfl
  have e2 : (Frontend.EntryArg.tid == .setupTid) = false := rfl
  have e3 : (Frontend.EntryArg.setupTid == .setupTid) = true := rfl
  have hfm : ∀ l : List Nat, l.flatMap (fun a => [Inv.regName "s" a]) = l.map (Inv.regName "s") := by
    intro l; induction l <;> simp_all
  cases arg <;> cases ret <;>
    simp [mainThread0, mainInsts, mainArgs, mainArgRegs, mainVs, mainR, mainDs, mainSetup,
      e1, e2, e3, List.flatMap_map, imm, hfm]

theorem foldl_dstep_sub : ∀ (l acc : List Reg), (∀ x ∈ l, x ∈ acc) → l.foldl dstep acc = acc
  | [], _, _ => rfl
  | x :: l, acc, h => by
    have hx : acc.contains x = true := by simpa using h x (by simp)
    simp only [List.foldl_cons, dstep, hx, ite_true]
    exact foldl_dstep_sub l acc fun y hy => h y (by simp [hy])

theorem foldl_dstep_new : ∀ (l acc : List Reg), l.Nodup → (∀ x ∈ l, x ∉ acc) →
    l.foldl dstep acc = acc ++ l
  | [], acc, _, _ => by simp
  | x :: l, acc, hn, h => by
    have hx : acc.contains x = false := by simpa using h x (by simp)
    simp only [List.foldl_cons, dstep, hx, Bool.false_eq_true, ite_false]
    rw [foldl_dstep_new l (acc ++ [x]) (List.nodup_cons.mp hn).2]
    · simp
    · intro y hy hm
      simp only [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact h y (by simp [hy]) hm
      · exact (List.nodup_cons.mp hn).1 hy

/-- A name `fresh` gives is not `tcb` (it has a `%`). -/
theorem regName_ne_tcb (h : String) (n : Nat) : Inv.regName h n ≠ "tcb" := by
  intro he
  have h1 : '%' ∈ (Inv.regName h n).toList := by
    have hp : (toString "%").toList = ['%'] := rfl
    simp [Inv.regName, String.toList_append, hp]
  rw [he] at h1
  revert h1; simp

theorem mem_mainDs {e : Frontend.Entry} {sw : Nat} {x : Reg} :
    x ∈ mainDs e sw ↔ ∃ i, i < mainSetup e sw ∧ Inv.regName "s" i = x := by
  simp [mainDs]

theorem mainDs_nodup (e : Frontend.Entry) (sw : Nat) : (mainDs e sw).Nodup := by
  unfold mainDs
  exact List.Pairwise.map _ (fun _ _ h => regName_ne h) List.nodup_range

/-- **The IR registers of the main-thread runtime function**, in order:
`tcb`, the setup words, `main`'s result (if an `Int`), the `exit_group`
result. -/
theorem funcRegs_mainThread0 (e : Frontend.Entry) (sw : Nat) :
    funcRegs (mainThread0 e sw) = "tcb" :: mainDs e sw ++ mainVs e sw ++ [mainR e sw] := by
  rw [funcRegs_mainThread0_foldl]
  have htcb : "tcb" ∉ mainDs e sw := fun h => by
    obtain ⟨i, -, hi⟩ := mem_mainDs.mp h; exact regName_ne_tcb _ _ hi
  have hv : ∀ x ∈ mainVs e sw, x ∉ "tcb" :: mainDs e sw := by
    intro x hx hm
    simp only [mainVs] at hx
    split at hx
    · simp only [List.mem_singleton] at hx
      subst hx
      rcases List.mem_cons.mp hm with h | h
      · exact regName_ne_tcb _ _ h
      · obtain ⟨i, hi, he⟩ := mem_mainDs.mp h
        exact regName_ne (show i ≠ mainSetup e sw by omega) he
    · cases hx
  have hvn : (mainVs e sw).Nodup := by unfold mainVs; split <;> simp
  have hr : mainR e sw ∉ "tcb" :: mainDs e sw ++ mainVs e sw := by
    intro hm
    simp only [List.mem_append, List.mem_cons] at hm
    rcases hm with (h | h) | h
    · exact regName_ne_tcb _ _ h
    · obtain ⟨i, hi, he⟩ := mem_mainDs.mp h
      exact regName_ne (n := i) (m := mainSetup e sw + if e.retInt = true then 1 else 0)
        (by split <;> omega) (by rw [he]; rfl)
    · simp only [mainVs] at h
      split at h
      · simp only [List.mem_singleton] at h
        exact regName_ne (show mainSetup e sw + (if e.retInt = true then 1 else 0) ≠ mainSetup e sw by
          simp [*]) (by simpa [mainR] using h)
      · cases h
  rw [List.foldl_append, List.foldl_append, List.foldl_append,
    foldl_dstep_new (["tcb"] ++ mainDs e sw) [] (by simpa using ⟨htcb, mainDs_nodup e sw⟩)
      (by simp)]
  rw [foldl_dstep_new _ _ hvn (by simpa using hv)]
  rw [foldl_dstep_sub (mainArgRegs e sw)]
  · rw [List.foldl_cons, show dstep ([] ++ (["tcb"] ++ mainDs e sw) ++ mainVs e sw) (mainR e sw) =
        "tcb" :: mainDs e sw ++ mainVs e sw ++ [mainR e sw] by
      simp only [dstep]; rw [ite_eq_right_iff.mpr (fun h => absurd (by simpa using h) hr)]; simp]
    rw [foldl_dstep_sub]
    intro x hx; simp [hx]
  · intro x hx
    simp only [mainArgRegs] at hx
    split at hx
    · simp at hx
    · simp at hx; simp [hx]
    · simp at hx; rcases hx with h | h <;> simp [h]

theorem idxOf?_append_cons {a : Reg} (pre post : List Reg) (h : a ∉ pre) :
    (pre ++ a :: post).idxOf? a = some pre.length := by
  rw [List.idxOf?_eq_some_iff]
  refine ⟨by simp, by simp, fun j hj he => h ?_⟩
  rw [List.getElem_append_left hj] at he
  exact he ▸ List.getElem_mem hj

/-- **The frame of the main-thread runtime function** (`A64.mainFrame`). -/
theorem mainThreadF_frame {entry : Frontend.Entry} {sw : Nat} {f : Func}
    (h : Runtime.mainThreadF entry sw = .ok f) (p : IR.Program) (fi : Nat) :
    (A64.ctxOf p fi f).frame = A64.mainFrame entry sw (A64.ctxOf p fi f).out := by
  rw [mainThreadF_eq] at h
  cases h
  show 8 * _ + align16 (8 * (funcRegs (mainThread0 entry sw)).length + 16) = _
  rw [funcRegs_mainThread0]
  simp only [A64.mainFrame, A64.mainSlots, mainVs, mainDs, List.length_cons, List.length_append,
    List.length_map, List.length_range]
  congr 3
  split <;> simp <;> omega

/-- **The slot of `main`'s result in the main-thread runtime function**
(`A64.mainSpill`), where it is kept for `exit_group`. -/
theorem mainThreadF_spill {entry : Frontend.Entry} {sw : Nat} {f : Func}
    (h : Runtime.mainThreadF entry sw = .ok f) (hr : entry.retInt = true) (p : IR.Program)
    (fi : Nat) :
    (A64.ctxOf p fi f).slotOff (Inv.regName "v" (mainSetup entry sw)) =
      .ok (A64.mainSpill entry sw (A64.ctxOf p fi f).out : Int) := by
  rw [mainThreadF_eq] at h
  cases h
  have hs : (A64.ctxOf p fi (mainThread0 entry sw)).slots =
      ("tcb" :: mainDs entry sw) ++ Inv.regName "v" (mainSetup entry sw) :: [mainR entry sw] := by
    show funcRegs _ = _
    rw [funcRegs_mainThread0]; simp [mainVs, hr]
  have hn : Inv.regName "v" (mainSetup entry sw) ∉ "tcb" :: mainDs entry sw := by
    intro hm
    rcases List.mem_cons.mp hm with h | h
    · exact regName_ne_tcb _ _ h
    · obtain ⟨i, hi, he⟩ := mem_mainDs.mp h
      exact regName_ne (show i ≠ mainSetup entry sw by omega) he
  unfold FnCtx.slotOff
  rw [hs, idxOf?_append_cons _ _ hn]
  simp only [A64.mainSpill, mainDs, List.length_cons, List.length_map, List.length_range]
  congr 1
  push_cast
  omega

/-! ## The frame bound from `Emitted.frames` -/

theorem ctxOf_frameOk (p : IR.Program) (fi : Nat) (f : Func) : FrameOk (A64.ctxOf p fi f) :=
  fnCtx_frameOk ..

/-- **The frame bound of each function from the emitted frame sizes**: if
every entry of `e.frames` is at most 32768, so is the frame of the context
each function is emitted in (`A64.ctxOf`, the context
`Scc.Emit.A64.emitItemsMaps` passes to `emitFunc`). -/
theorem frame_le_of_frames {l : Lowered} {e : A64.Emitted} (h : A64.emitAll l = .ok e)
    (hb : ∀ n ∈ e.frames, n ≤ 32768) {f : Func} {fi : Nat} (hm : (f, fi) ∈ l.ir.funcs.zipIdx) :
    (A64.ctxOf l.ir fi f).frame ≤ 32768 := by
  obtain ⟨-, hf⟩ := A64.emitAll_frames h
  refine hb _ ?_
  rw [hf]
  exact List.mem_map.mpr ⟨(f, fi), hm, rfl⟩

end

end Scc.Lower.InvA64
