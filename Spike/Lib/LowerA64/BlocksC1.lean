/-
**The emitted code of an `Accepted1` code block's blocks with calls**
(AArch64): the emitter's code of each instruction and terminator the closed
form `lowerC` emits with the depth counter (`InstC`, `TermC`,
`Spike/Lib/LowerShapeC1.lean`), and of a call block `call{n+5}`
(`callBlk`, `Spike/Lib/LowerCallC1.lean`) split at its `bl`.

- `AllIns`, `allIns_*`: an item list whose directives are instructions
  only (no label, no data);
- `getArgs_one`, `callArgs_one`, `setResults_one`: one argument word in
  `x0`, one result word from `x0`;
- `getOps`, `getArgs_eq`, `callArgs_eq`, `allIns_getOps`, `callArgs_three`:
  up to eight register arguments, each operand's load into `x0`, `x1`, …
  in order (no stack argument), instructions only; the allocator's three;
- `fnCtx_maps`, `growth_progOf`: the emitter places a stack-map label after
  every call (`FnCtx.maps`) in every function of a program with
  `IR.Program.growth`, as `progOf` sets it;
- `inst_call1_inv`: a user call `call [d] f [w]` (`inst_call_inv`,
  `Spike/Lib/LowerA64/CallSite1.lean`, at one word each way) is `w`'s load
  into `x0`, `bl f`, the label `spK` and the store of `x0` into `d`'s slot;
- `inst_allIns`: every other `InstC` instruction's code is instructions
  only; `term_allIns`: so is a `ret`'s, a `br`'s; `term_unreachable`: the
  halt label and its self-branch;
- `instsItems_allIns`: the code of `InstC` instructions without a call is
  instructions only;
- `callSite_run`: with that, `callSite1`'s run before the `bl` starts at
  the block's label and is instructions only (`call_blockAt`'s premise);
- `callBlk_code`: the code of a call block `call{n+5}` numbered from `k` is
  `A ++ [bl wc_g] ++ .label spK :: B ++ C`: `A` the new depth's store and
  `w`'s load into `x0`, `B` the result's store, the thread-pointer read and
  the old depth's store (both instructions only), `C` the code of the rest
  of the block and its terminator.
-/
import Spike.Lib.LowerA64.Blocks1
import Spike.Lib.LowerA64.CallSite1
import Spike.Lib.LowerCallC1

namespace Spike.Lib.LowerA64

open Kraken Kraken.AArch64.Parser
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (isIns)
open Scc.Cert.Code1A64 (instsItems blockItems)
open Spike.Lib.LowerShape (InstC TermC)
open Spike.Lib.LowerCall (NoCall callBlk)

/-! ## Instructions only -/

/-- **The directives of `l` are instructions only** (no label, no data). -/
def AllIns (l : List Item) : Prop := (directives l).all isIns = true

theorem allIns_nil : AllIns [] := rfl

theorem allIns_append {l l' : List Item} (h : AllIns l) (h' : AllIns l') : AllIns (l ++ l') := by
  unfold AllIns at *
  rw [directives_append, List.all_append, h, h']; rfl

theorem allIns_ins {w : RegWidth} (op : Operation w) : AllIns [ins op] := by
  simp [AllIns, directives, ins, isIns]

theorem allIns_movImm (d : XReg) (n : Int) : AllIns (movImm d n) := by
  unfold AllIns; rw [directives_movImm]; exact movDs_ins _ _

theorem allIns_ldrOff (w : RegWidth) (rt : XReg) (base : RegOrSp .W64) (off : Int) :
    AllIns (ldrOff w rt base off) := by
  unfold ldrOff
  split
  · exact allIns_ins _
  · split
    · exact allIns_ins _
    · exact allIns_append (allIns_movImm _ _) (allIns_ins _)

theorem allIns_strOff (w : RegWidth) (rt : XReg) (base : RegOrSp .W64) (off : Int) :
    AllIns (strOff w rt base off) := by
  unfold strOff
  split
  · exact allIns_ins _
  · split
    · exact allIns_ins _
    · exact allIns_append (allIns_movImm _ _) (allIns_ins _)

/-- The value of a successful `bind`. -/
theorem bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem ok_inj {ε α : Type} {a b : α} (h : (Except.ok a : Except ε α) = .ok b) : a = b := by
  cases h; rfl

section Ctx

variable {cx : FnCtx}

theorem allIns_getReg {t : XReg} {r : Scc.IR.Reg} {l : List Item} (h : cx.getReg t r = .ok l) : AllIns l := by
  obtain ⟨off, -, h⟩ := bind_eq_ok h
  cases ok_inj h
  exact allIns_ldrOff _ _ _ _

theorem allIns_setReg {r : Scc.IR.Reg} {t : XReg} {l : List Item} (h : cx.setReg r t = .ok l) : AllIns l := by
  obtain ⟨off, -, h⟩ := bind_eq_ok h
  cases ok_inj h
  exact allIns_strOff _ _ _ _

theorem allIns_getOp {t : XReg} {a : Scc.IR.Operand} {l : List Item} (h : cx.getOp t a = .ok l) : AllIns l := by
  cases a with
  | reg r => exact allIns_getReg h
  | imm v => cases ok_inj h; exact allIns_movImm _ _

/-! ## One argument, one result -/

/-- One register argument: `w` into `x0`. -/
theorem getArgs_one (w : Scc.IR.Operand) : cx.getArgs [w] = cx.getOp .X0 w := by
  have ha : argRegs = .X0 :: argRegs.tail := rfl
  simp only [FnCtx.getArgs]
  rw [ha]
  cases hv : cx.getOp .X0 w <;>
    simp [hv, bind, Except.bind, pure, Except.pure, forIn, ForIn.forIn]

/-- One call argument: `w` into `x0` (no stack argument). -/
theorem callArgs_one (w : Scc.IR.Operand) (base : Nat) : cx.callArgs [w] base = cx.getOp .X0 w := by
  rw [← getArgs_one]
  cases hv : cx.getArgs [w] <;>
    simp [FnCtx.callArgs, argRegs, xregs, Scc.IR.maxArgs, hv, bind, Except.bind, pure, Except.pure, forIn,
      ForIn.forIn] <;>
    rw [show (List.drop 8 [w]).zipIdx = ([] : List (Scc.IR.Operand × Nat)) from rfl] <;> rfl

/-- One result: `x0` into `d`. -/
theorem setResults_one (d : Scc.IR.Reg) : cx.setResults [d] = cx.setReg d .X0 := by
  have ha : argRegs = .X0 :: argRegs.tail := rfl
  simp only [FnCtx.setResults]
  rw [ha]
  cases hv : cx.setReg d .X0 <;>
    simp [hv, Scc.IR.maxRets, bind, Except.bind, pure, Except.pure, forIn, ForIn.forIn]

/-! ## Up to eight register arguments -/

/-- **The loads of operands into registers**, in order: each operand's
`getOp` into its register, concatenated. -/
def getOps (cx : FnCtx) : List (Scc.IR.Operand × XReg) → Except String (List Item)
  | [] => .ok []
  | (a, r) :: rest => do return (← cx.getOp r a) ++ (← getOps cx rest)

/-- `getArgs`'s loop body: append the operand's load to the accumulator. -/
def getOpsStep (cx : FnCtx) (x : Scc.IR.Operand × XReg) (out : List Item) :
    Except String (ForInStep (List Item)) := do
  let v ← cx.getOp x.2 x.1
  pure (ForInStep.yield (out ++ v))

/-- `getArgs`'s loop: appending each operand's load to the accumulator is
the accumulator then `getOps`. -/
theorem forIn_getOps (l : List (Scc.IR.Operand × XReg)) (init : List Item) :
    forIn (m := Except String) l init (getOpsStep cx) =
      (match getOps cx l with
        | .error err => .error err
        | .ok v => .ok (init ++ v)) := by
  induction l generalizing init with
  | nil => simp [getOps, forIn, ForIn.forIn, pure, Except.pure]
  | cons p rest ih =>
    obtain ⟨a, r⟩ := p
    cases ha : cx.getOp r a with
    | error e => simp [getOps, getOpsStep, ha, List.forIn_cons, bind, Except.bind]
    | ok la =>
      simp only [List.forIn_cons, getOpsStep, ha, bind, Except.bind, pure, Except.pure]
      rw [ih]
      simp only [getOps, ha, bind, Except.bind, pure, Except.pure]
      cases hr : getOps cx rest <;> simp

/-- **At most eight register arguments**: `getArgs` is `getOps` of the
arguments zipped with `x0`, `x1`, …. -/
theorem getArgs_eq {args : List Scc.IR.Operand} (h : args.length ≤ 8) :
    cx.getArgs args = getOps cx (args.zip argRegs) := by
  have hl : ¬ args.length > argRegs.length := by simp [argRegs, xregs]; omega
  simp only [FnCtx.getArgs, hl, ite_false]
  rw [show (fun (x : Scc.IR.Operand × XReg) (out : List Item) => (do
      let v ← cx.getOp x.snd x.fst
      pure (ForInStep.yield (out ++ v)) : Except String (ForInStep (List Item)))) = getOpsStep cx from rfl,
    forIn_getOps]
  cases getOps cx (args.zip argRegs) <;> rfl

/-- **At most eight call arguments**: no stack argument, `callArgs` is
`getArgs`. -/
theorem callArgs_eq {args : List Scc.IR.Operand} (h : args.length ≤ 8) (base : Nat) :
    cx.callArgs args base = cx.getArgs args := by
  have hd : args.drop 8 = [] := List.drop_eq_nil_of_le h
  have ht : args.take 8 = args := List.take_of_length_le h
  have hm : ¬ args.length > Scc.IR.maxArgs := by simp [Scc.IR.maxArgs]; omega
  simp only [FnCtx.callArgs, hm, ite_false, argRegs, xregs]
  simp only [List.length_take, List.length_cons, List.length_nil]
  rw [show min 8 31 = 8 from rfl, hd, ht]
  cases cx.getArgs args <;> simp [forIn, ForIn.forIn, bind, Except.bind, pure, Except.pure]

/-- **The code of operands' loads is instructions only.** -/
theorem allIns_getOps : ∀ {l : List (Scc.IR.Operand × XReg)} {c : List Item}, getOps cx l = .ok c → AllIns c
  | [], c, h => by cases ok_inj h; exact allIns_nil
  | (a, r) :: rest, c, h => by
    simp only [getOps] at h
    obtain ⟨la, ha, h⟩ := bind_eq_ok h
    obtain ⟨lr, hr, h⟩ := bind_eq_ok h
    cases ok_inj h
    exact allIns_append (allIns_getOp ha) (allIns_getOps hr)

/-- **Three call arguments** (the allocator's `h`, `k`, `u`): `x0`, `x1`,
`x2`'s loads. -/
theorem callArgs_three (a b c : Scc.IR.Operand) (base : Nat) :
    cx.callArgs [a, b, c] base = (do
      let la ← cx.getOp .X0 a
      let lb ← cx.getOp .X1 b
      let lc ← cx.getOp .X2 c
      return la ++ (lb ++ lc)) := by
  rw [callArgs_eq (by simp) base, getArgs_eq (by simp)]
  show getOps cx [(a, .X0), (b, .X1), (c, .X2)] = _
  simp only [getOps]
  cases cx.getOp .X0 a <;> cases cx.getOp .X1 b <;> cases cx.getOp .X2 c <;>
    simp [bind, Except.bind, pure, Except.pure]

end Ctx

/-! ## Stack-map labels -/

/-- A function's context places stack-map labels after its calls when the
program has `IR.Program.growth`. -/
theorem fnCtx_maps (abortFn : String) (gr : Scc.IR.Growth) (areas : List (Scc.IR.Sym × Nat)) (fi : Nat)
    (f : Scc.IR.Func) : (fnCtx abortFn (some gr) areas fi f).maps = true := rfl

/-- **`progOf` has `IR.Program.growth`**, so every function's context
places stack-map labels after its calls (`fnCtx_maps`). -/
theorem growth_progOf (lay : Scc.Layout) (rt fs : List Scc.IR.Func) :
    (Scc.Lower.Inv.progOf lay rt fs).growth.isSome = true := rfl

section Emit

variable {cx : FnCtx}

/-- **The code of a one-word user call** `call [d] f [w]` numbered `k`
(stack maps on; `inst_call_inv` at one argument and one result): `w`'s load
`lw` into `x0`, `bl f`, the label `spK`, then `x0`'s store `ls` into `d`;
`lw` and `ls` are instructions only. -/
theorem inst_call1_inv (hm : cx.maps = true) {k : Nat} {d : Scc.IR.Reg} {f : Label} {w : Scc.IR.Operand}
    {ci : List Item} (h : cx.inst k (.call [d] f [w]) = .ok ci) :
    ∃ lw ls, cx.getOp .X0 w = .ok lw ∧ cx.setReg d .X0 = .ok ls ∧ AllIns lw ∧ AllIns ls ∧
      directives ci = directives lw ++ .instr ⟨.W64, .BL (.label f)⟩ ::
        .label (cx.local s!"sp{k}") :: directives ls := by
  obtain ⟨ca, sr, hca, hsr, hd⟩ := inst_call_inv hm h
  rw [callArgs_one] at hca
  rw [setResults_one] at hsr
  exact ⟨ca, sr, hca, hsr, allIns_getOp hca, allIns_setReg hsr, hd⟩

/-- **The code of every other `InstC` instruction is instructions only**:
a checked `+`, a saturating `-`, the thread-pointer read, the depth's
plain 64-bit load, store and increment. -/
theorem inst_allIns {k : Nat} {i : Scc.IR.Inst} (hi : InstC i) (hc : Spike.Lib.LowerShape.isCall i = false)
    {ci : List Item} (h : cx.inst k i = .ok ci) : AllIns ci := by
  cases hi with
  | addChk d p q =>
    simp only [FnCtx.inst] at h
    obtain ⟨la, ha, h⟩ := bind_eq_ok h
    obtain ⟨lb, hb, h⟩ := bind_eq_ok h
    obtain ⟨ls, hs, h⟩ := bind_eq_ok h
    cases ok_inj h
    refine allIns_append (allIns_append (allIns_append (allIns_getOp ha) (allIns_getOp hb)) ?_)
      (allIns_setReg hs)
    simp [AllIns, directives_addChecked, isIns]
  | subSat d p q =>
    simp only [FnCtx.inst] at h
    obtain ⟨la, ha, h⟩ := bind_eq_ok h
    obtain ⟨lb, hb, h⟩ := bind_eq_ok h
    obtain ⟨ls, hs, h⟩ := bind_eq_ok h
    cases ok_inj h
    refine allIns_append (allIns_append (allIns_append (allIns_getOp ha) (allIns_getOp hb)) ?_)
      (allIns_setReg hs)
    simp [AllIns, subSat, directives, ins, isIns]
  | getTp d =>
    simp only [FnCtx.inst] at h
    obtain ⟨ls, hs, h⟩ := bind_eq_ok h
    cases ok_inj h
    exact allIns_append (allIns_ins _) (allIns_setReg hs)
  | load d a =>
    simp only [FnCtx.inst] at h
    obtain ⟨lb, hb, h⟩ := bind_eq_ok h
    obtain ⟨body, hbody, h⟩ := bind_eq_ok h
    obtain ⟨ls, hs, h⟩ := bind_eq_ok h
    cases ok_inj h
    cases ok_inj hbody
    exact allIns_append (allIns_append (allIns_getReg hb) (allIns_ldrOff _ _ _ _)) (allIns_setReg hs)
  | store a v =>
    simp only [FnCtx.inst] at h
    obtain ⟨lv, hv, h⟩ := bind_eq_ok h
    obtain ⟨rel, hrel, h⟩ := bind_eq_ok h
    cases ok_inj hrel
    obtain ⟨lb, hb, h⟩ := bind_eq_ok h
    cases ok_inj h
    exact allIns_append (allIns_append (allIns_getOp hv) (allIns_getReg hb)) (allIns_strOff _ _ _ _)
  | inc d s =>
    simp only [FnCtx.inst] at h
    obtain ⟨la, ha, h⟩ := bind_eq_ok h
    obtain ⟨lb, hb, h⟩ := bind_eq_ok h
    obtain ⟨ls, hs, h⟩ := bind_eq_ok h
    cases ok_inj h
    refine allIns_append (allIns_append (allIns_append (allIns_getOp ha) (allIns_getOp hb)) ?_)
      (allIns_setReg hs)
    simp [AllIns, binOp, addReg, directives, ins, isIns]
  | call d g w _ => simp [Spike.Lib.LowerShape.isCall] at hc
  | abort => simp [Spike.Lib.LowerShape.isCall] at hc

/-- **The code of a `ret` or a `br`** (`TermC`) is instructions only. -/
theorem term_allIns {frames : Option Nat} {k : Nat} {t : Scc.IR.Term} (ht : TermC frames t)
    (hu : t ≠ .unreachable) {c2 : List Item} (h : cx.term k t = .ok c2) : AllIns c2 := by
  cases ht with
  | ret w _ =>
    cases hv : cx.getOp .X0 w with
    | error e =>
      have ha : argRegs = .X0 :: argRegs.tail := rfl
      simp only [FnCtx.term] at h
      rw [ha] at h
      simp [hv, Scc.IR.maxRets, bind, Except.bind, pure, Except.pure, forIn, ForIn.forIn] at h
    | ok lw =>
      rw [term_ret1 k hv] at h
      cases h
      refine allIns_append (allIns_append (allIns_getOp hv) ?_) (allIns_ins _)
      unfold AllIns FnCtx.leave
      rw [directives_append, directives_append, List.all_append, List.all_append]
      have := allIns_ldrOff .W64 .X29 spW64 ((cx.frame : Int) - 16)
      have := allIns_ldrOff .W64 .X30 spW64 ((cx.frame : Int) - 8)
      unfold AllIns at *
      simp only [*, Bool.true_and]
      unfold addImm
      split
      · simp [directives, ins, isIns]
      · simp [directives, ins, isIns]
      · exact allIns_append (allIns_movImm _ _) (allIns_ins _)
  | br p q l l' _ _ | depth d fr l l' _ =>
    simp only [FnCtx.term] at h
    obtain ⟨la, ha, h⟩ := bind_eq_ok h
    obtain ⟨lb, hb, h⟩ := bind_eq_ok h
    obtain ⟨T, -, h⟩ := bind_eq_ok h
    obtain ⟨F, -, h⟩ := bind_eq_ok h
    cases ok_inj h
    refine allIns_append (allIns_append (allIns_getOp ha) (allIns_getOp hb)) ?_
    simp [AllIns, cmpReg, jcc, jmp, directives, ins, isIns]
  | unreachable => exact absurd rfl hu

/-- **The code of `unreachable`**: the halt label and its self-branch. -/
theorem term_unreachable (k : Nat) :
    cx.term k .unreachable = .ok (halt (cx.local s!"halt{k}")) := rfl

end Emit

/-! ## A call block -/

section CallBlock

variable {cx : FnCtx}

theorem instsItems_append (k : Nat) :
    ∀ (xs ys : List Scc.IR.Inst) {c : List Item}, instsItems cx k (xs ++ ys) = .ok c →
      ∃ cx' cy, instsItems cx k xs = .ok cx' ∧ instsItems cx (k + xs.length) ys = .ok cy ∧ c = cx' ++ cy
  | [], ys, c, h => ⟨[], c, rfl, by simpa using h, rfl⟩
  | x :: xs, ys, c, h => by
    simp only [List.cons_append, instsItems] at h
    obtain ⟨ci, hci, h⟩ := bind_eq_ok h
    obtain ⟨cr, hcr, h⟩ := bind_eq_ok h
    cases ok_inj h
    obtain ⟨cx', cy, h1, h2, rfl⟩ := instsItems_append (k + 1) xs ys hcr
    refine ⟨ci ++ cx', cy, ?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using h2, by simp⟩
    simp [instsItems, hci, h1, bind, Except.bind, pure, Except.pure]

/-- **The code of a call block `call{n+5}`** numbered from `k`, stack-map
labels on, split at its `bl`: `A` (the new depth's store `c0`, then `w`'s
load `lw` into `x0`), `bl wc_g`, the label `sp{k+1}`, `B` (`x0`'s store
`ls` into `r%n`, the thread-pointer read `c2` and the old depth's store
`c3`), and `C`, the code `cr` of the rest of the block from `k + 4` and its
terminator's `ct`. `A` and `B` are instructions only. -/
theorem callBlk_code (hm : cx.maps = true) {k n : Nat} {g : String} {w : Scc.IR.Operand}
    {rest : List Scc.IR.Inst} {t : Scc.IR.Term} {code : List Item}
    (h : blockItems cx k (callBlk n g w rest t) = .ok code) :
    ∃ c0 lw ls c2 c3 cr ct,
      cx.getOp .X0 w = .ok lw ∧ cx.setReg (Scc.Lower.Inv.regName "r" n) .X0 = .ok ls ∧
      instsItems cx (k + 4) rest = .ok cr ∧ cx.term (k + 4 + rest.length) t = .ok ct ∧
      AllIns (c0 ++ lw) ∧ AllIns (ls ++ c2 ++ c3) ∧
      directives code = directives (c0 ++ lw) ++ .instr ⟨.W64, .BL (.label (Scc.Lower.Names.user g))⟩ ::
        .label (cx.local s!"sp{k + 1}") :: (directives (ls ++ c2 ++ c3) ++ directives (cr ++ ct)) := by
  simp only [blockItems] at h
  obtain ⟨ci, hci, h⟩ := bind_eq_ok h
  obtain ⟨ct, hct, h⟩ := bind_eq_ok h
  cases ok_inj h
  simp only [Scc.Lower.Inv.callPost] at hci hct
  obtain ⟨cp, cr, hcp, hcr, rfl⟩ := instsItems_append k _ rest hci
  simp only [instsItems] at hcp
  obtain ⟨c0, h0, hcp⟩ := bind_eq_ok hcp
  obtain ⟨cp1, hcp1, hcp⟩ := bind_eq_ok hcp
  cases ok_inj hcp
  obtain ⟨c1, h1, hcp1⟩ := bind_eq_ok hcp1
  obtain ⟨cp2, hcp2, hcp1⟩ := bind_eq_ok hcp1
  cases ok_inj hcp1
  obtain ⟨c2, h2, hcp2⟩ := bind_eq_ok hcp2
  obtain ⟨cp3, hcp3, hcp2⟩ := bind_eq_ok hcp2
  cases ok_inj hcp2
  obtain ⟨c3, h3, hcp3⟩ := bind_eq_ok hcp3
  obtain ⟨cp4, hcp4, hcp3⟩ := bind_eq_ok hcp3
  cases ok_inj hcp3
  cases ok_inj hcp4
  obtain ⟨lw, ls, hw, hs, hlw, hls, hd⟩ := inst_call1_inv hm h1
  have a0 : AllIns c0 := inst_allIns (.store _ _) rfl h0
  have a2 : AllIns c2 := inst_allIns (.getTp _) rfl h2
  have a3 : AllIns c3 := inst_allIns (.store _ _) rfl h3
  have e4 : k + (rest.length + 1 + 1 + 1 + 1) = k + 4 + rest.length := by omega
  simp only [List.length_cons, List.cons_append, List.nil_append] at hct
  rw [e4] at hct
  refine ⟨c0, lw, ls, c2, c3, cr, ct, hw, hs, by simpa using hcr, hct,
    allIns_append a0 hlw, allIns_append (allIns_append hls a2) a3, ?_⟩
  simp only [directives_append, hd, List.append_assoc, List.cons_append, List.append_nil]

/-- **The code of instructions without a call is instructions only**
(`InstC`, no `call`). -/
theorem instsItems_allIns :
    ∀ {k : Nat} {is : List Scc.IR.Inst} {c : List Item}, (∀ i ∈ is, InstC i) → NoCall is →
      instsItems cx k is = .ok c → AllIns c
  | _, [], c, _, _, h => by cases ok_inj h; exact allIns_nil
  | k, i :: is, c, hs, hn, h => by
    simp only [instsItems] at h
    obtain ⟨ci, hci, h⟩ := bind_eq_ok h
    obtain ⟨cr, hcr, h⟩ := bind_eq_ok h
    cases ok_inj h
    exact allIns_append (inst_allIns (hs i (by simp)) (hn i (by simp)) hci)
      (instsItems_allIns (fun j hj => hs j (by simp [hj])) (fun j hj => hn j (by simp [hj])) hcr)

/-- **The run before a call's `bl`** (`callSite1`'s `X ++ ys`) when the
code before the `bl` is instructions only: no label `X`, the run from the
block's label `l`, and `ys` instructions only (`call_blockAt`'s premise). -/
theorem callSite_run {c1 ca : List Item} {X ys : List Directive} {L l : Label}
    (h1 : AllIns c1) (ha : AllIns ca) (hX : (X = [] ∧ L = l) ∨ ∃ X', X = X' ++ [.label L])
    (he : directives c1 ++ directives ca = X ++ ys) :
    X = [] ∧ L = l ∧ ys = directives c1 ++ directives ca ∧ ys.all isIns = true := by
  have hall : (X ++ ys).all isIns = true := by
    rw [← he, List.all_append]; unfold AllIns at h1 ha; rw [h1, ha]; rfl
  rcases hX with ⟨rfl, rfl⟩ | ⟨X', rfl⟩
  · simp only [List.nil_append] at he hall
    exact ⟨rfl, rfl, he.symm, hall⟩
  · simp [List.all_append, isIns] at hall

end CallBlock

end Spike.Lib.LowerA64
