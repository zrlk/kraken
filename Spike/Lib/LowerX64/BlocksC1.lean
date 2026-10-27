/-
**The emitted code of an `Accepted1` code block's blocks with calls**
(x86-64): the emitter's code of each instruction and terminator the closed
form `lowerC` emits with the depth counter (`InstC`, `TermC`,
`Spike/Lib/LowerShapeC1.lean`), and of a call block `call{n+5}`
(`callBlk`, `Spike/Lib/LowerCallC1.lean`) split at its `callq`; the twin
of `Spike/Lib/LowerA64/BlocksC1.lean`.

- `AllIns`, `allIns_*`: an item list whose directives are label-free;
- `Emits`, `Emits.seq`, `emits_*`: an emitter action appends the same
  items from every state (and leaves the label counter and the safepoints
  as they are);
- `callArgs_one`, `stores_one_eq`: one argument word into `%rdi`, one
  result word from `%rax`;
- `getOps`, `callArgs_eq`, `callArgs_getOps`, `callArgs_ok`,
  `allIns_getOps`, `callArgs_three`: up to six register arguments, each
  operand's load into `%rdi`, `%rsi`, … in order (no stack argument),
  label-free; the allocator's three;
- `frOf_maps`, `growth_progOf`: a function's frame records safepoints
  after its calls in a program with `IR.Program.growth`, as `progOf` sets
  it;
- `emitInst_call1_inv`: a user call `call [d] f [w]` (stack maps on) is
  `w`'s load into `%rdi`, `callq f`, the return label `.L<fn>.x<k>` (`k`
  the label counter before the call) and the store of `%rax` into `d`'s
  slot;
- `emitInst_allIns`: every other `InstC` instruction's code is label-free
  and the same from every state; `emitTerm_allIns`: so is every `TermC`
  terminator's (`unreachable` is `ud2`);
- `instsCode_allIns`: the code of `InstC` instructions without a call;
- `callBlk_code`: the code of a call block `call{n+5}` numbered from `k`
  is `A ++ [callq g, .L<fn>.x<k>:] ++ B ++ C`: `A` the new depth's store
  and `w`'s load into `%rdi`, `B` the result's store, the thread-pointer
  read and the old depth's store, `C` the code of the rest of the block and
  its terminator (all label-free); the next label number is `k + 1`;
- `callSite_run`: with that, `callSite1`'s split of the block's code at its
  `callq` has no label before it (`Xd = []`, `L` the block's label) and its
  run before the `callq` is `A`'s directives.

Where x86-64 differs from AArch64: the emitter is a state monad (`E`), so
an instruction's code is stated as the items it appends from every state
(`Emits`) rather than an `Except` value; the argument register is `%rdi`
and the result register `%rax`; the return label is the label counter's
`.L<fn>.x<k>` (no call before it in the block takes a label); the
`unreachable` terminator is one `ud2` (no halt label), so every `TermC`
terminator is label-free; label-freeness is all `call_blockAt` needs
(`isLabel`, no `isIns`).
-/
import Spike.Lib.LowerX64.Blocks1
import Spike.Lib.LowerX64.CallSite1
import Spike.Lib.LowerCallC1

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Emit.X64 (S E Item emitInst emitTerm ld st ins labelOf cmpAB directives i64 rel xr xm om or_ mem
  callArgs loadArgs argRegs retRegs safepoint)
open Scc.Lower.InvX64
open Spike.Lib.LowerShape (InstC TermC isCall)
open Spike.Lib.LowerCall (NoCall callBlk)

/-! ## Label-free items -/

/-- **The directives of `l` are label-free.** -/
def AllIns (l : List Item) : Prop := (directives l).all (fun d => !d.isLabel) = true

theorem allIns_nil : AllIns [] := rfl

theorem allIns_append {l l' : List Item} (h : AllIns l) (h' : AllIns l') : AllIns (l ++ l') := by
  unfold AllIns at *
  rw [directives_eq_dirs] at *
  rw [dirs_append, List.all_append, h, h']; rfl

theorem allIns_d {d : Directive} (h : d.isLabel = false) : AllIns [.d d] := by
  simp [AllIns, directives_eq_dirs, dirs, h]

theorem allIns_getOp {fr : Scc.Emit.X64.Frame} {t : Reg64} {a : Scc.IR.Operand} {l : List Item}
    (h : getOp fr t a = .ok l) : AllIns l := by
  unfold AllIns
  rw [directives_eq_dirs]
  rcases getOp_cases h with ⟨_, _, _, _, hl⟩ | ⟨_, _, hl⟩ <;> rw [hl] <;> rfl

/-- The `AllIns` of a list of appended parts. -/
macro "allIns_tac" : tactic => `(tactic| repeat (first
  | (apply allIns_append) | (exact allIns_nil) | (exact allIns_getOp ‹_›) | (exact allIns_d rfl)))

/-! ## Emitted items -/

/-- **`x` appends the items `c`** from every state, leaving the label
counter and the safepoints as they are. -/
def Emits (x : E Unit) (c : List Item) : Prop := ∀ s : S, x s = .ok ((), { s with out := c.reverse ++ s.out })

theorem Emits.seq {x y : E Unit} {c c' : List Item} (hx : Emits x c) (hy : Emits y c') :
    Emits (x >>= fun _ => y) (c ++ c') := by
  intro s
  rw [bind_ok (hx s), hy]
  simp [List.reverse_append, List.append_assoc]

theorem emits_pure : Emits (pure () : E Unit) [] := fun _ => rfl

theorem emits_ins (d : Directive) : Emits (ins d) [.d d] := ins_eq d

theorem emits_ld {fr : Scc.Emit.X64.Frame} {t : Reg64} {a : Scc.IR.Operand} {l : List Item}
    (h : getOp fr t a = .ok l) : Emits (ld fr a t) l := ld_getOp h

theorem emits_st {fr : Scc.Emit.X64.Frame} {d : Scc.IR.Reg} {off : Int} (h : rsOf fr d = some off) :
    Emits (st fr .rax d) [.d (stDir off)] := by
  intro s
  cases hf : fr.slots.find? (·.1 == d) with
  | none =>
    simp only [rsOf, Scc.Emit.X64.Frame.slotOff, hf] at h
    cases h
  | some v =>
    obtain ⟨r', k⟩ := v
    have h' := rsOf_eq (Scc.Lower.InvX64.slotOff_find hf {})
    rw [h] at h'
    cases h'
    exact Scc.Lower.InvX64.st_eq (Scc.Lower.InvX64.slotOff_find hf _) _

theorem ld_ok {fr : Scc.Emit.X64.Frame} {t : Reg64} {a : Scc.IR.Operand} {s s' : S} {u : Unit}
    (h : ld fr a t s = .ok (u, s')) : ∃ l, getOp fr t a = .ok l := by
  rcases ld_cases fr a t s with ⟨l, hl, -⟩ | ⟨e, he⟩
  · exact ⟨l, hl⟩
  · rw [he] at h; cases h

theorem st_ok {fr : Scc.Emit.X64.Frame} {d : Scc.IR.Reg} {s s' : S} {u : Unit}
    (h : st fr .rax d s = .ok (u, s')) : ∃ off, rsOf fr d = some off := by
  rcases st_cases fr d s with ⟨off, hd, -⟩ | ⟨e, he⟩
  · exact ⟨off, hd⟩
  · rw [he] at h; cases h

/-! ## One argument, one result -/

/-- **One call argument**: `callArgs` of one word is its load into `%rdi`
(no stack argument). -/
theorem callArgs_one_eq (fr : Scc.Emit.X64.Frame) (w : Scc.IR.Operand) (what : String) :
    callArgs fr [w] what = (ld fr w .rdi >>= fun _ => pure ()) := by
  have h1 : ¬ [w].length > Scc.IR.maxArgs := by simp [Scc.IR.maxArgs]
  have h2 : ¬ ([w].take argRegs.length).length > argRegs.length := by simp [argRegs]
  simp only [callArgs, loadArgs, h1, h2, ite_false]
  rw [show List.drop argRegs.length [w] = [] from rfl,
    show (List.take argRegs.length [w]).zip argRegs = [(w, .rdi)] from rfl]
  simp only [List.zipIdx_nil, List.forIn_nil, List.forIn_cons, pure_bind, bind_assoc]

/-- **One call argument's code**: `w`'s load into `%rdi`. -/
theorem callArgs_one {fr : Scc.Emit.X64.Frame} {w : Scc.IR.Operand} {l : List Item} (h : getOp fr .rdi w = .ok l)
    (what : String) : Emits (callArgs fr [w] what) l := by
  intro s
  rw [callArgs_one_eq, bind_ok (ld_getOp h s)]
  rfl

/-- **One result**: the results' stores of one word are `%rax`'s store. -/
theorem stores_one_eq (fr : Scc.Emit.X64.Frame) (d : Scc.IR.Reg) :
    (forIn (m := E) ([d].zip retRegs) PUnit.unit fun (x : Scc.IR.Reg × Reg64) (_ : PUnit) => do
      st fr x.2 x.1; pure (ForInStep.yield PUnit.unit)) = (st fr .rax d >>= fun _ => pure PUnit.unit) := by
  rw [show [d].zip retRegs = [(d, .rax)] from rfl]
  simp only [List.forIn_cons, List.forIn_nil, bind_assoc, pure_bind]

/-! ## Up to six register arguments -/

/-- The value of a successful `bind` of `Except`. -/
theorem exc_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- **The loads of operands into registers**, in order: each operand's
`getOp` into its register, concatenated. -/
def getOps (fr : Scc.Emit.X64.Frame) : List (Scc.IR.Operand × Reg64) → Except String (List Item)
  | [] => .ok []
  | (a, r) :: rest => do return (← getOp fr r a) ++ (← getOps fr rest)

/-- `loadArgs`'s loop: each operand's load into its register. -/
abbrev ldsLoop (fr : Scc.Emit.X64.Frame) (l : List (Scc.IR.Operand × Reg64)) : E PUnit :=
  forIn (m := E) l PUnit.unit fun (x : Scc.IR.Operand × Reg64) (_ : PUnit) => do
    ld fr x.1 x.2; pure (ForInStep.yield PUnit.unit)

/-- **The loads' loop appends `getOps`'s items.** -/
theorem ldsLoop_emits {fr : Scc.Emit.X64.Frame} :
    ∀ {l : List (Scc.IR.Operand × Reg64)} {c : List Item}, getOps fr l = .ok c →
      Emits (ldsLoop fr l >>= fun _ => pure ()) c
  | [], c, h => by cases h; intro s; rfl
  | (a, r) :: rest, c, h => by
    simp only [getOps] at h
    obtain ⟨la, ha, h⟩ := exc_bind_ok h
    obtain ⟨lr, hr, h⟩ := exc_bind_ok h
    cases h
    intro s
    have e := ldsLoop_emits hr { s with out := la.reverse ++ s.out }
    simp only [ldsLoop, List.forIn_cons, bind_assoc, pure_bind] at e ⊢
    rw [bind_ok (ld_getOp ha s), e]
    simp [List.reverse_append, List.append_assoc]

/-- **The loads' loop succeeds only when every load does** (`getOps`). -/
theorem ldsLoop_ok {fr : Scc.Emit.X64.Frame} :
    ∀ {l : List (Scc.IR.Operand × Reg64)} {s s' : S},
      (ldsLoop fr l >>= fun _ => pure ()) s = .ok ((), s') → ∃ c, getOps fr l = .ok c
  | [], _, _, _ => ⟨[], rfl⟩
  | (a, r) :: rest, s, s', h => by
    simp only [ldsLoop, List.forIn_cons, bind_assoc, pure_bind] at h
    obtain ⟨u, s1, h1, h⟩ := bind_inv h
    obtain ⟨la, ha⟩ := ld_ok h1
    obtain ⟨lr, hr⟩ := ldsLoop_ok (l := rest) (by simpa [ldsLoop] using h)
    exact ⟨la ++ lr, by simp [getOps, ha, hr, bind, Except.bind, pure, Except.pure]⟩

/-- **At most six call arguments**: no stack argument, `callArgs` is the
loads of the arguments zipped with `%rdi`, `%rsi`, …. -/
theorem callArgs_eq (fr : Scc.Emit.X64.Frame) {args : List Scc.IR.Operand} (h : args.length ≤ 6) (what : String) :
    callArgs fr args what = (ldsLoop fr (args.zip argRegs) >>= fun _ => pure ()) := by
  have hd : args.drop argRegs.length = [] := List.drop_eq_nil_of_le (by simpa [argRegs] using h)
  have ht : args.take argRegs.length = args := List.take_of_length_le (by simpa [argRegs] using h)
  have h1 : ¬ args.length > Scc.IR.maxArgs := by simp [Scc.IR.maxArgs]; omega
  have h2 : ¬ args.length > argRegs.length := by simp [argRegs]; omega
  simp only [callArgs, loadArgs, h1, ite_false, hd, ht, h2, List.zipIdx_nil, List.forIn_nil, pure_bind]

/-- **At most six call arguments' code**: `getOps`'s. -/
theorem callArgs_getOps {fr : Scc.Emit.X64.Frame} {args : List Scc.IR.Operand} (h : args.length ≤ 6)
    {c : List Item} (hg : getOps fr (args.zip argRegs) = .ok c) (what : String) :
    Emits (callArgs fr args what) c := by
  rw [callArgs_eq fr h]; exact ldsLoop_emits hg

/-- **At most six call arguments succeed only with their loads** (`getOps`). -/
theorem callArgs_ok {fr : Scc.Emit.X64.Frame} {args : List Scc.IR.Operand} (h : args.length ≤ 6) {what : String}
    {s s' : S} (hc : callArgs fr args what s = .ok ((), s')) : ∃ c, getOps fr (args.zip argRegs) = .ok c := by
  rw [callArgs_eq fr h] at hc; exact ldsLoop_ok hc

/-- **The code of operands' loads is label-free.** -/
theorem allIns_getOps {fr : Scc.Emit.X64.Frame} :
    ∀ {l : List (Scc.IR.Operand × Reg64)} {c : List Item}, getOps fr l = .ok c → AllIns c
  | [], c, h => by cases h; exact allIns_nil
  | (a, r) :: rest, c, h => by
    simp only [getOps] at h
    obtain ⟨la, ha, h⟩ := exc_bind_ok h
    obtain ⟨lr, hr, h⟩ := exc_bind_ok h
    cases h
    exact allIns_append (allIns_getOp ha) (allIns_getOps hr)

/-- **Three call arguments** (the allocator's `h`, `k`, `u`): `%rdi`,
`%rsi`, `%rdx`'s loads. -/
theorem callArgs_three (fr : Scc.Emit.X64.Frame) (a b c : Scc.IR.Operand) :
    getOps fr ([a, b, c].zip argRegs) = (do
      let la ← getOp fr .rdi a
      let lb ← getOp fr .rsi b
      let lc ← getOp fr .rdx c
      return la ++ (lb ++ lc)) := by
  show getOps fr [(a, .rdi), (b, .rsi), (c, .rdx)] = _
  simp only [getOps]
  cases getOp fr .rdi a <;> cases getOp fr .rsi b <;> cases getOp fr .rdx c <;>
    simp [bind, Except.bind, pure, Except.pure]

/-! ## Stack-map labels -/

/-- **`progOf` has `IR.Program.growth`**, so every function's frame
records safepoints after its calls (`frOf_maps`). -/
theorem growth_progOf (lay : Scc.Layout) (rt fs : List Scc.IR.Func) :
    (Scc.Lower.Inv.progOf lay rt fs).growth.isSome = true := rfl

/-- A function's frame records safepoints after its calls when the program
has `IR.Program.growth`. -/
theorem frOf_maps {ir : Scc.IR.Program} (h : ir.growth.isSome = true) (f : Scc.IR.Func) : (frOf ir f).maps = true := h

/-! ## The code of a one-word user call -/

/-- **The code of a one-word user call** `call [d] f [w]` (stack maps on)
from a state `s`: `w`'s load `lw` into `%rdi`, `callq f`, the return label
`.L<fn>.x<k>` at the label counter `k` of `s`, then `%rax`'s store into
`d`'s slot `off`; the counter is `k + 1` after it. -/
theorem emitInst_call1_inv {fr : Scc.Emit.X64.Frame} (hm : fr.maps = true) {sm : Option Scc.IR.StackMap.Entry}
    {d : Scc.IR.Reg} {f : Scc.IR.Sym} {w : Scc.IR.Operand} {s s' : S}
    (h : emitInst fr sm (.call [d] f [w]) s = .ok ((), s')) :
    ∃ lw off mp, getOp fr .rdi w = .ok lw ∧ rsOf fr d = some off ∧ AllIns lw ∧
      s' = { out := (lw ++ [Item.d (i64 (.call (rel f))), Item.d (.label s!".L{fr.fn}.x{s.next}")] ++
        [Item.d (stDir off)]).reverse ++ s.out, next := s.next + 1, maps := mp } := by
  have h0 : ¬ [d].length > retRegs.length := by simp [retRegs]
  simp only [emitInst, h0, ite_false] at h
  obtain ⟨u1, s1, h1, h⟩ := bind_inv h
  rw [callArgs_one_eq] at h1
  obtain ⟨u0, s0, h10, h11⟩ := bind_inv h1
  obtain ⟨lw, hw⟩ := ld_ok h10
  rw [ld_getOp hw s] at h10
  cases h10
  cases h11
  obtain ⟨u2, s2, h2, h⟩ := bind_inv h
  cases h2
  obtain ⟨u3, s3, h3, h⟩ := bind_inv h
  have hs3 : ∃ mp, s3 = { out := Item.d (.label s!".L{fr.fn}.x{s.next}") :: Item.d (i64 (.call (rel f))) ::
      (lw.reverse ++ s.out), next := s.next + 1, maps := mp } := by
    unfold safepoint at h3
    simp only [hm, ite_true] at h3
    obtain ⟨l, t1, e1, h3⟩ := bind_inv h3
    cases e1
    obtain ⟨u, t2, e2, h3⟩ := bind_inv h3
    cases e2
    obtain ⟨st1, t3, e3, h3⟩ := bind_inv h3
    have := mapM_slotOff_state fr _ e3
    subst this
    obtain ⟨hp1, t4, e4, h3⟩ := bind_inv h3
    have := mapM_slotOff_state fr _ e4
    subst this
    cases h3
    exact ⟨_, rfl⟩
  obtain ⟨mp, rfl⟩ := hs3
  rw [stores_one_eq] at h
  obtain ⟨u4, s4, h4, h⟩ := bind_inv h
  obtain ⟨u5, s5, h5, h4⟩ := bind_inv h4
  obtain ⟨off, hd⟩ := st_ok h5
  rw [emits_st hd] at h5
  cases h5
  cases h4
  cases h
  refine ⟨lw, off, mp, hw, hd, allIns_getOp hw, ?_⟩
  simp [List.reverse_append, List.append_assoc]

/-! ## Every other instruction, every terminator -/

/-- **The code of every other `InstC` instruction** is the same items from
every state, label-free: a checked `+`, a saturating `-`, the
thread-pointer read, the depth's plain 64-bit load, store and increment. -/
theorem emitInst_allIns {fr : Scc.Emit.X64.Frame} {sm : Option Scc.IR.StackMap.Entry} {i : Scc.IR.Inst}
    (hi : InstC i) (hc : isCall i = false) {s s' : S} (h : emitInst fr sm i s = .ok ((), s')) :
    ∃ c, Emits (emitInst fr sm i) c ∧ AllIns c := by
  cases hi with
  | addChk d p q =>
    obtain ⟨la, lb, off, ha, hb, hd, -⟩ := emitInst_add_cases fr sm d p q s h
    rw [Scc.Lower.InvX64.emitInst_addChk]
    exact ⟨_, (emits_ld ha).seq ((emits_ld hb).seq ((emits_ins _).seq ((emits_ins _).seq (emits_st hd)))),
      by allIns_tac⟩
  | subSat d p q =>
    obtain ⟨la, lb, off, ha, hb, hd, -⟩ := emitInst_sub_cases fr sm d p q s h
    simp only [emitInst]
    exact ⟨_, (emits_ld ha).seq ((emits_ld hb).seq ((emits_ins _).seq ((emits_ins _).seq
      ((emits_ins _).seq (emits_st hd))))), by allIns_tac⟩
  | getTp d =>
    simp only [emitInst] at h ⊢
    obtain ⟨u1, s1, h1, h⟩ := bind_inv h
    obtain ⟨off, hd⟩ := st_ok h
    exact ⟨_, (emits_ins _).seq (emits_st hd), by allIns_tac⟩
  | load d a =>
    simp only [emitInst] at h ⊢
    obtain ⟨u1, s1, h1, h⟩ := bind_inv h
    obtain ⟨lb, hb⟩ := ld_ok h1
    obtain ⟨u2, s2, h2, h⟩ := bind_inv h
    obtain ⟨off, hd⟩ := st_ok h
    exact ⟨_, (emits_ld hb).seq ((emits_ins _).seq (emits_st hd)), by allIns_tac⟩
  | store a v =>
    simp only [emitInst] at h ⊢
    obtain ⟨u1, s1, h1, h⟩ := bind_inv h
    obtain ⟨lb, hb⟩ := ld_ok h1
    obtain ⟨u2, s2, h2, h⟩ := bind_inv h
    obtain ⟨lv, hv⟩ := ld_ok h2
    exact ⟨_, (emits_ld hb).seq ((emits_ld hv).seq (emits_ins _)), by allIns_tac⟩
  | inc d r =>
    simp only [emitInst] at h ⊢
    obtain ⟨u1, s1, h1, h⟩ := bind_inv h
    obtain ⟨la, ha⟩ := ld_ok h1
    obtain ⟨u2, s2, h2, h⟩ := bind_inv h
    obtain ⟨lb, hb⟩ := ld_ok h2
    obtain ⟨u3, s3, h3, h⟩ := bind_inv h
    obtain ⟨off, hd⟩ := st_ok h
    exact ⟨_, (emits_ld ha).seq ((emits_ld hb).seq ((emits_ins _).seq (emits_st hd))), by allIns_tac⟩
  | call d g w => simp [isCall] at hc
  | abort => simp [isCall] at hc

/-- **The code of every `TermC` terminator** is the same items from every
state, label-free: a one-word `ret`, a `br` (an `if`'s, the bracket's) and
`unreachable`'s `ud2`. -/
theorem emitTerm_allIns {fr : Scc.Emit.X64.Frame} {frames : Option Nat} {t : Scc.IR.Term} (ht : TermC frames t)
    {s s' : S} (h : emitTerm fr t s = .ok ((), s')) : ∃ c, Emits (emitTerm fr t) c ∧ AllIns c := by
  cases ht with
  | ret w =>
    rw [emitTerm_ret1] at h ⊢
    obtain ⟨u1, s1, h1, h⟩ := bind_inv h
    obtain ⟨l, hl⟩ := ld_ok h1
    exact ⟨_, (emits_ld hl).seq ((((emits_ins _).seq (emits_ins _))).seq (emits_ins _)), by allIns_tac⟩
  | br p q t f =>
    simp only [emitTerm, cmpAB] at h ⊢
    obtain ⟨u1, s1, h1, h⟩ := bind_inv h
    obtain ⟨u0, s0, h0, h1⟩ := bind_inv h1
    obtain ⟨la, ha⟩ := ld_ok h0
    obtain ⟨u2, s2, h2, h1⟩ := bind_inv h1
    obtain ⟨lb, hb⟩ := ld_ok h2
    exact ⟨_, ((emits_ld ha).seq ((emits_ld hb).seq (emits_ins _))).seq ((emits_ins _).seq (emits_ins _)),
      by allIns_tac⟩
  | depth d fr' t f =>
    simp only [emitTerm, cmpAB] at h ⊢
    obtain ⟨u1, s1, h1, h⟩ := bind_inv h
    obtain ⟨u0, s0, h0, h1⟩ := bind_inv h1
    obtain ⟨la, ha⟩ := ld_ok h0
    obtain ⟨u2, s2, h2, h1⟩ := bind_inv h1
    obtain ⟨lb, hb⟩ := ld_ok h2
    exact ⟨_, ((emits_ld ha).seq ((emits_ld hb).seq (emits_ins _))).seq ((emits_ins _).seq (emits_ins _)),
      by allIns_tac⟩
  | unreachable => exact ⟨_, emits_ins _, by allIns_tac⟩

/-! ## A block's instructions without a call -/

theorem instsCode_nil_ms (fr : Scc.Emit.X64.Frame) (is : List Scc.IR.Inst) (s : S) :
    instsCode fr is [] s = .ok ((), s) := by
  simp [instsCode]; rfl

theorem emits_nil {x : E Unit} (h : ∀ s, x s = .ok ((), s)) : Emits x [] := by
  intro s; rw [h]; rfl

/-- **The code of instructions without a call** (`InstC`, no `call`) is the
same items from every state, label-free. -/
theorem instsCode_allIns {fr : Scc.Emit.X64.Frame} :
    ∀ {is : List Scc.IR.Inst} {ms : List (Option Scc.IR.StackMap.Entry)} {s s' : S},
      (∀ i ∈ is, InstC i) → NoCall is → instsCode fr is ms s = .ok ((), s') →
        ∃ c, Emits (instsCode fr is ms) c ∧ AllIns c
  | [], ms, _, _, _, _, _ => ⟨[], emits_nil (instsCode_nil fr ms), allIns_nil⟩
  | _ :: _, [], _, _, _, _, _ => ⟨[], emits_nil (instsCode_nil_ms fr _), allIns_nil⟩
  | i :: is, m :: ms, s, s', hs, hn, h => by
    rw [instsCode_cons] at h ⊢
    obtain ⟨u, s1, h1, h2⟩ := bind_inv h
    obtain ⟨ci, ei, ai⟩ := emitInst_allIns (hs i (by simp)) (hn i (by simp)) h1
    obtain ⟨cr, er, ar⟩ := instsCode_allIns (fun j hj => hs j (by simp [hj])) (fun j hj => hn j (by simp [hj])) h2
    exact ⟨_, ei.seq er, allIns_append ai ar⟩

/-! ## A call block -/

/-- **The code of a call block `call{n+5}`** numbered from `k` (stack maps
on, a map for each of its first four instructions), split at its `callq`:
`A` (the new depth's store `c0`, then `w`'s load `lw` into `%rdi`), `callq
g`, the return label `.L<fn>.x<k>`, `B` (`%rax`'s store into `r%n`'s slot
`off`, the thread-pointer read `c2` and the old depth's store `c3`), and
`C`, the code `cr` of the rest of the block and its terminator's `ct`; each
instruction's and the terminator's code the same from every state, all
label-free, and the next label number `k + 1`. -/
theorem callBlk_code {fr : Scc.Emit.X64.Frame} (hm : fr.maps = true) {frames : Option Nat} {k n : Nat}
    {g : String} {w : Scc.IR.Operand} {rest : List Scc.IR.Inst} {t : Scc.IR.Term}
    {m0 m1 m2 m3 : Option Scc.IR.StackMap.Entry} {ms : List (Option Scc.IR.StackMap.Entry)}
    {code : List Item} {n' : Nat}
    (hr : ∀ i ∈ rest, InstC i) (hn : NoCall rest) (ht : TermC frames t)
    (h : Scc.Cert.Code1X64.blockItems fr k (callBlk n g w rest t) (m0 :: m1 :: m2 :: m3 :: ms) = .ok (code, n')) :
    ∃ c0 lw off c2 c3 cr ct,
      Emits (emitInst fr m0 ((Scc.Lower.Inv.callPost g w n)[0]'(by simp [Scc.Lower.Inv.callPost]))) c0 ∧
      getOp fr .rdi w = .ok lw ∧ rsOf fr (Scc.Lower.Inv.regName "r" n) = some off ∧
      Emits (emitInst fr m2 ((Scc.Lower.Inv.callPost g w n)[2]'(by simp [Scc.Lower.Inv.callPost]))) c2 ∧
      Emits (emitInst fr m3 ((Scc.Lower.Inv.callPost g w n)[3]'(by simp [Scc.Lower.Inv.callPost]))) c3 ∧
      Emits (instsCode fr rest ms) cr ∧ Emits (emitTerm fr t) ct ∧
      AllIns (c0 ++ lw) ∧ AllIns ([Item.d (stDir off)] ++ c2 ++ c3) ∧ AllIns (cr ++ ct) ∧ n' = k + 1 ∧
      code = (c0 ++ lw) ++ [Item.d (i64 (.call (rel (Scc.Lower.Names.user g)))),
        Item.d (.label s!".L{fr.fn}.x{k}")] ++ ([Item.d (stDir off)] ++ c2 ++ c3) ++ (cr ++ ct) := by
  unfold Scc.Cert.Code1X64.blockItems at h
  split at h
  · rename_i s hrun
    cases h
    have hrun' : Scc.Cert.Code1X64.blockCode fr (callBlk n g w rest t) (m0 :: m1 :: m2 :: m3 :: ms)
        { next := k } = .ok ((), s) := hrun
    rw [blockCode_eq] at hrun'
    obtain ⟨u, s1, hI, hT⟩ := bind_inv hrun'
    simp only [Scc.Lower.Inv.callPost, List.cons_append, List.nil_append] at hI
    rw [instsCode_cons] at hI
    obtain ⟨u0, t0, h0, hI⟩ := bind_inv hI
    obtain ⟨c0, e0, a0⟩ := emitInst_allIns (.store _ _) rfl h0
    rw [e0] at h0; cases h0
    rw [instsCode_cons] at hI
    obtain ⟨u1, t1, h1, hI⟩ := bind_inv hI
    obtain ⟨lw, off, mp, hw, hd, aw, rfl⟩ := emitInst_call1_inv hm h1
    rw [instsCode_cons] at hI
    obtain ⟨u2, t2, h2, hI⟩ := bind_inv hI
    obtain ⟨c2, e2, a2⟩ := emitInst_allIns (.getTp _) rfl h2
    rw [e2] at h2; cases h2
    rw [instsCode_cons] at hI
    obtain ⟨u3, t3, h3, hI⟩ := bind_inv hI
    obtain ⟨c3, e3, a3⟩ := emitInst_allIns (.store _ _) rfl h3
    rw [e3] at h3; cases h3
    obtain ⟨cr, er, ar⟩ := instsCode_allIns hr hn hI
    rw [er] at hI; cases hI
    obtain ⟨ct, et, at'⟩ := emitTerm_allIns ht hT
    rw [et] at hT; cases hT
    refine ⟨c0, lw, off, c2, c3, cr, ct, e0, hw, hd, e2, e3, er, et, allIns_append a0 aw,
      allIns_append (allIns_append (allIns_d rfl) a2) a3, allIns_append ar at', rfl, ?_⟩
    simp [List.reverse_append, List.append_assoc]
  · cases h

/-! ## The run before a call -/

/-- **A label-free prefix, a non-label, then a label**, split two ways:
the same split. -/
theorem split_label {c c' : Directive} {a b : Label} {r r' : List Directive}
    (hc : c.isLabel = false) (hc' : c'.isLabel = false) :
    ∀ {ys D : List Directive}, ys.all (fun d => !d.isLabel) = true → D.all (fun d => !d.isLabel) = true →
      ys ++ c :: .label a :: r = D ++ c' :: .label b :: r' → ys = D ∧ c = c' ∧ a = b ∧ r = r'
  | [], [], _, _, he => by simp only [List.nil_append, List.cons.injEq, Directive.label.injEq] at he; exact ⟨rfl, he⟩
  | [], d :: D, _, hD, he => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
    obtain ⟨-, he⟩ := he
    match D, hD, he with
    | [], _, he => simp only [List.nil_append, List.cons.injEq] at he; rw [← he.1] at hc'; cases hc'
    | d2 :: D, hD, he =>
      simp only [List.cons_append, List.cons.injEq] at he
      rw [← he.1] at hD; simp [Directive.isLabel] at hD
  | y :: ys, [], hy, _, he => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
    obtain ⟨-, he⟩ := he
    match ys, hy, he with
    | [], _, he => simp only [List.nil_append, List.cons.injEq] at he; rw [he.1] at hc; cases hc
    | y2 :: ys, hy, he =>
      simp only [List.cons_append, List.cons.injEq] at he
      rw [he.1] at hy; simp [Directive.isLabel] at hy
  | y :: ys, d :: D, hy, hD, he => by
    simp only [List.cons_append, List.cons.injEq] at he
    simp only [List.all_cons, Bool.and_eq_true] at hy hD
    obtain ⟨rfl, h1, h2, h3⟩ := split_label hc hc' hy.2 hD.2 he.2
    exact ⟨by rw [he.1], h1, h2, h3⟩

/-- **The run before a call's `callq`** (`callSite1`'s `Xd ++ ys`) when the
block's code is a label-free `A`, the `callq`, its return label and a
label-free rest (`callBlk_code`): no label `Xd`, the run from the block's
label `l`, and `ys` is `A`'s directives. -/
theorem callSite_run {A : List Item} {Xd ys rest rest' : List Directive} {L l a b : Label} {c c' : Directive}
    (hA : AllIns A) (hys : ys.all (fun d => !d.isLabel) = true) (hr' : rest'.all (fun d => !d.isLabel) = true)
    (hc : c.isLabel = false) (hc' : c'.isLabel = false)
    (hX : (Xd = [] ∧ L = l) ∨ ∃ X', Xd = X' ++ [.label L])
    (he : Xd ++ ys ++ c :: .label a :: rest = directives A ++ c' :: .label b :: rest') :
    Xd = [] ∧ L = l ∧ ys = directives A := by
  rcases hX with ⟨rfl, rfl⟩ | ⟨X', rfl⟩
  · exact ⟨rfl, rfl, (split_label hc hc' hys hA (by simpa using he)).1⟩
  · exfalso
    have hcnt := congrArg (List.countP (fun d => d.isLabel)) he
    unfold AllIns at hA
    have h0 : (directives A).countP (fun d => d.isLabel) = 0 := by
      rw [List.countP_eq_zero]; intro d hd; simpa using List.all_eq_true.mp hA d hd
    have h1 : rest'.countP (fun d => d.isLabel) = 0 := by
      rw [List.countP_eq_zero]; intro d hd; simpa using List.all_eq_true.mp hr' d hd
    simp only [List.countP_append, List.countP_cons, h0, h1, hc, hc'] at hcnt
    simp [Directive.isLabel] at hcnt
    omega

end Spike.Lib.LowerX64
