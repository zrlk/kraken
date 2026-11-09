/-
**A call-free `Accepted1` function's blocks from the placement checks**
(x86-64): `body1_seg`'s code premises (`Code1` of the open block,
`BlocksCode` of the later ones) from `blocksOk` and `blocksPh`, at a code
predicate `Cd1` carrying each construct's block placed (`At1`, whole or a
`ret`'s in two pieces around its return site's label), its phase check
(`blkPh`, no dead target) and its kind (`Kind1`); the twin of
`Spike/Lib/LowerA64/Blocks1.lean`.

- `lower1_shape`: the lowering of a call-free `Accepted1` body has only
  checked `+`s and saturating `-`s, and only `ret [w]` and `br .eq`
  terminators (`BlkOK1`).
- `emitInst_add_cases`, `emitInst_sub_cases`, `blockCode_spec`: the
  emitter's code of a block, split into the constructs' directives
  (`Code1D`), with the fresh labels P5 adds after each checked `+` and
  before each `ret` (`retL fr.fn k`, the label counter at `k`).
- `KindD`, `Kind1`, `kind1_ok`: a construct's block is covered at the
  frame's offsets, so every directive of it is classified and none is a
  label.
- `code1_of_seg`: a block's directives after its label (`segIn`), every
  run from there passing its phase check, give `Code1` at `Cd1`, each
  construct's block at the sizes the listing gives; each fresh label starts
  a new run, at the address `labelGap` gives (`hgap`; `hgap_of_lays`,
  `hgap_ofPlaceOK`).
- `code1_block`, `blocksCode1`, `entryCode1`: from a block's
  `blocksOk`/`blocksPh` facts (`blocksPh_blockPh`); `zip_callMaps`: every block's safepoint maps
  are one per instruction, so the emitter writes all of them.

Where x86-64 differs from AArch64: the emitter is a state monad (`E`), so
a block's code is split by `blockCode_spec` into a directive-level form
(`Code1D`) first; a block is its directives zipped with the sizes of the
listing's cells after its label (`after`), so `code1_of_seg` reads the
blocks off those cells (`t`) and `Cd1` places them at their byte offsets
(`cellOff`); a construct's block is label-free because it is covered
(`classify_of_okBlk`).
-/
import Spike.Lib.LowerX64.Body1
import Spike.Lib.LowerX64.MainCode1
import Spike.Lib.LowerX64.Construct1

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (S E Item emitInst emitTerm ld st ins labelOf cmpAB directives i64)
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (blockAt after after_eq labelGap)
open Scc.Cert.Code1X64 (blockCode blockItems blocksOk segIn segIn_iff blockAt_of_segIn blocksOk_block
  take_drop_append segIn_label labelGap_of_segIn labelsAt_append)
open Scc.Cert.Ph1X64 (runs runsAux runPh runPhB blocksPh blocksPh_block blkPh_of_runPhB runsAux_nil segCells
  segCells_map blocksPh_blockPh runPhB_get cellOff_mid)
open Spike.Lib.X64Consumer (blkPh)
open Scc.Sem.X64 (codeLabel)
open Scc.Lower.Inv (lower1 Res1 atomV EnvScalar envScalar_cons atomV_of_atom0)

set_option linter.unusedSimpArgs false

/-! ## The lowering's shape -/

/-- An instruction of a call-free `Accepted1` body: a checked `+` or a
saturating `-`. -/
def InstOK1 : Scc.IR.Inst → Prop
  | .addChk .. => True
  | .subSat .. => True
  | _ => False

/-- A terminator of a call-free `Accepted1` body: a one-word `ret` or an
`if`'s `br .eq`. -/
def TermOK1 : Scc.IR.Term → Prop
  | .ret [_] => True
  | .br .eq .. => True
  | _ => False

/-- A block of a call-free `Accepted1` body (`InstOK1`, `TermOK1`). -/
def BlkOK1 (is : List Scc.IR.Inst) (tm : Scc.IR.Term) : Prop := (∀ i ∈ is, InstOK1 i) ∧ TermOK1 tm

/-- **The lowering of a call-free `Accepted1` body** has `BlkOK1` open
block and later blocks. -/
theorem lower1_shape :
    ∀ (e : Expr) (scope : List String) (env : Scc.Lower.Env) (n : Nat) (r : Res1),
      Scc.Lower.body1 [] scope e = true → EnvScalar scope env → lower1 env n e = some r →
      BlkOK1 r.insts r.term ∧ ∀ b ∈ r.blocks, BlkOK1 b.insts b.term := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope env n r hb h hr
    cases op with
    | atom a =>
      simp only [Scc.Lower.body1, Scc.Lower.atom1, Bool.and_eq_true] at hb
      obtain ⟨t, w, ha, ht⟩ := atomV_of_atom0 hb.1 h
      cases hr' : lower1 ((x, t, [w]) :: env) n e with
      | none => simp [lower1, ha, ht, hr'] at hr
      | some r' =>
        simp [lower1, ha, ht, hr'] at hr
        subst hr
        exact ih (x :: scope) _ n r' hb.2 (envScalar_cons h x w ht) hr'
    | add a b =>
      simp only [Scc.Lower.body1, Scc.Lower.atom1, Bool.and_eq_true] at hb
      obtain ⟨t, p, ha, -⟩ := atomV_of_atom0 hb.1.1 h
      obtain ⟨t', q, hb', -⟩ := atomV_of_atom0 hb.1.2 h
      cases hr' : lower1 ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e with
      | none => simp [lower1, ha, hb', hr'] at hr
      | some r' =>
        simp [lower1, ha, hb', hr'] at hr
        subst hr
        obtain ⟨⟨hi, ht⟩, hbs⟩ := ih (x :: scope) _ (n + 1) r' hb.2 (envScalar_cons h x _ rfl) hr'
        exact ⟨⟨List.forall_mem_cons.mpr ⟨trivial, hi⟩, ht⟩, hbs⟩
    | sub a b =>
      simp only [Scc.Lower.body1, Scc.Lower.atom1, Bool.and_eq_true] at hb
      obtain ⟨t, p, ha, -⟩ := atomV_of_atom0 hb.1.1 h
      obtain ⟨t', q, hb', -⟩ := atomV_of_atom0 hb.1.2 h
      cases hr' : lower1 ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e with
      | none => simp [lower1, ha, hb', hr'] at hr
      | some r' =>
        simp [lower1, ha, hb', hr'] at hr
        subst hr
        obtain ⟨⟨hi, ht⟩, hbs⟩ := ih (x :: scope) _ (n + 1) r' hb.2 (envScalar_cons h x _ rfl) hr'
        exact ⟨⟨List.forall_mem_cons.mpr ⟨trivial, hi⟩, ht⟩, hbs⟩
    | call g is a ts => simp [Scc.Lower.body1, Scc.Lower.callee1] at hb
    | _ => simp [Scc.Lower.body1] at hb
  | ifeq a b yes no ihy ihn =>
    intro scope env n r hb h hr
    simp only [Scc.Lower.body1, Scc.Lower.atom1, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨ha0, hb0⟩, hy0⟩, hn0⟩ := hb
    obtain ⟨t, p, ha, -⟩ := atomV_of_atom0 ha0 h
    obtain ⟨t', q, hb', -⟩ := atomV_of_atom0 hb0 h
    cases hy : lower1 env (n + 2) yes with
    | none => simp [lower1, ha, hb', hy] at hr
    | some ry =>
      cases hn : lower1 env ry.next no with
      | none => simp [lower1, ha, hb', hy, hn] at hr
      | some rn =>
        simp [lower1, ha, hb', hy, hn] at hr
        subst hr
        obtain ⟨hyo, hyb⟩ := ihy scope env (n + 2) ry hy0 h hy
        obtain ⟨hno, hnb⟩ := ihn scope env ry.next rn hn0 h hn
        refine ⟨⟨fun i hi => (by cases hi), trivial⟩, fun b hb => ?_⟩
        simp only [List.mem_cons, List.mem_append] at hb
        rcases hb with rfl | hb | rfl | hb
        · exact hyo
        · exact hyb b hb
        · exact hno
        · exact hnb b hb
  | ret a =>
    intro scope env n r hb h hr
    obtain ⟨t, w, ha, -⟩ := atomV_of_atom0 (by simpa [Scc.Lower.body1] using hb) h
    simp [lower1, ha] at hr
    subst hr
    exact ⟨⟨fun i hi => (by cases hi), trivial⟩, fun b hb => by cases hb⟩
  | _ => intro scope env n r hb; simp [Scc.Lower.body1] at hb

/-! ## The emitter's code, split into the constructs' directives -/

section Emit

theorem blockCode_cons (fr : Scc.Emit.X64.Frame) (lb : Scc.IR.Label) (i : Scc.IR.Inst) (is : List Scc.IR.Inst)
    (tm : Scc.IR.Term) (m : Option Scc.IR.StackMap.Entry) (ms : List (Option Scc.IR.StackMap.Entry)) :
    blockCode fr ⟨lb, i :: is, tm⟩ (m :: ms) = (do emitInst fr m i; blockCode fr ⟨lb, is, tm⟩ ms) := by
  simp only [blockCode, List.zip_cons_cons, List.forIn_cons, bind_assoc, pure_bind]

theorem blockCode_nil (fr : Scc.Emit.X64.Frame) (lb : Scc.IR.Label) (tm : Scc.IR.Term)
    (ms : List (Option Scc.IR.StackMap.Entry)) :
    blockCode fr ⟨lb, [], tm⟩ ms = emitTerm fr tm := by
  simp [blockCode]

theorem bind_ok {α β : Type} {x : E α} {f : α → E β} {s s' : S} {a : α} (h : x s = .ok (a, s')) :
    (x >>= f) s = f a s' := by
  show StateT.bind x f s = _
  simp only [StateT.bind, h]; rfl

theorem bind_err {α β : Type} {x : E α} {f : α → E β} {s : S} {e : String} (h : x s = .error e) :
    (x >>= f) s = .error e := by
  show StateT.bind x f s = _
  simp only [StateT.bind, h]; rfl

theorem bind_inv {α β : Type} {x : E α} {f : α → E β} {s s' : S} {b : β} (h : (x >>= f) s = .ok (b, s')) :
    ∃ a s1, x s = .ok (a, s1) ∧ f a s1 = .ok (b, s') := by
  cases hx : x s with
  | error e => rw [bind_err hx] at h; cases h
  | ok r => obtain ⟨a, s1⟩ := r; rw [bind_ok hx] at h; exact ⟨a, s1, rfl, h⟩

theorem ins_eq (d : Directive) (s : S) : ins d s = .ok ((), { s with out := .d d :: s.out }) := rfl

theorem directives_eq_dirs (l : List Item) : directives l = dirs l := rfl

theorem ld_cases (fr : Scc.Emit.X64.Frame) (a : Scc.IR.Operand) (t : Reg64) (s : S) :
    (∃ l, getOp fr t a = .ok l ∧ ld fr a t s = .ok ((), { s with out := l.reverse ++ s.out })) ∨
    ∃ e, ld fr a t s = .error e := by
  cases hg : getOp fr t a with
  | ok l => exact .inl ⟨l, rfl, ld_getOp hg s⟩
  | error e =>
    right
    cases a with
    | imm v => simp [getOp, Scc.Lower.InvX64.ld_imm] at hg
    | reg x =>
      cases hf : fr.slots.find? (·.1 == x) with
      | some v =>
        obtain ⟨r', k⟩ := v
        rw [getOp, Scc.Lower.InvX64.ld_reg (Scc.Lower.InvX64.slotOff_find hf _)] at hg; cases hg
      | none =>
        exact ⟨_, by simp only [ld, Scc.Emit.X64.Frame.slot, Scc.Emit.X64.Frame.slotOff, hf, bind, StateT.bind]; rfl⟩

theorem st_cases (fr : Scc.Emit.X64.Frame) (d : Scc.IR.Reg) (s : S) :
    (∃ off, rsOf fr d = some off ∧ st fr .rax d s = .ok ((), { s with out := .d (stDir off) :: s.out })) ∨
    ∃ e, st fr .rax d s = .error e := by
  cases hf : fr.slots.find? (·.1 == d) with
  | some v =>
    obtain ⟨r', k⟩ := v
    exact .inl ⟨_, rsOf_eq (Scc.Lower.InvX64.slotOff_find hf {}),
      Scc.Lower.InvX64.st_eq (Scc.Lower.InvX64.slotOff_find hf _) _⟩
  | none =>
    exact .inr ⟨_, by simp only [st, Scc.Emit.X64.Frame.slot, Scc.Emit.X64.Frame.slotOff, hf, bind, StateT.bind]; rfl⟩

theorem freshL_eq (fn : String) (s : S) :
    Scc.Emit.X64.freshL fn s = .ok (retL fn s.next, { s with next := s.next + 1 }) := rfl

theorem lbl_eq (l : String) (s : S) :
    Scc.Emit.X64.lbl l s = .ok ((), { s with out := .d (.label l) :: s.out }) := rfl

/-- **The code of a checked `+`**: both operands' loads, the checked add,
the fall-through's fresh label (`retL fr.fn s.next`, P5), the store; the
next fresh label is `s.next + 1`. -/
theorem emitInst_add_cases (fr : Scc.Emit.X64.Frame) (sm) (d : Scc.IR.Reg) (a b : Scc.IR.Operand) (s : S) {u s'}
    (h : emitInst fr sm (.addChk d a b) s = .ok (u, s')) :
    ∃ la lb off, getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧ rsOf fr d = some off ∧
      s' = { s with out := (la ++ lb ++ addChecked (ovfL fr) ++
        [Item.d (.label (retL fr.fn s.next)), Item.d (stDir off)]).reverse ++ s.out, next := s.next + 1 } := by
  rw [Scc.Lower.InvX64.emitInst_addChk] at h
  rcases ld_cases fr a .rax s with ⟨la, ha, e1⟩ | ⟨e, e1⟩
  · rw [bind_ok e1] at h
    rcases ld_cases fr b .rcx { s with out := la.reverse ++ s.out } with ⟨lb, hb, e2⟩ | ⟨e, e2⟩
    · rw [bind_ok e2, bind_ok (ins_eq _ _), bind_ok (ins_eq _ _), bind_ok (freshL_eq _ _), bind_ok (lbl_eq _ _)] at h
      rcases st_cases fr d _ with ⟨off, hd, e3⟩ | ⟨e, e3⟩
      · rw [e3] at h
        cases h
        exact ⟨la, lb, off, ha, hb, hd, by simp [addChecked, ovfL]⟩
      · rw [e3] at h; cases h
    · rw [bind_err e2] at h; cases h
  · rw [bind_err e1] at h; cases h

/-- **The code of a saturating `-`**: both operands' loads, the saturating
subtraction, the store. -/
theorem emitInst_sub_cases (fr : Scc.Emit.X64.Frame) (sm) (d : Scc.IR.Reg) (a b : Scc.IR.Operand) (s : S) {u s'}
    (h : emitInst fr sm (.subSat d a b) s = .ok (u, s')) :
    ∃ la lb off, getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧ rsOf fr d = some off ∧
      s' = { s with out := (la ++ lb ++ subSatItems ++ [Item.d (stDir off)]).reverse ++ s.out } := by
  rw [emitInst_subSat] at h
  rcases ld_cases fr a .rax s with ⟨la, ha, e1⟩ | ⟨e, e1⟩
  · rw [bind_ok e1] at h
    rcases ld_cases fr b .rcx { s with out := la.reverse ++ s.out } with ⟨lb, hb, e2⟩ | ⟨e, e2⟩
    · rw [bind_ok e2, bind_ok (ins_eq _ _), bind_ok (x := Scc.Emit.X64.movl .rdx 0) (ins_eq _ _),
        bind_ok (ins_eq _ _)] at h
      rcases st_cases fr d _ with ⟨off, hd, e3⟩ | ⟨e, e3⟩
      · rw [e3] at h
        cases h
        exact ⟨la, lb, off, ha, hb, hd, by simp [subSatItems]⟩
      · rw [e3] at h; cases h
    · rw [bind_err e2] at h; cases h
  · rw [bind_err e1] at h; cases h

/-- **A block's directives, construct by construct**, the label counter at
`k`: each checked `+`'s directives, its fall-through's label `retL fr.fn k`
and its store, the counter `k + 1` after it, or a saturating `-`'s
directives and its store, then the rest; then a `ret`'s (its load and
teardown, its return site's label `retL fr.fn k`, `ret`) or an `if`'s
(`Code1`'s blocks, before the listing gives them sizes). -/
def Code1D (fr : Scc.Emit.X64.Frame) : Nat → List Directive → List Scc.IR.Inst → Scc.IR.Term → Prop
  | k, ds, [], .ret [w] => ∃ l, getOp fr .rax w = .ok l ∧
      ds = tearDirs l ++ [.label (retL fr.fn k), i64 .ret]
  | _, ds, [], .br .eq a b ct cf => ∃ la lb, getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧
      ds = brDirs la lb (labelOf fr.fn ct) ++ jmpDirs (labelOf fr.fn cf)
  | k, ds, .addChk d a b :: is, tm => ∃ la lb off ds', getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧
      rsOf fr d = some off ∧ ds = addDirs fr la lb ++ [.label (retL fr.fn k), stDir off] ++ ds' ∧
      Code1D fr (k + 1) ds' is tm
  | k, ds, .subSat d a b :: is, tm => ∃ la lb off ds', getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧
      rsOf fr d = some off ∧ ds = subDirs la lb ++ [stDir off] ++ ds' ∧ Code1D fr k ds' is tm
  | _, _, _, _ => False

/-- **The emitter's code of a `BlkOK1` block** (every instruction with a
safepoint map): appended to the output, its directives `Code1D` from the
label counter `s.next`. -/
theorem blockCode_spec (fr : Scc.Emit.X64.Frame) (lb : Scc.IR.Label) {tm : Scc.IR.Term} (htm : TermOK1 tm) :
    ∀ (is : List Scc.IR.Inst) (ms : List (Option Scc.IR.StackMap.Entry)) (s s' : S),
      (∀ i ∈ is, InstOK1 i) → is.length ≤ ms.length → blockCode fr ⟨lb, is, tm⟩ ms s = .ok ((), s') →
      ∃ c, s'.out = c.reverse ++ s.out ∧ Code1D fr s.next (dirs c) is tm
  | [], ms, s, s', _, _, h => by
    rw [blockCode_nil] at h
    match tm, htm, h with
    | .ret [w], _, h =>
      rcases ld_cases fr w .rax s with ⟨l, hl, -⟩ | ⟨e, he⟩
      · rw [emitTerm_ret hl s] at h
        cases h
        exact ⟨l ++ retItems fr.fn s.next, rfl, l, hl, by rw [dirs_retItems]; rfl⟩
      · rw [emitTerm_ret1, bind_err he] at h; cases h
    | .br .eq a b ct cf, _, h =>
      rcases ld_cases fr a .rax s with ⟨la, ha, e1⟩ | ⟨e, e1⟩
      · rcases ld_cases fr b .rcx { s with out := la.reverse ++ s.out } with ⟨lb, hb, e2⟩ | ⟨e, e2⟩
        · rw [emitTerm_br_eq ha hb ct cf s] at h
          cases h
          refine ⟨_, rfl, la, lb, ha, hb, ?_⟩
          rw [dirs_append]; rfl
        · have hc : cmpAB fr a b s = .error e := by
            unfold cmpAB; rw [bind_ok e1, bind_err e2]
          simp only [emitTerm] at h
          rw [bind_err hc] at h; cases h
      · have hc : cmpAB fr a b s = .error e := by
          unfold cmpAB; rw [bind_err e1]
        simp only [emitTerm] at h
        rw [bind_err hc] at h; cases h
  | i :: is, [], _, _, _, hl, _ => by simp at hl
  | i :: is, m :: ms, s, s', hs, hl, h => by
    have hs' := List.forall_mem_cons.mp hs
    rw [blockCode_cons] at h
    obtain ⟨u, s1, h1, h2⟩ := bind_inv h
    obtain ⟨c', hs1, hc'⟩ := blockCode_spec fr lb htm is ms s1 s' hs'.2 (by simpa using hl) h2
    cases i with
    | addChk d a b =>
      obtain ⟨la, lb, off, ha, hb, hd, rfl⟩ := emitInst_add_cases fr m d a b s h1
      refine ⟨la ++ lb ++ addChecked (ovfL fr) ++ [Item.d (.label (retL fr.fn s.next)), Item.d (stDir off)] ++ c',
        ?_, la, lb, off, dirs c', ha, hb, hd, ?_, hc'⟩
      · rw [hs1]; simp [List.reverse_append, List.append_assoc]
      · rw [dirs_append, dirs_append]; rfl
    | subSat d a b =>
      obtain ⟨la, lb, off, ha, hb, hd, rfl⟩ := emitInst_sub_cases fr m d a b s h1
      refine ⟨la ++ lb ++ subSatItems ++ [Item.d (stDir off)] ++ c', ?_,
        la, lb, off, dirs c', ha, hb, hd, ?_, hc'⟩
      · rw [hs1]; simp [List.reverse_append, List.append_assoc]
      · rw [dirs_append, dirs_append]; rfl
    | _ => exact hs'.1.elim

end Emit

/-! ## The constructs' blocks -/

/-- **A construct's directives** of a call-free `Accepted1` body: a checked
`+`'s, a saturating `-`'s or an `if`'s compare-and-branch (operand loads),
a store, a `jmp`, or a `ret`'s. -/
def KindD (fr : Scc.Emit.X64.Frame) (ds : List Directive) : Prop :=
  (∃ a b la lb, getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧
    (ds = addDirs fr la lb ∨ ds = subDirs la lb ∨ ∃ T, ds = brDirs la lb T)) ∨
  (∃ d off, rsOf fr d = some off ∧ ds = [stDir off]) ∨
  (∃ F, ds = jmpDirs F) ∨
  (∃ w lw, getOp fr .rax w = .ok lw ∧ ds = retDirs lw)

/-- **A construct's block** (sized): its directives are a construct's
(`KindD`). -/
def Kind1 (fr : Scc.Emit.X64.Frame) (blk : List (Directive × Nat)) : Prop := KindD fr (blk.map (·.1))

theorem zip_fst_snd {α β : Type} : ∀ l : List (α × β), (l.map (·.1)).zip (l.map (·.2)) = l
  | [] => rfl
  | (a, b) :: l => by simp only [List.map_cons, List.zip_cons_cons, zip_fst_snd l]

section Kinds

variable {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
include hf h1

/-- **A construct's directives are covered** at the frame's offsets, at any
sizes of their length. -/
theorem kindD_ok {ds : List Directive} (hk : KindD fr ds) {zs : List Nat} (hz : zs.length = ds.length) :
    okBlk (-(fr.size : Int)) 16 (oB fr) (ds.zip zs) = true := by
  rcases hk with ⟨a, b, la, lb, ha, hb, rfl | rfl | ⟨T, rfl⟩⟩ | ⟨d, o, hd, rfl⟩ | ⟨F, rfl⟩ | ⟨w, lw, hg, rfl⟩
  · obtain ⟨da, hda⟩ := dirs_getOp ha
    obtain ⟨db, hdb⟩ := dirs_getOp hb
    have hz' := hz
    rw [addDirs, dirs_append, dirs_append, hda, hdb, dirs_addChecked] at hz'
    match zs, hz' with
    | [z0, z1, z2, z3], _ =>
    have hsplit : (addDirs fr la lb).zip [z0, z1, z2, z3] =
        (dirs la).zip [z0] ++ ((dirs lb).zip [z1] ++ (dirs (addChecked (ovfL fr))).zip [z2, z3]) := by
      rw [addDirs, dirs_append, dirs_append, hda, hdb, dirs_addChecked]; rfl
    rw [hsplit, okBlk_getOp hf h1 (by decide) (by decide) ha (by simp [hda]),
      okBlk_getOp hf h1 (by decide) (by decide) hb (by simp [hdb])]
    exact okBlk_addChecked (by simp [oB, SO.kill, rm]) _
  · obtain ⟨da, hda⟩ := dirs_getOp ha
    obtain ⟨db, hdb⟩ := dirs_getOp hb
    have hz' := hz
    rw [subDirs, dirs_append, dirs_append, hda, hdb, dirs_subSat] at hz'
    match zs, hz' with
    | [z0, z1, z2, z3, z4], _ =>
    have hsplit : (subDirs la lb).zip [z0, z1, z2, z3, z4] =
        (dirs la).zip [z0] ++ ((dirs lb).zip [z1] ++ (dirs subSatItems).zip [z2, z3, z4]) := by
      rw [subDirs, dirs_append, dirs_append, hda, hdb, dirs_subSat]; rfl
    rw [hsplit, okBlk_getOp hf h1 (by decide) (by decide) ha (by simp [hda]),
      okBlk_getOp hf h1 (by decide) (by decide) hb (by simp [hdb])]
    exact okBlk_subSat (by simp [oB, SO.kill, rm]) (by simp [oB, SO.kill, rm])
  · obtain ⟨da, hda⟩ := dirs_getOp ha
    obtain ⟨db, hdb⟩ := dirs_getOp hb
    have hz' := hz
    rw [brDirs, dirs_append, dirs_append, hda, hdb, dirs_cmpJe] at hz'
    match zs, hz' with
    | [z0, z1, z2, z3], _ =>
    have hsplit : (brDirs la lb T).zip [z0, z1, z2, z3] =
        (dirs la).zip [z0] ++ ((dirs lb).zip [z1] ++ (dirs (cmpJe T)).zip [z2, z3]) := by
      rw [brDirs, dirs_append, dirs_append, hda, hdb, dirs_cmpJe]; rfl
    rw [hsplit, okBlk_getOp hf h1 (by decide) (by decide) ha (by simp [hda]),
      okBlk_getOp hf h1 (by decide) (by decide) hb (by simp [hdb])]
    exact okBlk_cmpJe T
  · obtain ⟨z, rfl⟩ := length_one hz
    obtain ⟨h8, hm, hle⟩ := rsOf_bounds hf hd
    have ho : (Int64.ofInt o).toInt = o := toInt_ofInt_small (by omega) (by omega)
    have hc : classify (stDir o) = some (AI.st .rbp (Int64.ofInt o) .rax) := rfl
    simp only [List.zip_cons_cons, List.zip_nil_left, okBlk, hc, AI.ok, AI.isTerm, oB, SO.get, lk, ho, offOk]
    simp
    omega
  · obtain ⟨z, rfl⟩ := length_one hz
    exact okBlk_jmp F
  · obtain ⟨dl, hdl⟩ := dirs_getOp hg
    have hds : retDirs lw = dirs lw ++ epi := by rw [retDirs, dirs_append, dirs_epiItems]
    rw [hds, hdl] at hz
    match zs, hz with
    | [z0, z1, z2, z3], _ =>
    have hsplit : (retDirs lw).zip [z0, z1, z2, z3] = (dirs lw).zip [z0] ++ epi.zip [z1, z2, z3] := by
      rw [hds, hdl]; rfl
    rw [hsplit, okBlk_getOp hf h1 (by decide) (by decide) hg (by simp [hdl])]
    exact okBlk_epi (by omega) z1 z2 z3

/-- **A construct's block is covered** at the frame's offsets. -/
theorem kind1_ok {blk : List (Directive × Nat)} (hk : Kind1 fr blk) :
    okBlk (-(fr.size : Int)) 16 (oB fr) blk = true := by
  have := kindD_ok hf h1 hk (zs := blk.map (·.2)) (by simp)
  rwa [zip_fst_snd] at this

end Kinds

/-- Every directive of a covered block is classified. -/
theorem classify_of_okBlk {lo hi : Int} :
    ∀ {o : SO} {blk : List (Directive × Nat)}, okBlk lo hi o blk = true → ∀ d ∈ blk, (classify d.1).isSome = true
  | _, [], _, d, hd => by cases hd
  | o, (x, z) :: xs, h, d, hd => by
    unfold okBlk at h
    split at h
    · rename_i a ha
      simp only [Bool.and_eq_true] at h
      rcases List.mem_cons.mp hd with rfl | hd
      · show (classify x).isSome = true
        rw [ha]; rfl
      · exact classify_of_okBlk h.2 d hd
    · cases h

/-- A classified directive is not a label. -/
theorem isLabel_of_classify {d : Directive} (h : (classify d).isSome = true) : d.isLabel = false := by
  cases d with
  | label l => simp [X64.classify] at h
  | _ => rfl

section Kinds

variable {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
include hf h1

/-- **A construct's directives are label-free.** -/
theorem kindD_noLabel {ds : List Directive} (hk : KindD fr ds) : ds.all (fun d => !d.isLabel) = true := by
  have hok := kindD_ok hf h1 hk (zs := List.replicate ds.length 0) (by simp)
  rw [List.all_eq_true]
  intro d hd
  have hm : (ds.zip (List.replicate ds.length 0)).map (·.1) = ds := List.map_fst_zip (by simp)
  rw [← hm] at hd
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
  simp [isLabel_of_classify (classify_of_okBlk hok p hp)]

/-- **A construct's directives are classified.** -/
theorem classify_of_kindD {ds : List Directive} (hk : KindD fr ds) : ∀ d ∈ ds, (classify d).isSome = true := by
  have hok := kindD_ok hf h1 hk (zs := List.replicate ds.length 0) (by simp)
  intro d hd
  have hm : (ds.zip (List.replicate ds.length 0)).map (·.1) = ds := List.map_fst_zip (by simp)
  rw [← hm] at hd
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
  exact classify_of_okBlk hok p hp

end Kinds

/-! ## The code predicate -/

/-- **`blk` is placed at `pc`**: `k` cells (`off` bytes) after a label `l`
(`blockAt`). -/
def At1 (cells : List (Directive × Nat)) (lab : Label → Int64) (pc : Int64) (blk : List (Directive × Nat)) : Prop :=
  ∃ l k off, lab l + Int64.ofNat off = pc ∧ blockAt cells l k off blk = true

/-- **The code predicate of a call-free `Accepted1` body**: `blk` is a
construct's block (`Kind1`) placed at `pc` (`At1`), whole or in two pieces,
the second right after the first (a `ret`'s load and teardown, then `ret`
after its return site's label, P5), passing the phase check at `pc` with no
dead target and the return address `ra`. -/
def Cd1 (cells : List (Directive × Nat)) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64)
    (fr : Scc.Emit.X64.Frame) (ra : Int64) (pc : Int64) (blk : List (Directive × Nat)) : Prop :=
  Kind1 fr blk ∧
    (At1 cells lab pc blk ∨ ∃ b1 b2, blk = b1 ++ b2 ∧ At1 cells lab pc b1 ∧
      At1 cells lab (pc + Int64.ofNat (b1.map (·.2)).sum) b2) ∧
    blkPh okPc ph (fun _ => false) lab pc ra blk = true

theorem cellOff_add (t : List (Directive × Nat)) (a b : Nat) :
    cellOff t (a + b) = cellOff t a + (((t.drop a).take b).map (·.2)).sum := by
  unfold cellOff
  rw [List.take_add, List.map_append, List.sum_append]

theorem cellOff_take (t : List (Directive × Nat)) {a N : Nat} (h : a ≤ N) : cellOff (t.take N) a = cellOff t a := by
  unfold cellOff
  rw [List.take_take, Nat.min_eq_left h]

theorem take_split (t : List (Directive × Nat)) (a b N : Nat) (h : a + b ≤ N) :
    t.take N = t.take a ++ (t.drop a).take b ++ (t.drop (a + b)).take (N - (a + b)) := by
  have e : N = a + (b + (N - (a + b))) := by omega
  rw [congrArg (fun n => t.take n) e, List.take_add, List.take_add, List.drop_drop, List.append_assoc]

theorem pc_step (p : Int64) (t : List (Directive × Nat)) (a b : Nat) :
    p + Int64.ofNat (cellOff t (a + b)) = p + Int64.ofNat (cellOff t a) +
      Int64.ofNat ((((t.drop a).take b).map (·.2)).sum) := by
  rw [cellOff_add, Int64.ofNat_add, Int64.add_assoc]

/-! ## Runs -/

/-- **A label-free prefix joins the current run.** -/
theorem runsAux_shift : ∀ (l : Label) (acc c S : List (Directive × Nat)), (∀ d ∈ c, d.1.isLabel = false) →
    runsAux l acc (c ++ S) = runsAux l (c.reverse ++ acc) S
  | l, acc, [], S, _ => by simp
  | l, acc, d :: c, S, h => by
    have hd : d.1.isLabel = false := h d (List.mem_cons_self ..)
    have ih := runsAux_shift l (d :: acc) c S fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    obtain ⟨d, zd⟩ := d
    cases d with
    | label l'' => cases hd
    | instr i => simp only [List.cons_append, runsAux]; rw [ih]; simp
    | byteArray a => simp only [List.cons_append, runsAux]; rw [ih]; simp

/-- **The current run** of `runsAux l acc S`: `acc` (reversed) and the
cells of `S` up to its first label. -/
theorem runsAux_run0 : ∀ (l : Label) (acc S : List (Directive × Nat)), ∃ P, (l, acc.reverse ++ P) ∈ runsAux l acc S
  | l, acc, [] => ⟨[], by simp [runsAux]⟩
  | l, acc, (.label _, _) :: _ => ⟨[], by simp [runsAux]⟩
  | l, acc, (.instr i, w) :: S => by
    obtain ⟨P, hP⟩ := runsAux_run0 l ((.instr i, w) :: acc) S
    exact ⟨(.instr i, w) :: P, by simpa [runsAux] using hP⟩
  | l, acc, (.byteArray a, w) :: S => by
    obtain ⟨P, hP⟩ := runsAux_run0 l ((.byteArray a, w) :: acc) S
    exact ⟨(.byteArray a, w) :: P, by simpa [runsAux] using hP⟩

/-- **The first run is after the label** the runs start from. -/
theorem runsAux_head (l : Label) :
    ∀ (acc ds : List (Directive × Nat)), ∃ y, (l, y) ∈ runsAux l acc ds
  | acc, [] => ⟨acc.reverse, by simp [runsAux]⟩
  | acc, (d, z) :: ds => by
    cases d with
    | label l' => exact ⟨acc.reverse, by simp [runsAux]⟩
    | _ => simpa [runsAux] using runsAux_head l _ ds

/-- **The runs past a label-free slice**: the slice of `t` from `a` of
length `b` label-free, the runs from `a` are those from `a + b`, the slice
joining the current run. -/
theorem runs_step {l : Label} {t : List (Directive × Nat)} {a b n : Nat}
    (h : ∀ d ∈ (t.drop a).take b, d.1.isLabel = false) :
    runsAux l (t.take a).reverse ((t.drop a).take (b + n)) =
      runsAux l (t.take (a + b)).reverse ((t.drop (a + b)).take n) := by
  rw [List.take_add, runsAux_shift _ _ _ _ h, ← List.reverse_append, ← List.take_add, List.drop_drop]

/-- The cells of a slice of a segment are label-free when its directives
are. -/
theorem slice_noLabel {S : List (Directive × Nat)} {c : List Directive} (hY : S.map (·.1) = c)
    (hc : c.all (fun d => !d.isLabel) = true) : ∀ d ∈ S, d.1.isLabel = false := by
  intro d hd
  have := List.all_eq_true.mp hc d.1 (by rw [← hY]; exact List.mem_map_of_mem hd)
  simpa using this

/-- **The cells after an inner label of a segment**: after `label l'` of
the segment `P ++ .label l' :: Q` of `l`, whose cells are `t`. -/
theorem after_label {cells : List (Directive × Nat)} {l l' : Label} {P Q : List Directive}
    {t : List (Directive × Nat)} (h : segIn cells l (P ++ .label l' :: Q) = true) (ht : after l cells = some t) :
    after l' cells = some (t.drop (P.length + 1)) := by
  obtain ⟨i, hi, -, hl⟩ := segIn_iff.mp h
  have hl' := Scc.Cert.Code1X64.labelsAt_append hl
  simp only [Scc.Cert.Code1X64.labelsAt, Bool.and_eq_true, beq_iff_eq] at hl'
  rw [after_eq, hi] at ht
  cases ht
  rw [after_eq, hl'.1, List.drop_drop]
  simp only [Option.map_some, Nat.add_assoc]

/-- **`runPhB` reads the labels at the run's targets only.** -/
theorem runPhB_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64} {pc ra : Int64}
    {blk : List (Directive × Nat)} (h : ∀ L ∈ blkLabs blk, lab L = lab' L) :
    runPhB okPc ph lab pc ra blk = runPhB okPc ph lab' pc ra blk := by
  unfold runPhB
  congr 1
  funext k
  congr 1
  cases hk : blk[k]? with
  | none => rfl
  | some dz =>
    simp only
    cases hc : X64.classify dz.1 with
    | none => rfl
    | some a =>
      simp only
      rw [aiTgts_congr fun L hL => h L ?_]
      exact List.mem_filterMap.mpr ⟨dz, List.mem_of_getElem? hk, by rw [hc]; exact hL⟩

/-- **The phase check of two blocks, one right after the other**, the
second's pc in the first's phase. -/
theorem blkPh_append1 {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {dd : Nat → Bool}
    {pc ra : Int64} {a b : List (Directive × Nat)}
    (ha : blkPh okPc ph dd lab pc ra a = true)
    (hb : blkPh okPc ph dd lab (pc + Int64.ofNat (a.map (·.2)).sum) ra b = true)
    (he : ph (pc + Int64.ofNat (a.map (·.2)).sum).toBitVec.toNat = ph pc.toBitVec.toNat) :
    blkPh okPc ph dd lab pc ra (a ++ b) = true := by
  unfold blkPh at ha hb ⊢
  rw [List.all_eq_true] at ha hb ⊢
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [List.length_append] at hk'
  rcases Nat.lt_or_ge k a.length with h' | h'
  · have hoff : cellOff (a ++ b) k = cellOff a k := by
      unfold cellOff; rw [List.take_append_of_le_length (by omega)]
    rw [hoff, List.getElem?_append_left h']
    exact ha k (List.mem_range.mpr h')
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h'
    have hoff : cellOff (a ++ b) (a.length + j) = (a.map (·.2)).sum + cellOff b j := by
      unfold cellOff
      rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left, List.map_append,
        List.sum_append]
    have := hb j (List.mem_range.mpr (by omega))
    rw [he] at this
    rw [hoff, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, Int64.ofNat_add, ← Int64.add_assoc]
    exact this

section Code

variable {cells : List (Directive × Nat)} {l : Label} {t : List (Directive × Nat)}

theorem seg_take (ht : after l cells = some t) {ds : List Directive} (h : segIn cells l ds = true) :
    (t.take ds.length).map (·.1) = ds := by
  have := segCells_map h
  unfold segCells at this
  rwa [ht] at this

theorem seg_slice (ht : after l cells = some t) {xs ys zs : List Directive}
    (h : segIn cells l (xs ++ ys ++ zs) = true) : ((t.drop xs.length).take ys.length).map (·.1) = ys := by
  have h1 := seg_take ht h
  have h2 := (take_drop_append (L := t) (k := 0) (xs := xs ++ ys) (ys := zs) (by simpa using h1)).1
  have h3 := (take_drop_append (L := t) (k := 0) (xs := xs) (ys := ys) h2).2
  simpa using h3

theorem slice_len (ht : after l cells = some t) {xs ys zs : List Directive}
    (h : segIn cells l (xs ++ ys ++ zs) = true) :
    (((t.drop xs.length).take ys.length).map (·.2)).length = ys.length := by
  have := congrArg List.length (seg_slice ht h)
  simpa using this

variable {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
  {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {ra : Int64}

/-- **A classified piece `ys` of a segment is placed and passes its phase
check**: after the label-free `xs` in the segment after `l` (the cells
`t`), every run from there passing `runPhB`; at the sizes of its cells
(`(t.drop xs.length).take ys.length`); its pc in the phase of `l`'s if it
is not empty. -/
theorem piece_of (ht : after l cells = some t) {xs ys zs : List Directive}
    (hseg : segIn cells l (xs ++ ys ++ zs) = true) (hx : xs.all (fun d => !d.isLabel) = true)
    (hc : ∀ d ∈ ys, (classify d).isSome = true)
    (hph : ∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (ys ++ zs).length),
      runPhB okPc ph lab (lab r.1) ra r.2 = true) :
    ((t.drop xs.length).take ys.length).map (·.1) = ys ∧
      At1 cells lab (lab l + Int64.ofNat (cellOff t xs.length)) ((t.drop xs.length).take ys.length) ∧
      blkPh okPc ph (fun _ => false) lab (lab l + Int64.ofNat (cellOff t xs.length)) ra
        ((t.drop xs.length).take ys.length) = true ∧
      (ys ≠ [] → ph (lab l + Int64.ofNat (cellOff t xs.length)).toBitVec.toNat = ph (lab l).toBitVec.toNat) := by
  have hY := seg_slice ht hseg
  have hy : ys.all (fun d => !d.isLabel) = true :=
    List.all_eq_true.mpr fun d hd => by simp [isLabel_of_classify (hc d hd)]
  have hlenT : (xs ++ ys ++ zs).length ≤ t.length := by
    have := congrArg List.length (seg_take ht hseg)
    simp only [List.length_map, List.length_take] at this
    omega
  have hS := slice_noLabel hY hy
  refine ⟨hY, ?_, ?_⟩
  · obtain ⟨t', ht', -, hb⟩ := blockAt_of_segIn hseg hx hy
    rw [ht] at ht'
    cases ht'
    exact ⟨l, xs.length, cellOff t xs.length, rfl, hb⟩
  · rw [List.length_append, List.take_add, runsAux_shift _ _ _ _ hS] at hph
    obtain ⟨P, hP⟩ := runsAux_run0 l (((t.drop xs.length).take ys.length).reverse ++ (t.take xs.length).reverse)
      (((t.drop xs.length).drop ys.length).take zs.length)
    have hr := hph _ hP
    simp only [List.reverse_append, List.reverse_reverse] at hr
    have hr' : runPhB okPc ph lab (lab l) ra (t.take xs.length ++ (t.drop xs.length).take ys.length ++ P) = true := by
      simpa only [List.append_assoc] using hr
    have e : cellOff (t.take xs.length ++ (t.drop xs.length).take ys.length ++ P) (t.take xs.length).length =
        cellOff t xs.length := by
      unfold cellOff
      rw [List.append_assoc, List.take_left' rfl]
    have hb := blkPh_of_runPhB hr' fun d hd => hc d.1 (by rw [← hY]; exact List.mem_map_of_mem hd)
    rw [e] at hb
    refine ⟨hb, fun hne => ?_⟩
    have hne' : ys.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
    have hlen : (t.take xs.length).length <
        (t.take xs.length ++ (t.drop xs.length).take ys.length ++ P).length := by
      simp only [List.length_append, List.length_take, List.length_drop] at hlenT ⊢
      omega
    have := (runPhB_get hr' hlen).2.1
    rwa [e] at this

include hf h1 in
/-- **A construct's piece `ys` of a segment is at `Cd1`** (`piece_of`), at
the sizes of its cells. -/
theorem cd1_piece (ht : after l cells = some t) {xs ys zs : List Directive}
    (hseg : segIn cells l (xs ++ ys ++ zs) = true) (hx : xs.all (fun d => !d.isLabel) = true) (hk : KindD fr ys)
    (hph : ∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (ys ++ zs).length),
      runPhB okPc ph lab (lab r.1) ra r.2 = true) :
    (((t.drop xs.length).take ys.length).map (·.2)).length = ys.length ∧
      Cd1 cells okPc ph lab fr ra (lab l + Int64.ofNat (cellOff t xs.length))
        (ys.zip (((t.drop xs.length).take ys.length).map (·.2))) := by
  obtain ⟨hY, hat, hb, -⟩ := piece_of ht hseg hx (classify_of_kindD hf h1 hk) hph
  have hYe := zip_fst_snd ((t.drop xs.length).take ys.length)
  rw [hY] at hYe
  refine ⟨by simpa using congrArg List.length hY, ?_⟩
  rw [hYe]
  exact ⟨by show KindD fr _; rw [hY]; exact hk, .inl hat, hb⟩

/-- **The runs across an inner label** of a segment: of the runs from `xs`
over the label-free `ys` and the label `L`, the current one ends at
`xs ++ ys`, and the rest are the runs from `L`. -/
theorem runs_label {Q : Label × List (Directive × Nat) → Prop} (ht : after l cells = some t)
    {xs ys R : List Directive} {L : Label}
    (hseg : segIn cells l (xs ++ ys ++ .label L :: R) = true) (hy : ys.all (fun d => !d.isLabel) = true)
    (h : ∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (ys ++ .label L :: R).length), Q r) :
    Q (l, t.take (xs ++ ys).length) ∧
      ∀ r ∈ runsAux L [] ((t.drop ((xs ++ ys).length + 1)).take R.length), Q r := by
  have hS := slice_noLabel (seg_slice ht hseg) hy
  rw [List.length_append, runs_step hS] at h
  have hYL := seg_slice ht (xs := xs ++ ys) (ys := [.label L]) (zs := R)
    (by simpa only [List.append_assoc, List.singleton_append] using hseg)
  obtain ⟨⟨dl, z0⟩, hL1⟩ : ∃ p, (t.drop (xs ++ ys).length).take 1 = [p] :=
    List.length_eq_one_iff.mp (by simpa using congrArg List.length hYL)
  rw [List.length_singleton, hL1] at hYL
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hYL
  subst hYL
  rw [List.length_append] at hL1
  have hsplit : (t.drop (xs.length + ys.length)).take (1 + R.length) =
      (t.drop (xs.length + ys.length)).take 1 ++ (t.drop (xs.length + ys.length + 1)).take R.length := by
    rw [List.take_add, List.drop_drop]
  rw [show (Directive.label L :: R).length = 1 + R.length by simp; omega, hsplit, hL1] at h
  simp only [List.singleton_append, runsAux, List.mem_cons, forall_eq_or_imp, List.reverse_reverse] at h
  rw [List.length_append]
  exact h

/-- **An inner label of a segment**: the cells after it, the segment after
it, and its address (`hgap`). -/
theorem label_at (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (ht : after l cells = some t) {P R : List Directive} {L : Label}
    (hseg : segIn cells l (P ++ .label L :: R) = true) (hP : P.all (fun d => !d.isLabel) = true) :
    after L cells = some (t.drop (P.length + 1)) ∧ segIn cells L R = true ∧
      lab L = lab l + Int64.ofNat (cellOff t P.length) := by
  refine ⟨after_label hseg ht, segIn_label hseg, ?_⟩
  obtain ⟨t', ht', hg⟩ := labelGap_of_segIn hseg hP
  rw [ht] at ht'
  cases ht'
  exact hgap _ _ _ _ hg

include hf h1 in
/-- **A block's directives after its label give `Code1`**: the directives
`ds` (`Code1D`, the label counter at `k`) after the label-free `xs` and
before `zs` in the segment after `l` (the cells `t`), every run from there
passing `runPhB` at `lab` in the phase of `ra`, and `lab` following the
labels' gaps (`hgap`). Each fall-through's label (`retL fr.fn k`) starts a
new run. -/
theorem code1_of_seg (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    {tm : Scc.IR.Term} (htm : TermOK1 tm) :
    ∀ (is : List Scc.IR.Inst) (k : Nat) (ds : List Directive) (l : Label) (t : List (Directive × Nat))
      (xs zs : List Directive), (∀ i ∈ is, InstOK1 i) → Code1D fr k ds is tm →
      after l cells = some t → segIn cells l (xs ++ ds ++ zs) = true → xs.all (fun d => !d.isLabel) = true →
      (∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (ds ++ zs).length),
        runPhB okPc ph lab (lab r.1) ra r.2 = true) →
      (∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (ds ++ zs).length),
        ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) →
      Code1 fr (Cd1 cells okPc ph lab fr ra) (lab l + Int64.ofNat (cellOff t xs.length)) is tm
  | [], k, ds, l, t, xs, zs, _, hD, ht, hseg, hx, hph, hrl => by
    match tm, htm, hD with
    | .ret [w], _, ⟨lw, hg, he⟩ =>
      subst he
      have hcR : ∀ d ∈ retDirs lw, (classify d).isSome = true :=
        classify_of_kindD hf h1 (.inr (.inr (.inr ⟨w, lw, hg, rfl⟩)))
      have hRe : retDirs lw = tearDirs lw ++ [i64 .ret] := by rw [retDirs, dirs_epiItems_split, ← tearDirs]
      have hcT : ∀ d ∈ tearDirs lw, (classify d).isSome = true :=
        fun d hd => hcR d (by rw [hRe]; exact List.mem_append_left _ hd)
      have hcr : ∀ d ∈ [i64 .ret], (classify d).isSome = true :=
        fun d hd => hcR d (by rw [hRe]; exact List.mem_append_right _ hd)
      have hTl : (tearDirs lw).all (fun d => !d.isLabel) = true :=
        List.all_eq_true.mpr fun d hd => by simp [isLabel_of_classify (hcT d hd)]
      have hTne : tearDirs lw ≠ [] := by
        obtain ⟨dl, hdl⟩ := dirs_getOp hg
        rw [tearDirs, dirs_append, hdl]; simp
      -- the load and teardown
      have hseg1 : segIn cells l (xs ++ tearDirs lw ++ .label (retL fr.fn k) :: ([i64 .ret] ++ zs)) = true := by
        simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hseg
      have hph1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
          ((t.drop xs.length).take (tearDirs lw ++ .label (retL fr.fn k) :: ([i64 .ret] ++ zs)).length),
          runPhB okPc ph lab (lab r.1) ra r.2 = true := by
        simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hph
      have hrl1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
          ((t.drop xs.length).take (tearDirs lw ++ .label (retL fr.fn k) :: ([i64 .ret] ++ zs)).length),
          ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
        simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hrl
      obtain ⟨hY1, hat1, hb1, hp1⟩ := piece_of ht hseg1 hx hcT hph1
      have hxT : (xs ++ tearDirs lw).all (fun d => !d.isLabel) = true := by rw [List.all_append, hx, hTl]; rfl
      obtain ⟨ht2, hseg2, hsp⟩ := label_at hgap ht (by simpa only [List.append_assoc] using hseg1) hxT
      obtain ⟨-, hafter⟩ := runs_label ht hseg1 hTl hph1
      obtain ⟨-, hrafter⟩ := runs_label ht hseg1 hTl hrl1
      generalize hT2 : t.drop ((xs ++ tearDirs lw).length + 1) = t2 at ht2 hafter hrafter
      -- `ret`, after the return site's label
      have hph2 : ∀ r ∈ runsAux (retL fr.fn k) (t2.take ([] : List Directive).length).reverse
          ((t2.drop ([] : List Directive).length).take ([i64 .ret] ++ zs).length),
          runPhB okPc ph lab (lab r.1) ra r.2 = true := by simpa using hafter
      obtain ⟨hY2, hat2, hb2, -⟩ := piece_of (xs := []) ht2 (by simpa using hseg2) rfl hcr hph2
      simp only [List.length_nil, List.drop_zero, Spike.Lib.X64.cellOff_zero, show Int64.ofNat 0 = 0 from rfl,
        Int64.add_zero] at hY2 hat2 hb2
      have hphR : ph (lab (retL fr.fn k)).toBitVec.toNat = ph ra.toBitVec.toNat := by
        obtain ⟨y, hy⟩ := runsAux_head (retL fr.fn k) [] _
        exact hrafter _ hy
      have hphl : ph (lab l).toBitVec.toNat = ph ra.toBitVec.toNat := by
        obtain ⟨y, hy⟩ := runsAux_head l _ _
        exact hrl _ hy
      have hsp' : lab (retL fr.fn k) = lab l + Int64.ofNat (cellOff t xs.length) +
          Int64.ofNat (((t.drop xs.length).take (tearDirs lw).length).map (·.2)).sum := by
        rw [hsp, List.length_append, pc_step]
      have hp1' := hp1 hTne
      generalize (t.drop xs.length).take (tearDirs lw).length = Y1 at hY1 hat1 hb1 hsp'
      generalize t2.take [i64 .ret].length = Y2 at hY2 hat2 hb2
      generalize lab l + Int64.ofNat (cellOff t xs.length) = pc at hat1 hb1 hp1' hsp' ⊢
      have hm : (Y1 ++ Y2).map (·.1) = retDirs lw := by rw [List.map_append, hY1, hY2, hRe]
      refine ⟨lw, (Y1 ++ Y2).map (·.2), hg, by rw [← hm]; simp, ?_⟩
      have hz := zip_fst_snd (Y1 ++ Y2)
      rw [hm] at hz
      rw [hz]
      refine ⟨by show KindD fr _; rw [hm]; exact .inr (.inr (.inr ⟨w, lw, hg, rfl⟩)),
        .inr ⟨Y1, Y2, rfl, hat1, by rw [← hsp']; exact hat2⟩, ?_⟩
      exact blkPh_append1 hb1 (by rw [← hsp']; exact hb2) (by rw [← hsp', hphR, hp1', hphl])
    | .br .eq a b ct cf, _, ⟨la, lb, ha, hb, he⟩ =>
      subst he
      have hkb : KindD fr (brDirs la lb (labelOf fr.fn ct)) := .inl ⟨a, b, la, lb, ha, hb, .inr (.inr ⟨_, rfl⟩)⟩
      have hkj : KindD fr (jmpDirs (labelOf fr.fn cf)) := .inr (.inr (.inl ⟨_, rfl⟩))
      have hbl := kindD_noLabel hf h1 hkb
      have hseg1 : segIn cells l (xs ++ brDirs la lb (labelOf fr.fn ct) ++ (jmpDirs (labelOf fr.fn cf) ++ zs)) =
          true := by simpa only [List.append_assoc] using hseg
      have hph1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
          ((t.drop xs.length).take (brDirs la lb (labelOf fr.fn ct) ++ (jmpDirs (labelOf fr.fn cf) ++ zs)).length),
          runPhB okPc ph lab (lab r.1) ra r.2 = true := by simpa only [List.append_assoc] using hph
      obtain ⟨hlen, c1⟩ := cd1_piece hf h1 ht hseg1 hx hkb hph1
      have hS := slice_noLabel (seg_slice ht hseg1) hbl
      rw [List.length_append, runs_step hS] at hph1
      have hseg2 : segIn cells l ((xs ++ brDirs la lb (labelOf fr.fn ct)) ++ jmpDirs (labelOf fr.fn cf) ++ zs) =
          true := by simpa only [List.append_assoc] using hseg
      have hxb : (xs ++ brDirs la lb (labelOf fr.fn ct)).all (fun d => !d.isLabel) = true := by
        rw [List.all_append, hx, hbl]; rfl
      obtain ⟨hlen2, c2⟩ := cd1_piece hf h1 ht hseg2 hxb hkj (by simpa only [List.length_append] using hph1)
      obtain ⟨z, hz⟩ := length_one (zs := ((t.drop (xs ++ brDirs la lb (labelOf fr.fn ct)).length).take
        (jmpDirs (labelOf fr.fn cf)).length).map (·.2)) (by simpa [jmpDirs] using hlen2)
      rw [hz, List.length_append, pc_step] at c2
      exact ⟨la, lb, _, z, ha, hb, hlen, c1, c2⟩
  | i :: is, k, ds, l, t, xs, zs, hs, hD, ht, hseg, hx, hph, hrl => by
    have hs' := List.forall_mem_cons.mp hs
    cases i with
    | addChk d a b =>
      obtain ⟨la, lb, off, ds', ha, hb, hd, rfl, hD'⟩ := hD
      have hkA : KindD fr (addDirs fr la lb) := .inl ⟨a, b, la, lb, ha, hb, .inl rfl⟩
      have hkS : KindD fr [stDir off] := .inr (.inl ⟨d, off, hd, rfl⟩)
      have hAl := kindD_noLabel hf h1 hkA
      -- the checked add
      have hseg1 : segIn cells l (xs ++ addDirs fr la lb ++ .label (retL fr.fn k) :: ([stDir off] ++ (ds' ++ zs))) =
          true := by
        simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hseg
      have hph1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
          ((t.drop xs.length).take (addDirs fr la lb ++ .label (retL fr.fn k) :: ([stDir off] ++ (ds' ++ zs))).length),
          runPhB okPc ph lab (lab r.1) ra r.2 = true := by
        simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hph
      have hrl1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
          ((t.drop xs.length).take (addDirs fr la lb ++ .label (retL fr.fn k) :: ([stDir off] ++ (ds' ++ zs))).length),
          ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
        simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hrl
      obtain ⟨hlen, c1⟩ := cd1_piece hf h1 ht hseg1 hx hkA hph1
      have hxA : (xs ++ addDirs fr la lb).all (fun d => !d.isLabel) = true := by rw [List.all_append, hx, hAl]; rfl
      obtain ⟨ht2, hseg2, hsp⟩ := label_at hgap ht (by simpa only [List.append_assoc] using hseg1) hxA
      obtain ⟨-, hafter⟩ := runs_label ht hseg1 hAl hph1
      obtain ⟨-, hrafter⟩ := runs_label ht hseg1 hAl hrl1
      generalize t.drop ((xs ++ addDirs fr la lb).length + 1) = t2 at ht2 hafter hrafter
      -- the store, after the fall-through's label
      have hsegS : segIn cells (retL fr.fn k) ([] ++ [stDir off] ++ (ds' ++ zs)) = true := by simpa using hseg2
      have hphS : ∀ r ∈ runsAux (retL fr.fn k) (t2.take ([] : List Directive).length).reverse
          ((t2.drop ([] : List Directive).length).take ([stDir off] ++ (ds' ++ zs)).length),
          runPhB okPc ph lab (lab r.1) ra r.2 = true := by simpa using hafter
      have hrlS : ∀ r ∈ runsAux (retL fr.fn k) (t2.take ([] : List Directive).length).reverse
          ((t2.drop ([] : List Directive).length).take ([stDir off] ++ (ds' ++ zs)).length),
          ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by simpa using hrafter
      obtain ⟨hlenS, c2⟩ := cd1_piece hf h1 ht2 hsegS rfl hkS hphS
      have hSS := slice_noLabel (seg_slice ht2 hsegS) (kindD_noLabel hf h1 hkS)
      rw [show ([stDir off] ++ (ds' ++ zs)).length = [stDir off].length + (ds' ++ zs).length from
        List.length_append .., runs_step hSS] at hphS hrlS
      -- the rest of the block, the label counter at `k + 1`
      have c3 := code1_of_seg hgap htm is (k + 1) ds' (retL fr.fn k) t2 [stDir off] zs hs'.2 hD' ht2
        (by simpa using hsegS) (kindD_noLabel hf h1 hkS) (by simpa using hphS) (by simpa using hrlS)
      simp only [List.length_nil, List.drop_zero, Spike.Lib.X64.cellOff_zero, show Int64.ofNat 0 = 0 from rfl,
        Int64.add_zero] at hlenS c2
      obtain ⟨z, hz⟩ := length_one (zs := (t2.take [stDir off].length).map (·.2)) (by simpa using hlenS)
      rw [hz] at c2
      have hcz : cellOff t2 [stDir off].length = z := by
        unfold cellOff; rw [hz]; simp
      rw [hcz] at c3
      have hsp' : lab (retL fr.fn k) = lab l + Int64.ofNat (cellOff t xs.length) +
          Int64.ofNat (((t.drop xs.length).take (addDirs fr la lb).length).map (·.2)).sum := by
        rw [hsp, List.length_append, pc_step]
      refine ⟨la, lb, off, _, z, ha, hb, hd, hlen, c1, ?_, ?_⟩
      · rw [← hsp']; simpa only [List.zip_cons_cons, List.zip_nil_left] using c2
      · rw [← hsp']; exact c3
    | subSat d a b =>
      obtain ⟨la, lb, off, ds', ha, hb, hd, rfl, hD'⟩ := hD
      have hkA : KindD fr (subDirs la lb) := .inl ⟨a, b, la, lb, ha, hb, .inr (.inl rfl)⟩
      have hkS : KindD fr [stDir off] := .inr (.inl ⟨d, off, hd, rfl⟩)
      have hAl := kindD_noLabel hf h1 hkA
      have hSl := kindD_noLabel hf h1 hkS
      -- the saturating sub
      have hseg1 : segIn cells l (xs ++ subDirs la lb ++ ([stDir off] ++ (ds' ++ zs))) = true := by
        simpa only [List.append_assoc] using hseg
      have hph1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
          ((t.drop xs.length).take (subDirs la lb ++ ([stDir off] ++ (ds' ++ zs))).length),
          runPhB okPc ph lab (lab r.1) ra r.2 = true := by simpa only [List.append_assoc] using hph
      have hrl1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
          ((t.drop xs.length).take (subDirs la lb ++ ([stDir off] ++ (ds' ++ zs))).length),
          ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by simpa only [List.append_assoc] using hrl
      obtain ⟨hlen, c1⟩ := cd1_piece hf h1 ht hseg1 hx hkA hph1
      have hS := slice_noLabel (seg_slice ht hseg1) hAl
      rw [List.length_append, runs_step hS] at hph1 hrl1
      -- the store
      have hxA : (xs ++ subDirs la lb).all (fun d => !d.isLabel) = true := by rw [List.all_append, hx, hAl]; rfl
      have hseg2 : segIn cells l ((xs ++ subDirs la lb) ++ [stDir off] ++ (ds' ++ zs)) = true := by
        simpa only [List.append_assoc] using hseg
      have hph2 : ∀ r ∈ runsAux l (t.take (xs ++ subDirs la lb).length).reverse
          ((t.drop (xs ++ subDirs la lb).length).take ([stDir off] ++ (ds' ++ zs)).length),
          runPhB okPc ph lab (lab r.1) ra r.2 = true := by simpa only [List.length_append] using hph1
      have hrl2 : ∀ r ∈ runsAux l (t.take (xs ++ subDirs la lb).length).reverse
          ((t.drop (xs ++ subDirs la lb).length).take ([stDir off] ++ (ds' ++ zs)).length),
          ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by simpa only [List.length_append] using hrl1
      obtain ⟨hlenS, c2⟩ := cd1_piece hf h1 ht hseg2 hxA hkS hph2
      have hS2 := slice_noLabel (seg_slice ht hseg2) hSl
      rw [show ([stDir off] ++ (ds' ++ zs)).length = [stDir off].length + (ds' ++ zs).length from
        List.length_append .., runs_step hS2] at hph2 hrl2
      -- the rest of the block
      have hxAS : (xs ++ subDirs la lb ++ [stDir off]).all (fun d => !d.isLabel) = true := by
        rw [List.all_append, hxA, hSl]; rfl
      have c3 := code1_of_seg hgap htm is k ds' l t (xs ++ subDirs la lb ++ [stDir off]) zs hs'.2 hD' ht
        (by simpa only [List.append_assoc] using hseg) hxAS (by simpa only [List.length_append] using hph2)
        (by simpa only [List.length_append] using hrl2)
      obtain ⟨z, hz⟩ := length_one (zs := ((t.drop (xs ++ subDirs la lb).length).take [stDir off].length).map (·.2))
        (by simpa using hlenS)
      rw [hz, List.length_append, pc_step] at c2
      rw [List.length_append] at hz
      rw [List.length_append, List.length_append, pc_step, pc_step, hz] at c3
      exact ⟨la, lb, off, _, z, ha, hb, hd, hlen, c1, by simpa only [List.zip_cons_cons, List.zip_nil_left] using c2,
        by simpa using c3⟩
    | _ => exact (hs'.1).elim

end Code

/-! ## From the placement checks -/

section Place

variable {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
  {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {ra : Int64}
  {lo : Nat}

include hf h1 in
/-- **A placed block's code gives `Code1`** at its label, its label counter
from `n`: its code after the label (`segIn`) and its runs' phase facts at
the code labels (`labC`), every label read resolving, which `lab` agrees
with (`hlab`), and `lab` following the labels' gaps (`hgap`); every
instruction with a safepoint map (`hms`). -/
theorem code1_block (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {b : Scc.IR.Block} (hs : BlkOK1 b.insts b.term) {ms : List (Option Scc.IR.StackMap.Entry)}
    (hms : b.insts.length ≤ ms.length) {n n' : Nat} {code : List Item}
    (hc : blockItems fr n b ms = .ok (code, n'))
    (hseg : segIn cells (labelOf fr.fn b.label) (directives code) = true)
    (hph : ∀ r ∈ runs (labelOf fr.fn b.label) (segCells cells (labelOf fr.fn b.label) (directives code).length),
      runPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) ra r = true ∧
        ph (labC lo cells r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    Code1 fr (Cd1 cells okPc ph lab fr ra) (lab (labelOf fr.fn b.label)) b.insts b.term := by
  obtain ⟨lb, is, tm⟩ := b
  simp only at hs hms hseg hph ⊢
  unfold blockItems at hc
  split at hc
  · next s heq =>
    cases hc
    obtain ⟨c, hout, hD⟩ := blockCode_spec fr lb hs.2 is ms _ _ hs.1 hms heq
    have hcs : s.out.reverse = c := by rw [hout]; simp
    rw [hcs] at hseg hph
    simp only [directives_eq_dirs] at hseg hph
    obtain ⟨i, hi, -, -⟩ := segIn_iff.mp hseg
    obtain ⟨t, ht⟩ : ∃ t, after (labelOf fr.fn lb) cells = some t := ⟨_, by rw [after_eq, hi]; rfl⟩
    have hsc : segCells cells (labelOf fr.fn lb) (dirs c).length = t.take (dirs c).length := by
      unfold segCells; rw [ht]
    rw [hsc] at hph
    have := code1_of_seg (okPc := okPc) (ph := ph) (ra := ra) hf h1 hgap hs.2 is n (dirs c) _ t [] [] hs.1 hD ht
      (by simpa using hseg) rfl
      (fun r hr => by
        have h' := (hph r (by simpa [runs] using hr)).1
        simp only [runPh, Bool.and_eq_true] at h'
        obtain ⟨⟨hres, hlabs⟩, hrun⟩ := h'
        rw [labC_eq hlab hres, runPhB_congr fun L hL => labC_eq hlab (List.all_eq_true.mp hlabs L hL)] at hrun
        exact hrun)
      (fun r hr => by
        have h' := hph r (by simpa [runs] using hr)
        simp only [runPh, Bool.and_eq_true] at h'
        obtain ⟨⟨⟨hres, -⟩, -⟩, hp⟩ := h'
        rw [labC_eq hlab hres] at hp
        exact hp)
    simpa [Spike.Lib.X64.cellOff_zero] using this
  · cases hc

include hf h1 in
/-- **The later blocks' code** (`BlocksCode`) at `Cd1`, from the
function's `blocksOk` and `blocksPh` (the blocks `bs` after `pre`, each with
its safepoint maps `G b`, one per instruction). -/
theorem blocksCode1 (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {G : Scc.IR.Block → List (Option Scc.IR.StackMap.Entry)} (hG : ∀ b, (G b).length = b.insts.length)
    {n : Nat} {pre bs : List Scc.IR.Block}
    (hok : blocksOk cells fr n ((pre ++ bs).map fun b => (b, G b)) = true)
    (hph : blocksPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) cells fr ra n
      ((pre ++ bs).map fun b => (b, G b)) = true)
    (hs : ∀ b ∈ bs, BlkOK1 b.insts b.term) :
    BlocksCode fr (Cd1 cells okPc ph lab fr ra) lab bs := by
  intro b hb
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hb
  have e : (pre ++ (s ++ b :: t)).map (fun b => (b, G b)) =
      (pre ++ s).map (fun b => (b, G b)) ++ (b, G b) :: t.map (fun b => (b, G b)) := by simp
  rw [e] at hok hph
  obtain ⟨code, n', hc, hseg⟩ := blocksOk_block hok
  obtain ⟨code', n'', hc', hr⟩ := blocksPh_blockPh hph
  rw [hc] at hc'; cases hc'
  exact code1_block hf h1 hgap hlab (hs b hb) (Nat.le_of_eq (hG b).symm) hc hseg hr

include hf h1 in
/-- **The entry block's code** (`Code1` at the entry's label) from the
function's `blocksOk` and `blocksPh`. -/
theorem entryCode1 (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {G : Scc.IR.Block → List (Option Scc.IR.StackMap.Entry)} (hG : ∀ b, (G b).length = b.insts.length)
    {n : Nat} {b : Scc.IR.Block} {bs : List Scc.IR.Block}
    (hok : blocksOk cells fr n ((b :: bs).map fun b => (b, G b)) = true)
    (hph : blocksPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) cells fr ra n
      ((b :: bs).map fun b => (b, G b)) = true)
    (hs : BlkOK1 b.insts b.term) :
    Code1 fr (Cd1 cells okPc ph lab fr ra) (lab (labelOf fr.fn b.label)) b.insts b.term := by
  obtain ⟨code, n', hc, hseg⟩ := blocksOk_block (pre := []) hok
  obtain ⟨code', n'', hc', hr⟩ := blocksPh_blockPh (pre := []) hph
  rw [hc] at hc'; cases hc'
  exact code1_block hf h1 hgap hlab hs (Nat.le_of_eq (hG b).symm) hc hseg hr

end Place

/-! ## The labels' gaps on a laid-out program -/

section Lays

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}

/-- **`code1_of_seg`'s `hgap`** at the labels of a laid-out program. -/
theorem hgap_of_lays (hp : Scc.Cert.Rt.X64.Lays exe cells kp) :
    ∀ a b n off, labelGap cells a b n off = true →
      (_root_.Executable.labels exe).label b = (_root_.Executable.labels exe).label a + Int64.ofNat off :=
  fun _ _ _ _ h => Scc.Cert.Rt.X64.label_labelGap_lays hp h

end Lays

/-- **`code1_of_seg`'s `hgap` at the layout of an output passing `PlaceOK`.** -/
theorem hgap_ofPlaceOK {cfg : Scc.Config} {p : CoreTerm.Prog} {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    ∀ a b n off, labelGap (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      a b n off = true →
      (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i).lab b =
        (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i).lab a + Int64.ofNat off := by
  haveI := (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i).valid
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := Spike.Lib.X64.Rt.rS0 (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i))
  intro a b n off hg
  rw [← hI.labOk]
  exact hgap_of_lays hI.lays a b n off hg

theorem zip_map_self {α β : Type} (G : α → β) : ∀ l : List α, l.zip (l.map G) = l.map fun b => (b, G b)
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.zip_cons_cons, zip_map_self G l]

/-- **A function's blocks with their safepoint maps**: one map per
instruction of each block. -/
theorem zip_callMaps (f : Scc.IR.Func) :
    ∃ G : Scc.IR.Block → List (Option Scc.IR.StackMap.Entry),
      f.blocks.zip (Scc.IR.StackMap.callMaps f) = f.blocks.map (fun b => (b, G b)) ∧
        ∀ b, (G b).length = b.insts.length := by
  unfold Scc.IR.StackMap.callMaps Scc.IR.StackMap.callLives
  simp only [List.map_map]
  refine ⟨_, zip_map_self _ _, fun b => ?_⟩
  simp only [Function.comp, List.length_map]
  generalize Scc.IR.StackMap.union _ _ = z
  generalize b.insts = l
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, List.length_cons, ih]

end Spike.Lib.LowerX64
