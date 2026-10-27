/-
**A call-free `Accepted1` function's blocks from the placement checks**
(x86-64): `body1_seg`'s code premises (`Code1` of the open block,
`BlocksCode` of the later ones) from `blocksOk` and `blocksPh`, at a code
predicate `Cd1` carrying each construct's block placed (`blockAt`), its
phase check (`blkPh`, no dead target) and its kind (`Kind1`); the twin of
`Spike/Lib/LowerA64/Blocks1.lean`.

- `lower1_shape`: the lowering of a call-free `Accepted1` body has only
  checked `+`s and saturating `-`s, and only `ret [w]` and `br .eq`
  terminators (`BlkOK1`).
- `emitInst_add_cases`, `emitInst_sub_cases`, `blockCode_spec`: the
  emitter's code of a block, split into the constructs' directives
  (`Code1D`).
- `KindD`, `Kind1`, `kind1_ok`: a construct's block is covered at the
  frame's offsets, so every directive of it is classified and none is a
  label.
- `code1_of_seg`: a block's directives after its label (`segIn`) passing
  its run's phase check give `Code1` at `Cd1`, each construct's block at
  the sizes the listing gives.
- `code1_block`, `blocksCode1`, `entryCode1`: from a block's
  `blocksOk`/`blocksPh` facts; `zip_callMaps`: every block's safepoint maps
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
open Scc.Emit.X64 (S E Item emitInst emitTerm ld st ins labelOf cmpAB directives)
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (blockAt after after_eq)
open Scc.Cert.Code1X64 (blockCode blockItems blocksOk segIn segIn_iff blockAt_of_segIn blocksOk_block
  take_drop_append)
open Scc.Cert.Ph1X64 (runs runsAux runPh runPhB blocksPh blocksPh_block blkPh_of_runPhB runsAux_nil segCells
  segCells_map)
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

/-- **The code of a checked `+`**: both operands' loads, the checked add,
the store. -/
theorem emitInst_add_cases (fr : Scc.Emit.X64.Frame) (sm) (d : Scc.IR.Reg) (a b : Scc.IR.Operand) (s : S) {u s'}
    (h : emitInst fr sm (.addChk d a b) s = .ok (u, s')) :
    ∃ la lb off, getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧ rsOf fr d = some off ∧
      s' = { s with out := (la ++ lb ++ addChecked (ovfL fr) ++ [Item.d (stDir off)]).reverse ++ s.out } := by
  rw [Scc.Lower.InvX64.emitInst_addChk] at h
  rcases ld_cases fr a .rax s with ⟨la, ha, e1⟩ | ⟨e, e1⟩
  · rw [bind_ok e1] at h
    rcases ld_cases fr b .rcx { s with out := la.reverse ++ s.out } with ⟨lb, hb, e2⟩ | ⟨e, e2⟩
    · rw [bind_ok e2, bind_ok (ins_eq _ _), bind_ok (ins_eq _ _)] at h
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

/-- **A block's directives, construct by construct**: each checked `+`'s or
saturating `-`'s directives and its store, then the rest; then a `ret`'s
or an `if`'s (`Code1`'s blocks, before the listing gives them sizes). -/
def Code1D (fr : Scc.Emit.X64.Frame) : List Directive → List Scc.IR.Inst → Scc.IR.Term → Prop
  | ds, [], .ret [w] => ∃ l, getOp fr .rax w = .ok l ∧ ds = retDirs l
  | ds, [], .br .eq a b ct cf => ∃ la lb, getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧
      ds = brDirs la lb (labelOf fr.fn ct) ++ jmpDirs (labelOf fr.fn cf)
  | ds, .addChk d a b :: is, tm => ∃ la lb off ds', getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧
      rsOf fr d = some off ∧ ds = addDirs fr la lb ++ [stDir off] ++ ds' ∧ Code1D fr ds' is tm
  | ds, .subSat d a b :: is, tm => ∃ la lb off ds', getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧
      rsOf fr d = some off ∧ ds = subDirs la lb ++ [stDir off] ++ ds' ∧ Code1D fr ds' is tm
  | _, _, _ => False

/-- **The emitter's code of a `BlkOK1` block** (every instruction with a
safepoint map): appended to the output, its directives `Code1D`. -/
theorem blockCode_spec (fr : Scc.Emit.X64.Frame) (lb : Scc.IR.Label) {tm : Scc.IR.Term} (htm : TermOK1 tm) :
    ∀ (is : List Scc.IR.Inst) (ms : List (Option Scc.IR.StackMap.Entry)) (s s' : S),
      (∀ i ∈ is, InstOK1 i) → is.length ≤ ms.length → blockCode fr ⟨lb, is, tm⟩ ms s = .ok ((), s') →
      ∃ c, s' = { s with out := c.reverse ++ s.out } ∧ Code1D fr (dirs c) is tm
  | [], ms, s, s', _, _, h => by
    rw [blockCode_nil] at h
    match tm, htm, h with
    | .ret [w], _, h =>
      rcases ld_cases fr w .rax s with ⟨l, hl, -⟩ | ⟨e, he⟩
      · rw [emitTerm_ret hl s] at h
        cases h
        exact ⟨l ++ epiItems, rfl, l, hl, rfl⟩
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
    obtain ⟨c', rfl, hc'⟩ := blockCode_spec fr lb htm is ms s1 s' hs'.2 (by simpa using hl) h2
    cases i with
    | addChk d a b =>
      obtain ⟨la, lb, off, ha, hb, hd, rfl⟩ := emitInst_add_cases fr m d a b s h1
      refine ⟨la ++ lb ++ addChecked (ovfL fr) ++ [Item.d (stDir off)] ++ c', ?_,
        la, lb, off, dirs c', ha, hb, hd, ?_, hc'⟩
      · simp [List.reverse_append, List.append_assoc]
      · rw [dirs_append, dirs_append]; rfl
    | subSat d a b =>
      obtain ⟨la, lb, off, ha, hb, hd, rfl⟩ := emitInst_sub_cases fr m d a b s h1
      refine ⟨la ++ lb ++ subSatItems ++ [Item.d (stDir off)] ++ c', ?_,
        la, lb, off, dirs c', ha, hb, hd, ?_, hc'⟩
      · simp [List.reverse_append, List.append_assoc]
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

/-- **A block's directives are label-free.** -/
theorem code1D_noLabel {tm : Scc.IR.Term} :
    ∀ {is : List Scc.IR.Inst} {ds : List Directive}, Code1D fr ds is tm → ds.all (fun d => !d.isLabel) = true
  | [], ds, h => by
    match tm, h with
    | .ret [w], ⟨l, hg, he⟩ => subst he; exact kindD_noLabel hf h1 (.inr (.inr (.inr ⟨w, l, hg, rfl⟩)))
    | .br .eq a b ct cf, ⟨la, lb, ha, hb, he⟩ =>
      subst he
      rw [List.all_append, kindD_noLabel hf h1 (.inl ⟨a, b, la, lb, ha, hb, .inr (.inr ⟨_, rfl⟩)⟩),
        kindD_noLabel hf h1 (.inr (.inr (.inl ⟨_, rfl⟩)))]; rfl
  | .addChk d a b :: is, ds, ⟨la, lb, off, ds', ha, hb, hd, he, h⟩ => by
    subst he
    rw [List.all_append, List.all_append, kindD_noLabel hf h1 (.inl ⟨a, b, la, lb, ha, hb, .inl rfl⟩),
      kindD_noLabel hf h1 (.inr (.inl ⟨d, off, hd, rfl⟩)), code1D_noLabel h]; rfl
  | .subSat d a b :: is, ds, ⟨la, lb, off, ds', ha, hb, hd, he, h⟩ => by
    subst he
    rw [List.all_append, List.all_append, kindD_noLabel hf h1 (.inl ⟨a, b, la, lb, ha, hb, .inr (.inl rfl)⟩),
      kindD_noLabel hf h1 (.inr (.inl ⟨d, off, hd, rfl⟩)), code1D_noLabel h]; rfl

end Kinds

/-! ## The code predicate -/

/-- **The code predicate of a call-free `Accepted1` body**: `blk` is a
construct's block (`Kind1`) at `pc`, `k` cells and `off` bytes after the
label `l` (`blockAt`), passing the phase check at `pc` with no dead target
and the return address `ra`. -/
def Cd1 (cells : List (Directive × Nat)) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64)
    (fr : Scc.Emit.X64.Frame) (ra : Int64) (pc : Int64) (blk : List (Directive × Nat)) : Prop :=
  Kind1 fr blk ∧ ∃ l k off, lab l + Int64.ofNat off = pc ∧ blockAt cells l k off blk = true ∧
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
  {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab0 : Label → Int64} {ra : Int64}

include hf h1 in
/-- **A construct's block inside a placed run** is at `Cd1`: the run
`xs ++ ys ++ zs` after `l` (`segIn`; the cells after `l` are `t`) passing its
phase check at the check's labels `lab0`, which agree with `lab` on the
run's targets; `ys` at the sizes of its cells. -/
theorem cd1_of (ht : after l cells = some t) {xs ys zs : List Directive}
    (hseg : segIn cells l (xs ++ ys ++ zs) = true) (hx : xs.all (fun d => !d.isLabel) = true) (hk : KindD fr ys)
    (hph : runPhB okPc ph lab0 (lab l) ra (t.take (xs ++ ys ++ zs).length) = true)
    (hL : ∀ L ∈ blkLabs (t.take (xs ++ ys ++ zs).length), lab0 L = lab L) :
    Cd1 cells okPc ph lab fr ra (lab l + Int64.ofNat (cellOff t xs.length))
      (ys.zip (((t.drop xs.length).take ys.length).map (·.2))) := by
  have hY := seg_slice ht hseg
  have hYe := zip_fst_snd ((t.drop xs.length).take ys.length)
  rw [hY] at hYe
  rw [hYe]
  have hk1 : Kind1 fr ((t.drop xs.length).take ys.length) := by
    show KindD fr (((t.drop xs.length).take ys.length).map (·.1)); rw [hY]; exact hk
  have hok := kind1_ok hf h1 hk1
  obtain ⟨t', ht', -, hb⟩ := blockAt_of_segIn hseg hx (kindD_noLabel hf h1 hk)
  rw [ht] at ht'
  obtain rfl := Option.some.inj ht'
  refine ⟨hk1, l, xs.length, cellOff t xs.length, rfl, hb, ?_⟩
  have hN := seg_take ht hseg
  have hlen : (xs ++ ys ++ zs).length ≤ t.length := by
    have := congrArg List.length hN
    simp only [List.length_map, List.length_take] at this
    omega
  have hsplit := take_split t xs.length ys.length (xs ++ ys ++ zs).length (by simp)
  rw [hsplit] at hph hL
  have hb' := blkPh_of_runPhB hph (classify_of_okBlk hok)
  rw [← hsplit, List.length_take, Nat.min_eq_left (by simp at hlen ⊢; omega),
    cellOff_take _ (by simp)] at hb'
  rwa [blkPh_congr (lab' := lab) fun L hL' => hL L (by
    simp only [blkLabs, List.filterMap_append, List.mem_append] at hL' ⊢; exact .inl (.inr hL'))] at hb'

include hf h1 in
/-- **A block's directives after its label give `Code1`**: the directives
`ds` (`Code1D`) after the label-free `xs` and before `zs` in the run after
`l` (the cells `t`), passing the run's phase check. -/
theorem code1_of_seg (ht : after l cells = some t) {tm : Scc.IR.Term} (htm : TermOK1 tm) :
    ∀ (is : List Scc.IR.Inst) (ds xs zs : List Directive), (∀ i ∈ is, InstOK1 i) → Code1D fr ds is tm →
      segIn cells l (xs ++ ds ++ zs) = true → xs.all (fun d => !d.isLabel) = true →
      runPhB okPc ph lab0 (lab l) ra (t.take (xs ++ ds ++ zs).length) = true →
      (∀ L ∈ blkLabs (t.take (xs ++ ds ++ zs).length), lab0 L = lab L) →
      Code1 fr (Cd1 cells okPc ph lab fr ra) (lab l + Int64.ofNat (cellOff t xs.length)) is tm
  | [], ds, xs, zs, _, hD, hseg, hx, hph, hL => by
    match tm, htm, hD with
    | .ret [w], _, ⟨lw, hg, he⟩ =>
      subst he
      exact ⟨lw, _, hg, slice_len ht hseg,
        cd1_of hf h1 ht hseg hx (.inr (.inr (.inr ⟨w, lw, hg, rfl⟩))) hph hL⟩
    | .br .eq a b ct cf, _, ⟨la, lb, ha, hb, he⟩ =>
      subst he
      have e : ∀ zs' : List Directive, xs ++ (brDirs la lb (labelOf fr.fn ct) ++ jmpDirs (labelOf fr.fn cf)) ++ zs' =
          xs ++ brDirs la lb (labelOf fr.fn ct) ++ (jmpDirs (labelOf fr.fn cf) ++ zs') := by
        intro; simp only [List.append_assoc]
      have e' : ∀ zs' : List Directive, xs ++ (brDirs la lb (labelOf fr.fn ct) ++ jmpDirs (labelOf fr.fn cf)) ++ zs' =
          (xs ++ brDirs la lb (labelOf fr.fn ct)) ++ jmpDirs (labelOf fr.fn cf) ++ zs' := by
        intro; simp only [List.append_assoc]
      have hkb : KindD fr (brDirs la lb (labelOf fr.fn ct)) := .inl ⟨a, b, la, lb, ha, hb, .inr (.inr ⟨_, rfl⟩)⟩
      rw [e] at hseg hph hL
      have hlen := slice_len ht hseg
      have c1 := cd1_of hf h1 ht hseg hx hkb hph hL
      rw [← e, e'] at hseg hph hL
      have hxb : (xs ++ brDirs la lb (labelOf fr.fn ct)).all (fun d => !d.isLabel) = true := by
        rw [List.all_append, hx, kindD_noLabel hf h1 hkb]; rfl
      have c2 := cd1_of hf h1 ht hseg hxb (.inr (.inr (.inl ⟨_, rfl⟩))) hph hL
      obtain ⟨z, hz⟩ := length_one (slice_len ht hseg)
      rw [hz, List.length_append, pc_step] at c2
      exact ⟨la, lb, _, z, ha, hb, hlen, c1, c2⟩
  | i :: is, ds, xs, zs, hs, hD, hseg, hx, hph, hL => by
    have hs' := List.forall_mem_cons.mp hs
    -- the construct's block `A` and its store
    have step : ∀ (A : List Directive) (off : Int) (ds' : List Directive), KindD fr A →
        (∃ d, rsOf fr d = some off) → ds = A ++ [stDir off] ++ ds' → Code1D fr ds' is tm →
        ∃ zs0 z, zs0.length = A.length ∧
          Cd1 cells okPc ph lab fr ra (lab l + Int64.ofNat (cellOff t xs.length)) (A.zip zs0) ∧
          Cd1 cells okPc ph lab fr ra (lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zs0.sum)
            [(stDir off, z)] ∧
          Code1 fr (Cd1 cells okPc ph lab fr ra)
            (lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zs0.sum + Int64.ofNat z) is tm := by
      intro A off ds' hkA ⟨d, hd⟩ hds hD'
      subst hds
      have hkS : KindD fr [stDir off] := .inr (.inl ⟨d, off, hd, rfl⟩)
      have r1 : xs ++ (A ++ [stDir off] ++ ds') ++ zs = xs ++ A ++ ([stDir off] ++ ds' ++ zs) := by
        simp only [List.append_assoc]
      have r2 : xs ++ (A ++ [stDir off] ++ ds') ++ zs = (xs ++ A) ++ [stDir off] ++ (ds' ++ zs) := by
        simp only [List.append_assoc]
      have r3 : xs ++ (A ++ [stDir off] ++ ds') ++ zs = (xs ++ A ++ [stDir off]) ++ ds' ++ zs := by
        simp only [List.append_assoc]
      have hxA : (xs ++ A).all (fun d => !d.isLabel) = true := by
        rw [List.all_append, hx, kindD_noLabel hf h1 hkA]; rfl
      have hxAS : (xs ++ A ++ [stDir off]).all (fun d => !d.isLabel) = true := by
        rw [List.all_append, hxA, kindD_noLabel hf h1 hkS]; rfl
      rw [r1] at hseg hph hL
      have hlen := slice_len ht hseg
      have c1 := cd1_of hf h1 ht hseg hx hkA hph hL
      rw [← r1, r2] at hseg hph hL
      have c2 := cd1_of hf h1 ht hseg hxA hkS hph hL
      obtain ⟨z, hz⟩ := length_one (slice_len ht hseg)
      rw [hz, List.length_append, pc_step] at c2
      rw [List.length_append] at hz
      rw [← r2, r3] at hseg hph hL
      have c3 := code1_of_seg ht htm is ds' (xs ++ A ++ [stDir off]) zs hs'.2 hD' hseg hxAS hph hL
      rw [List.length_append, List.length_append, pc_step, pc_step, hz] at c3
      exact ⟨_, z, hlen, c1, c2, by simpa using c3⟩
    cases i with
    | addChk d a b =>
      obtain ⟨la, lb, off, ds', ha, hb, hd, hds, hD'⟩ := hD
      obtain ⟨zs0, z, hlen, c1, c2, c3⟩ := step _ off ds' (.inl ⟨a, b, la, lb, ha, hb, .inl rfl⟩) ⟨d, hd⟩ hds hD'
      exact ⟨la, lb, off, zs0, z, ha, hb, hd, hlen, c1, c2, c3⟩
    | subSat d a b =>
      obtain ⟨la, lb, off, ds', ha, hb, hd, hds, hD'⟩ := hD
      obtain ⟨zs0, z, hlen, c1, c2, c3⟩ :=
        step _ off ds' (.inl ⟨a, b, la, lb, ha, hb, .inr (.inl rfl)⟩) ⟨d, hd⟩ hds hD'
      exact ⟨la, lb, off, zs0, z, ha, hb, hd, hlen, c1, c2, c3⟩
    | _ => exact (hs'.1).elim

end Code

/-! ## From the placement checks -/

section Place

variable {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
  {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {ra : Int64}
  {lo : Nat}

include hf h1 in
/-- **A placed block's code gives `Code1`** at its label: its code after
the label (`segIn`) and its runs' phase facts at the code labels
(`labC`), every label read resolving, which `lab` agrees with (`hlab`);
every instruction with a safepoint map (`hms`). -/
theorem code1_block (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {b : Scc.IR.Block} (hs : BlkOK1 b.insts b.term) {ms : List (Option Scc.IR.StackMap.Entry)}
    (hms : b.insts.length ≤ ms.length) {n n' : Nat} {code : List Item}
    (hc : blockItems fr n b ms = .ok (code, n'))
    (hseg : segIn cells (labelOf fr.fn b.label) (directives code) = true)
    (hph : ∀ r ∈ runs (labelOf fr.fn b.label) (segCells cells (labelOf fr.fn b.label) (directives code).length),
      runPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) ra r = true) :
    Code1 fr (Cd1 cells okPc ph lab fr ra) (lab (labelOf fr.fn b.label)) b.insts b.term := by
  obtain ⟨lb, is, tm⟩ := b
  simp only at hs hms hseg hph ⊢
  unfold blockItems at hc
  split at hc
  · next s heq =>
    cases hc
    obtain ⟨c, rfl, hD⟩ := blockCode_spec fr lb hs.2 is ms _ _ hs.1 hms heq
    simp only [List.append_nil, List.reverse_reverse, directives_eq_dirs] at hseg hph ⊢
    obtain ⟨i, hi, -, -⟩ := segIn_iff.mp hseg
    obtain ⟨t, ht⟩ : ∃ t, after (labelOf fr.fn lb) cells = some t := ⟨_, by rw [after_eq, hi]; rfl⟩
    have hT := seg_take ht hseg
    have hnl : ∀ d ∈ t.take (dirs c).length, d.1.isLabel = false := by
      intro d hd
      have hm : d.1 ∈ dirs c := by rw [← hT]; exact List.mem_map_of_mem hd
      simpa using List.all_eq_true.mp (code1D_noLabel hf h1 hD) d.1 hm
    have hsc : segCells cells (labelOf fr.fn lb) (dirs c).length = t.take (dirs c).length := by
      unfold segCells; rw [ht]
    rw [hsc] at hph
    have hr := hph (labelOf fr.fn lb, t.take (dirs c).length) (by rw [runs, runsAux_nil _ [] _ hnl]; simp)
    simp only [runPh, Bool.and_eq_true] at hr
    obtain ⟨⟨hres, hlabs⟩, hrun⟩ := hr
    rw [labC_eq hlab hres] at hrun
    have := code1_of_seg (lab0 := labC lo cells) hf h1 ht hs.2 is (dirs c) [] [] hs.1 hD
      (by simpa using hseg) rfl (by simpa using hrun)
      (fun L hL => labC_eq hlab (List.all_eq_true.mp hlabs L (by simpa using hL)))
    have h0 : cellOff t ([] : List Directive).length = 0 := rfl
    rwa [h0, show Int64.ofNat 0 = 0 from rfl, Int64.add_zero] at this
  · cases hc

include hf h1 in
/-- **The later blocks' code** (`BlocksCode`) at `Cd1`, from the
function's `blocksOk` and `blocksPh` (the blocks `bs` after `pre`, each with
its safepoint maps `G b`, one per instruction). -/
theorem blocksCode1 (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
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
  obtain ⟨code', n'', hc', hr⟩ := blocksPh_block hph
  rw [hc] at hc'; cases hc'
  exact code1_block hf h1 hlab (hs b hb) (Nat.le_of_eq (hG b).symm) hc hseg hr

include hf h1 in
/-- **The entry block's code** (`Code1` at the entry's label) from the
function's `blocksOk` and `blocksPh`. -/
theorem entryCode1 (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {G : Scc.IR.Block → List (Option Scc.IR.StackMap.Entry)} (hG : ∀ b, (G b).length = b.insts.length)
    {n : Nat} {b : Scc.IR.Block} {bs : List Scc.IR.Block}
    (hok : blocksOk cells fr n ((b :: bs).map fun b => (b, G b)) = true)
    (hph : blocksPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) cells fr ra n
      ((b :: bs).map fun b => (b, G b)) = true)
    (hs : BlkOK1 b.insts b.term) :
    Code1 fr (Cd1 cells okPc ph lab fr ra) (lab (labelOf fr.fn b.label)) b.insts b.term := by
  obtain ⟨code, n', hc, hseg⟩ := blocksOk_block (pre := []) hok
  obtain ⟨code', n'', hc', hr⟩ := blocksPh_block (pre := []) hph
  rw [hc] at hc'; cases hc'
  exact code1_block hf h1 hlab hs (Nat.le_of_eq (hG b).symm) hc hseg hr

end Place

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
