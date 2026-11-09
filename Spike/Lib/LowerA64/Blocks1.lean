/-
**A call-free `Accepted1` function's blocks from the placement checks**
(AArch64): `body1_seg`'s code premises (`Code1` of the open block,
`BlocksCode` of the later ones) from `blocksOk` and `blocksPh`, at a code
predicate `Cd1` carrying each construct's block placed (`blockAt`), its
phase check (`blkPh`, no dead target) and its kind (`Kind1`).

- `lower1_shape`: the lowering of a call-free `Accepted1` body has only
  checked `+`s and saturating `-`s, and only `ret [w]` and `br .eq`
  terminators (`BlkOK1`).
- `inst_addChk_inv`, `inst_subSat_inv`, `term_br_inv`, `term_ret_inv`: the
  emitter's code of each, split into the constructs' blocks, with the fresh
  labels P5 adds after each checked `+` and before each `ret` (`x{k}`).
- `Kind1`, `kind1_ins`, `kind1_ok`: a construct's block is instructions
  only and covered at the frame's offsets.
- `Cd1`: a construct's block placed (`At1`) whole or in two pieces (a
  `ret`'s, around its return site's label), passing its phase check;
  `CodeAt.append`, `CdOf.append` join the pieces' code.
- `code1_of_seg`: a block's code after its label (`segIn`), every run from
  there passing its phase check, gives `Code1` at `Cd1`; each fresh label
  starts a new run, at the address `labelGap` gives (`hgap`).
- `code1_block`, `blocksCode1`, `entryCode1`: from a block's
  `blocksOk`/`blocksPh` facts (`blocksPh_blockPh`).
-/
import Spike.Lib.LowerA64.Body1
import Spike.Lib.LowerA64.MainCode1

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (blockAt labelGap isIns)
open Scc.Cert.Code1A64 (blocksOk blockItems instsItems kAfter segIn blockAt_of_segIn blocksOk_block segIn_label
  labelGap_of_segIn)
open Scc.Cert.Ph1A64 (runs runsAux runPh runPhB blocksPh blocksPh_block blocksPh_blockPh blkPh_of_runPhB runsAux_nil
  runsAux_label runPhB_get)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64Consumer (blkPh)
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

/-! ## The emitter's code, split into the constructs' blocks -/

section Emit

variable {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095)

include hf h1 in
/-- **The code of a checked `+`**: the add's block, the fall-through's
label `x{k}` (P5), then the store's. -/
theorem inst_addChk_inv {k : Nat} {d : Scc.IR.Reg} {a b : Scc.IR.Operand} {ci : List Item}
    (h : cx.inst k (.addChk d a b) = .ok ci) :
    ∃ la lb off, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧ cx.slotOff d = .ok off ∧
      directives ci = addDirs cx la lb ++ .label (cx.local s!"x{k}") :: strDirs off := by
  cases ha : cx.getOp .X9 a <;> cases hb : cx.getOp .X10 b <;> cases hd : cx.slotOff d
  case ok.ok.ok la lb off =>
    rw [inst_addChk hf (by omega) k ha hb hd] at h
    cases h
    refine ⟨la, lb, off, rfl, rfl, rfl, ?_⟩
    simp only [addDirs, strDirs, directives_append, List.append_assoc]
    rfl
  all_goals simp [FnCtx.inst, FnCtx.setReg, ha, hb, hd, bind, Except.bind] at h

include hf h1 in
/-- **The code of a saturating `-`**: the subtraction's block, then the
store's. -/
theorem inst_subSat_inv {k : Nat} {d : Scc.IR.Reg} {a b : Scc.IR.Operand} {ci : List Item}
    (h : cx.inst k (.subSat d a b) = .ok ci) :
    ∃ la lb off, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧ cx.slotOff d = .ok off ∧
      directives ci = subDirs la lb ++ strDirs off := by
  cases ha : cx.getOp .X9 a <;> cases hb : cx.getOp .X10 b <;> cases hd : cx.slotOff d
  case ok.ok.ok la lb off =>
    have he : cx.inst k (.subSat d a b) = .ok (la ++ lb ++ subSat .X9 .X9 .X10 ++
        [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 off, none⟩⟩)]) := by
      simp only [FnCtx.inst, ha, hb, setReg_eq hf (by omega) hd, bind, Except.bind, pure, Except.pure]
    rw [he] at h
    cases h
    exact ⟨la, lb, off, rfl, rfl, rfl, by simp only [subDirs, strDirs, directives_append, List.append_assoc]⟩
  all_goals simp [FnCtx.inst, FnCtx.setReg, ha, hb, hd, bind, Except.bind] at h

/-- **The code of an `if`'s `br .eq`**: the compare-and-branch's block,
then the `b` to the `else` label. -/
theorem term_br_inv {k : Nat} {a b : Scc.IR.Operand} {t f : Scc.IR.Label} {c2 : List Item}
    (h : cx.term k (.br .eq a b t f) = .ok c2) :
    ∃ la lb T Fl, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧
      cx.blockLabel t = .ok T ∧ cx.blockLabel f = .ok Fl ∧ directives c2 = brDirs la lb T ++ jmpDirs Fl := by
  cases ha : cx.getOp .X9 a <;> cases hb : cx.getOp .X10 b <;> cases hT : cx.blockLabel t <;>
    cases hF : cx.blockLabel f
  case ok.ok.ok.ok la lb T Fl =>
    have he : cx.term k (.br .eq a b t f) = .ok (la ++ lb ++ [cmpReg .W64 .X9 .X10, jcc .EQ T, jmp Fl]) := by
      simp only [FnCtx.term, ha, hb, hT, hF, condCode, bind, Except.bind, pure, Except.pure]
    rw [he] at h
    cases h
    refine ⟨la, lb, T, Fl, rfl, rfl, rfl, rfl, ?_⟩
    rw [show ([cmpReg .W64 .X9 .X10, jcc .EQ T, jmp Fl] : List Item) =
      [cmpReg .W64 .X9 .X10, jcc .EQ T] ++ [jmp Fl] from rfl]
    simp only [brDirs, jmpDirs, directives_append, List.append_assoc]
  all_goals simp [FnCtx.term, ha, hb, hT, hF, bind, Except.bind] at h

/-- **The code of a one-word `ret`**: the word's load, the frame's exit,
the return site's label `x{k}` (P5), `ret`. -/
theorem term_ret_inv {k : Nat} {w : Scc.IR.Operand} {c2 : List Item} (h : cx.term k (.ret [w]) = .ok c2) :
    ∃ lw, cx.getOp .X0 w = .ok lw ∧ c2 = lw ++ cx.leave ++ [lbl (cx.local s!"x{k}"), ret] := by
  cases hv : cx.getOp .X0 w with
  | error e =>
    have ha : argRegs = .X0 :: argRegs.tail := rfl
    simp only [FnCtx.term] at h
    rw [ha] at h
    simp [hv, Scc.IR.maxRets, bind, Except.bind, pure, Except.pure, forIn, ForIn.forIn] at h
  | ok lw =>
    rw [term_ret1 k hv] at h
    cases h
    exact ⟨lw, rfl, rfl⟩

end Emit

/-! ## The constructs' blocks -/

/-- **A construct's block** of a call-free `Accepted1` body: a checked
`+`'s, a saturating `-`'s or an `if`'s compare-and-branch (operand loads),
a store, a `b`, or a `ret`'s. -/
def Kind1 (cx : FnCtx) (blk : List Directive) : Prop :=
  (∃ a b la lb, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧
    (blk = addDirs cx la lb ∨ blk = subDirs la lb ∨ ∃ T, blk = brDirs la lb T)) ∨
  (∃ d off, cx.slotOff d = .ok off ∧ blk = strDirs off) ∨
  (∃ F, blk = jmpDirs F) ∨
  (∃ w lw, cx.getOp .X0 w = .ok lw ∧ blk = directives (lw ++ cx.leave ++ [ret]))

theorem movDs_ins (d : XReg) : ∀ L, (movDs d L).all isIns = true
  | [] => by simp [movDs, movzD, isIns]
  | p :: rest => by simp [movDs, movzD, movkD, isIns, List.all_map, Function.comp_def]

section Kinds

variable {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095)

include hf h1 in
/-- An operand's load is instructions only. -/
theorem getOp_ins {t : XReg} {a : Scc.IR.Operand} {l : List Item} (ha : cx.getOp t a = .ok l) :
    (directives l).all isIns = true := by
  rcases getOp_cases hf h1 ha with ⟨r, off, -, -, hl⟩ | ⟨v, -, rfl⟩
  · rw [hl]; simp [RW.dir, AI.toDir, isIns]
  · rw [directives_movImm]; exact movDs_ins _ _

include hf h1 in
/-- **A construct's block is instructions only.** -/
theorem kind1_ins {blk : List Directive} (hk : Kind1 cx blk) : blk.all isIns = true := by
  rcases hk with ⟨a, b, la, lb, ha, hb, h | h | ⟨T, h⟩⟩ | ⟨d, off, -, rfl⟩ | ⟨F, rfl⟩ | ⟨w, lw, hg, rfl⟩
  all_goals try subst h
  · simp only [addDirs, directives_append, directives_addChecked, List.all_append, getOp_ins hf h1 ha,
      getOp_ins hf h1 hb, Bool.true_and]
    simp [isIns]
  · simp only [subDirs, directives_append, directives_subSat, List.all_append, getOp_ins hf h1 ha,
      getOp_ins hf h1 hb, Bool.true_and]
    simp [isIns]
  · simp only [brDirs, directives_append, directives_cmpJcc, List.all_append, getOp_ins hf h1 ha,
      getOp_ins hf h1 hb, Bool.true_and]
    simp [isIns]
  · simp [strDirs, directives, ins, isIns]
  · simp [jmpDirs, directives, jmp, ins, isIns]
  · rw [directives_leave hf h1, List.all_append, getOp_ins hf h1 hg]
    simp [epi, RW.dir, AI.toDir, isIns]

variable (h16 : cx.frame % 16 = 0)
include hf h1 h16

/-- **A construct's block is covered** at the frame's offsets. -/
theorem kind1_ok {blk : List Directive} (hk : Kind1 cx blk) :
    okBlk (-(cx.frame : Int)) 0 (oF cx) blk = true := by
  rcases hk with ⟨a, b, la, lb, ha, hb, h | h | ⟨T, h⟩⟩ | ⟨d, off, hd, rfl⟩ | ⟨F, rfl⟩ | ⟨w, lw, hg, rfl⟩
  all_goals try subst h
  · show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [addDirs, directives_append, directives_append, List.append_assoc, okBlk_getOp hf h1 h16 ha,
      okBlk_getOp hf h1 h16 hb]
    exact okBlk_addChecked _
  · show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [subDirs, directives_append, directives_append, List.append_assoc, okBlk_getOp hf h1 h16 ha,
      okBlk_getOp hf h1 h16 hb]
    exact okBlk_subSat
  · show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [brDirs, directives_append, directives_append, List.append_assoc, okBlk_getOp hf h1 h16 ha,
      okBlk_getOp hf h1 h16 hb]
    exact okBlk_cmpJcc _
  · obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf hd
    have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
    have hds : strDirs off = [(.X9, Int64.ofInt off)].map fun q => spStr q.1 q.2 := rfl
    rw [hds]
    refine okBlk_spStrs (by simp [oF]; omega) fun q hq => ?_
    simp only [List.mem_singleton] at hq
    subst hq
    simp only [oF, ho, offOk, decide_eq_true_eq]
    omega
  · exact okBlk_jmp F
  · have hge := frame_ge16 hf
    have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
    show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [directives_leave hf h1, okBlk_getOp hf h1 h16 hg]
    have := okBlk_epi (F := Int64.ofInt cx.frame) (by rw [hF64]; omega) (by rw [hF64]; omega)
    rwa [hF64] at this

end Kinds

/-- Every directive of a covered block is classified. -/
theorem classify_of_okBlk {lo hi : Int} :
    ∀ {o : SO} {blk : List Directive}, okBlk lo hi o blk = true → ∀ d ∈ blk, (classify d).isSome = true
  | _, [], _, d, hd => by cases hd
  | o, x :: xs, h, d, hd => by
    unfold okBlk at h
    split at h
    · rename_i a ha
      simp only [Bool.and_eq_true] at h
      rcases List.mem_cons.mp hd with rfl | hd
      · rw [ha]; rfl
      · exact classify_of_okBlk h.2 d hd
    · cases h

/-! ## The code predicate -/

/-- **A block placed at `pc`**: `k` instructions after a label `l`
(`blockAt`). -/
def At1 (prog : List Directive) (lab : Label → Int64) (pc : Int64) (blk : List Directive) : Prop :=
  ∃ l k, lab l + Int64.ofNat (4 * k) = pc ∧ blockAt prog l k blk = true

/-- **The code predicate of a call-free `Accepted1` body**: `blk` is a
construct's block (`Kind1`) placed at `pc` (`At1`), whole or in two pieces,
the second right after the first (a `ret`'s load and teardown, then `ret`
after its return site's label, P5), passing the phase check at `pc` with no
dead target and the return address `ra`. -/
def Cd1 (prog : List Directive) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (cx : FnCtx)
    (ra : Int64) (pc : Int64) (blk : List Directive) : Prop :=
  Kind1 cx blk ∧
    (At1 prog lab pc blk ∨ ∃ b1 b2, blk = b1 ++ b2 ∧ At1 prog lab pc b1 ∧
      At1 prog lab (pc + Int64.ofNat (4 * b1.length)) b2) ∧
    blkPh okPc ph (fun _ => false) lab pc ra blk = true

theorem pc_app (a : Int64) (xs ys : List Directive) :
    a + Int64.ofNat (4 * (xs ++ ys).length) = a + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * ys.length) := by
  rw [List.length_append, ofNat4_add]

/-- **A code segment's concatenation**: `a` at `pc`, `b` right after it. -/
theorem CodeAt.append {st} {pc : Int64} {a b : List Directive} (ha : Spike.Lib.A64.CodeAt st pc a)
    (hb : Spike.Lib.A64.CodeAt st (pc + Int64.ofNat (4 * a.length)) b) : Spike.Lib.A64.CodeAt st pc (a ++ b) := by
  intro j d hd
  rw [List.getElem?_append] at hd
  split at hd
  · exact ha j d hd
  · have := hb (j - a.length) d hd
    rwa [Int64.add_assoc, ← Int64.ofNat_add, ← Nat.mul_add, Nat.add_sub_cancel' (by omega)] at this

theorem CdOf.append {exe : _root_.Executable} {endPc pc : Int64} {a b : List Directive} (ha : CdOf exe endPc pc a)
    (hb : CdOf exe endPc (pc + Int64.ofNat (4 * a.length)) b) : CdOf exe endPc pc (a ++ b) :=
  fun s he hn => CodeAt.append (ha s he hn) (hb s he hn)

/-! ## Runs -/

theorem noLabel_of_isIns {c : List Directive} (h : c.all isIns = true) : ∀ d ∈ c, ∀ l', d ≠ .label l' := by
  intro d hd l' he
  subst he
  have := List.all_eq_true.mp h _ hd
  simp [isIns] at this

/-- **A label-free prefix joins the current run.** -/
theorem runsAux_shift : ∀ (l : Label) (acc c S : List Directive), (∀ d ∈ c, ∀ l', d ≠ .label l') →
    runsAux l acc (c ++ S) = runsAux l (c.reverse ++ acc) S
  | l, acc, [], S, _ => by simp
  | l, acc, d :: c, S, h => by
    have hd : ∀ l', d ≠ .label l' := h d (List.mem_cons_self ..)
    have ih := runsAux_shift l (d :: acc) c S fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    cases d with
    | label l'' => exact absurd rfl (hd l'')
    | instr i => simp only [List.cons_append, runsAux]; rw [ih]; simp
    | byteArray a => simp only [List.cons_append, runsAux]; rw [ih]; simp

/-- **The current run** of `runsAux l acc S`: `acc` (reversed) and the
directives of `S` up to its first label. -/
theorem runsAux_run0 : ∀ (l : Label) (acc S : List Directive), ∃ P, (l, acc.reverse ++ P) ∈ runsAux l acc S
  | l, acc, [] => ⟨[], by simp [runsAux]⟩
  | l, acc, .label _ :: _ => ⟨[], by simp [runsAux]⟩
  | l, acc, .instr i :: S => by
    obtain ⟨P, hP⟩ := runsAux_run0 l (.instr i :: acc) S
    exact ⟨.instr i :: P, by simpa [runsAux] using hP⟩
  | l, acc, .byteArray a :: S => by
    obtain ⟨P, hP⟩ := runsAux_run0 l (.byteArray a :: acc) S
    exact ⟨.byteArray a :: P, by simpa [runsAux] using hP⟩

/-- **The runs past instructions `A`** after `xs`: those from `xs ++ A`. -/
theorem runs_shift (l : Label) (xs : List Directive) {A : List Directive} (hA : A.all isIns = true)
    (Y : List Directive) : runsAux l xs.reverse (A ++ Y) = runsAux l (xs ++ A).reverse Y := by
  rw [runsAux_shift _ _ _ _ (noLabel_of_isIns hA), List.reverse_append]

/-- **The runs across a label `X`** after the instructions `A`: the current
run ends at `xs ++ A`, the rest are those from `X`. -/
theorem runs_label (l : Label) (xs : List Directive) {A : List Directive} (hA : A.all isIns = true)
    (X : Label) (Y : List Directive) :
    runsAux l xs.reverse (A ++ .label X :: Y) = (l, xs ++ A) :: runsAux X [] Y := by
  rw [runsAux_label _ _ _ _ _ (noLabel_of_isIns hA), List.reverse_reverse]

/-- **`runPhB` reads the labels at the run's targets only.** -/
theorem runPhB_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64} {pc ra : Int64}
    {blk : List Directive} (h : ∀ L ∈ blkLabs blk, lab L = lab' L) :
    runPhB okPc ph lab pc ra blk = runPhB okPc ph lab' pc ra blk := by
  unfold runPhB
  congr 1
  funext k
  congr 1
  cases hk : blk[k]? with
  | none => rfl
  | some d =>
    simp only
    cases hc : classify d with
    | none => rfl
    | some a =>
      simp only
      rw [aiTgts_congr fun L hL => h L ?_]
      exact List.mem_filterMap.mpr ⟨d, List.mem_of_getElem? hk, by rw [hc]; exact hL⟩

/-- **The phase check of two blocks, one right after the other**, the
second's pc in the first's phase. -/
theorem blkPh_append1 {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {dd : Nat → Bool}
    {pc ra : Int64} {a b : List Directive}
    (ha : blkPh okPc ph dd lab pc ra a = true)
    (hb : blkPh okPc ph dd lab (pc + Int64.ofNat (4 * a.length)) ra b = true)
    (he : ph (pc + Int64.ofNat (4 * a.length)).toBitVec.toNat = ph pc.toBitVec.toNat) :
    blkPh okPc ph dd lab pc ra (a ++ b) = true := by
  unfold blkPh at ha hb ⊢
  rw [List.all_eq_true] at ha hb ⊢
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [List.length_append] at hk'
  rcases Nat.lt_or_ge k a.length with h' | h'
  · rw [List.getElem?_append_left h']
    exact ha k (List.mem_range.mpr h')
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h'
    have := hb j (List.mem_range.mpr (by omega))
    rw [he] at this
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, ofNat4_add]
    exact this

section Code

variable {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
  {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {ra : Int64}

/-- **A covered piece `ys` of a segment is placed and passes its phase
check**: after the instructions `xs` in the code after `l` (`segIn`), every
run from there passing `runPhB`; its pc in the phase of `l`'s if it is not
empty. -/
theorem piece_of {l : Label} {xs ys zs : List Directive} (hseg : segIn prog l (xs ++ ys ++ zs) = true)
    (hx : xs.all isIns = true) (hy : ys.all isIns = true) (hc : ∀ d ∈ ys, (classify d).isSome = true)
    (hph : ∀ r ∈ runsAux l xs.reverse (ys ++ zs), runPhB okPc ph lab (lab r.1) ra r.2 = true) :
    At1 prog lab (lab l + Int64.ofNat (4 * xs.length)) ys ∧
      blkPh okPc ph (fun _ => false) lab (lab l + Int64.ofNat (4 * xs.length)) ra ys = true ∧
      (ys ≠ [] → ph (lab l + Int64.ofNat (4 * xs.length)).toBitVec.toNat = ph (lab l).toBitVec.toNat) := by
  obtain ⟨P, hP⟩ := runsAux_run0 l (ys.reverse ++ xs.reverse) zs
  rw [← runsAux_shift _ _ _ _ (noLabel_of_isIns hy)] at hP
  have hr := hph _ hP
  simp only [List.reverse_append, List.reverse_reverse] at hr
  have hr' : runPhB okPc ph lab (lab l) ra (xs ++ ys ++ P) = true := by simpa only [List.append_assoc] using hr
  refine ⟨⟨l, xs.length, rfl, blockAt_of_segIn hseg hx hy⟩, blkPh_of_runPhB hr' hc, fun hne => ?_⟩
  have hlen : xs.length < (xs ++ ys ++ P).length := by
    have : ys.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
    simp only [List.length_append]; omega
  exact (runPhB_get hr' hlen).2.1

include hf h1 h16 in
/-- **A construct's piece `ys` of a segment is at `Cd1`** (`piece_of`). -/
theorem cd1_piece {l : Label} {xs ys zs : List Directive} (hseg : segIn prog l (xs ++ ys ++ zs) = true)
    (hx : xs.all isIns = true) (hk : Kind1 cx ys)
    (hph : ∀ r ∈ runsAux l xs.reverse (ys ++ zs), runPhB okPc ph lab (lab r.1) ra r.2 = true) :
    Cd1 prog okPc ph lab cx ra (lab l + Int64.ofNat (4 * xs.length)) ys := by
  obtain ⟨hat, hb, -⟩ := piece_of hseg hx (kind1_ins hf h1 hk) (classify_of_okBlk (kind1_ok hf h1 h16 hk)) hph
  exact ⟨hk, .inl hat, hb⟩

/-- **An inner label of a segment**: the segment after it, and its address
(`hgap`). -/
theorem label_at (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    {l : Label} {P R : List Directive} {L : Label}
    (hseg : segIn prog l (P ++ .label L :: R) = true) (hP : P.all isIns = true) :
    segIn prog L R = true ∧ lab L = lab l + Int64.ofNat (4 * P.length) :=
  ⟨segIn_label hseg, hgap _ _ _ (labelGap_of_segIn hseg hP)⟩

include hf h1 h16 in
/-- **A block's code after its label gives `Code1`**: the block's
instructions' code `c1` (`instsItems`, numbered from `k`) and its
terminator's `c2` (numbered `kt`), after the instructions `xs` and before
`zs` in the code after `l` (`segIn`), every run from there passing `runPhB`
at `lab` in the phase of `ra`, and `lab` following the labels' gaps
(`hgap`). Each fresh label `x{k}` (after a checked `+`, before a `ret`, P5)
starts a new run. -/
theorem code1_of_seg (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    {tm : Scc.IR.Term} (htm : TermOK1 tm) :
    ∀ (is : List Scc.IR.Inst) (k kt : Nat) (l : Label) (c1 c2 : List Item) (xs zs : List Directive),
      (∀ i ∈ is, InstOK1 i) → instsItems cx k is = .ok c1 → cx.term kt tm = .ok c2 →
      segIn prog l (xs ++ directives (c1 ++ c2) ++ zs) = true → xs.all isIns = true →
      (∀ r ∈ runsAux l xs.reverse (directives (c1 ++ c2) ++ zs), runPhB okPc ph lab (lab r.1) ra r.2 = true) →
      (∀ r ∈ runsAux l xs.reverse (directives (c1 ++ c2) ++ zs),
        ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) →
      Code1 cx (Cd1 prog okPc ph lab cx ra) (lab l + Int64.ofNat (4 * xs.length)) is tm
  | [], k, kt, l, c1, c2, xs, zs, _, hi, ht, hseg, hx, hph, hrl => by
    simp only [instsItems] at hi
    cases hi
    simp only [List.nil_append] at hseg hph hrl
    match tm, htm, ht with
    | .ret [w], _, ht =>
      obtain ⟨lw, hg, rfl⟩ := term_ret_inv ht
      have hkR : Kind1 cx (directives (lw ++ cx.leave ++ [ret])) := .inr (.inr (.inr ⟨w, lw, hg, rfl⟩))
      generalize hX : cx.local s!"x{kt}" = X at hseg hph hrl
      generalize hT : directives (lw ++ cx.leave) = T
      generalize hR : directives [ret] = R
      have hTR : directives (lw ++ cx.leave ++ [ret]) = T ++ R := by rw [← hT, ← hR, directives_append]
      have hD : directives (lw ++ cx.leave ++ [lbl X, ret]) = T ++ .label X :: R := by
        rw [← hT, ← hR, show lw ++ cx.leave ++ [lbl X, ret] = (lw ++ cx.leave) ++ [lbl X] ++ [ret] by simp,
          directives_append, directives_append, List.append_assoc]; rfl
      rw [hD] at hseg hph hrl
      rw [hTR] at hkR
      have hins := kind1_ins hf h1 hkR
      have hcl := classify_of_okBlk (kind1_ok hf h1 h16 hkR)
      rw [List.all_append, Bool.and_eq_true] at hins
      -- the load and teardown
      have hseg1 : segIn prog l (xs ++ T ++ (.label X :: R ++ zs)) = true := by
        simpa only [List.append_assoc, List.cons_append] using hseg
      have hph1 : ∀ r ∈ runsAux l xs.reverse (T ++ (.label X :: R ++ zs)), runPhB okPc ph lab (lab r.1) ra r.2 = true :=
        by simpa only [List.append_assoc, List.cons_append] using hph
      obtain ⟨hat1, hb1, hp1⟩ := piece_of hseg1 hx hins.1 (fun d hd => hcl d (List.mem_append_left _ hd)) hph1
      have hxT : (xs ++ T).all isIns = true := by rw [List.all_append, hx, hins.1]; rfl
      obtain ⟨hseg2, hsp⟩ := label_at hgap (P := xs ++ T) (R := R ++ zs) (by simpa only [List.append_assoc,
        List.cons_append] using hseg) hxT
      rw [List.cons_append, runs_label l xs hins.1 X (R ++ zs)] at hph1
      have hrl1 := hrl
      rw [List.append_assoc, List.cons_append, runs_label l xs hins.1 X (R ++ zs)] at hrl1
      -- `ret`, after the return site's label
      obtain ⟨hat2, hb2, -⟩ := piece_of (l := X) (xs := []) (by simpa using hseg2) rfl hins.2
        (fun d hd => hcl d (List.mem_append_right _ hd)) (fun r hr => hph1 r (List.mem_cons_of_mem _ hr))
      rw [List.length_nil, ofNat4_zero] at hat2 hb2
      have hphX : ph (lab X).toBitVec.toNat = ph ra.toBitVec.toNat := by
        obtain ⟨P, hP⟩ := runsAux_run0 X [] (R ++ zs)
        exact hrl1 _ (List.mem_cons_of_mem _ hP)
      have hphl : ph (lab l).toBitVec.toNat = ph ra.toBitVec.toNat := hrl1 _ (List.mem_cons_self ..)
      have hsp' : lab X = lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * T.length) := by
        rw [hsp, pc_app]
      refine ⟨lw, hg, ?_⟩
      rw [hTR]
      refine ⟨hkR, .inr ⟨T, R, rfl, hat1, by rw [← hsp']; exact hat2⟩, ?_⟩
      refine blkPh_append1 hb1 (by rw [← hsp']; exact hb2) ?_
      by_cases hTe : T = []
      · subst hTe; simp only [List.length_nil, ofNat4_zero]
      · rw [← hsp', hphX, hp1 hTe, hphl]
    | .br .eq a b t f, _, ht =>
      obtain ⟨la, lb, T, Fl, ha, hb, hT, hF, hds⟩ := term_br_inv ht
      rw [hds] at hseg hph
      have hkb : Kind1 cx (brDirs la lb T) := .inl ⟨a, b, la, lb, ha, hb, .inr (.inr ⟨T, rfl⟩)⟩
      have hkj : Kind1 cx (jmpDirs Fl) := .inr (.inr (.inl ⟨Fl, rfl⟩))
      have hbi := kind1_ins hf h1 hkb
      refine ⟨la, lb, T, Fl, ha, hb, hT, hF, ?_, ?_⟩
      · exact cd1_piece hf h1 h16 (by simpa only [List.append_assoc] using hseg) hx hkb
          (by simpa only [List.append_assoc] using hph)
      · have hxb : (xs ++ brDirs la lb T).all isIns = true := by rw [List.all_append, hx, hbi]; rfl
        have := cd1_piece hf h1 h16 (xs := xs ++ brDirs la lb T) (by simpa only [List.append_assoc] using hseg)
          hxb hkj (by rw [← runs_shift l xs hbi]; simpa only [List.append_assoc] using hph)
        rwa [pc_app] at this
  | i :: is, k, kt, l, c1, c2, xs, zs, hs, hi, ht, hseg, hx, hph, hrl => by
    have hs' := List.forall_mem_cons.mp hs
    simp only [instsItems] at hi
    cases hci : cx.inst k i with
    | error e => simp [hci, bind, Except.bind] at hi
    | ok ci =>
      cases hc1 : instsItems cx (k + 1) is with
      | error e => simp [hci, hc1, bind, Except.bind] at hi
      | ok c1' =>
        simp [hci, hc1, bind, Except.bind, pure, Except.pure] at hi
        subst hi
        have hdc : directives (ci ++ c1' ++ c2) = directives ci ++ directives (c1' ++ c2) := by
          rw [List.append_assoc, directives_append]
        rw [hdc] at hseg hph hrl
        generalize hDd : directives (c1' ++ c2) = D at hseg hph hrl
        cases i with
        | addChk d a b =>
          obtain ⟨la, lb, off, ha, hb, hd, hds⟩ := inst_addChk_inv hf h1 hci
          rw [hds] at hseg hph hrl
          generalize hX : cx.local s!"x{k}" = X at hseg hph hrl
          have hkA : Kind1 cx (addDirs cx la lb) := .inl ⟨a, b, la, lb, ha, hb, .inl rfl⟩
          have hkS : Kind1 cx (strDirs off) := .inr (.inl ⟨d, off, hd, rfl⟩)
          have hAi := kind1_ins hf h1 hkA
          have hSi := kind1_ins hf h1 hkS
          -- the checked add
          have hseg1 : segIn prog l (xs ++ addDirs cx la lb ++ (.label X :: (strDirs off ++ D ++ zs))) = true := by
            simpa only [List.append_assoc, List.cons_append] using hseg
          have hph1 : ∀ r ∈ runsAux l xs.reverse (addDirs cx la lb ++ .label X :: (strDirs off ++ D ++ zs)),
              runPhB okPc ph lab (lab r.1) ra r.2 = true := by
            simpa only [List.append_assoc, List.cons_append] using hph
          have hrl1 : ∀ r ∈ runsAux l xs.reverse (addDirs cx la lb ++ .label X :: (strDirs off ++ D ++ zs)),
              ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
            simpa only [List.append_assoc, List.cons_append] using hrl
          have c1 := cd1_piece hf h1 h16 hseg1 hx hkA hph1
          have hxA : (xs ++ addDirs cx la lb).all isIns = true := by rw [List.all_append, hx, hAi]; rfl
          obtain ⟨hseg2, hsp⟩ := label_at hgap (P := xs ++ addDirs cx la lb) (R := strDirs off ++ D ++ zs)
            (by simpa only [List.append_assoc] using hseg1) hxA
          rw [runs_label l xs hAi X] at hph1 hrl1
          have hsp' : lab X = lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * (addDirs cx la lb).length) := by
            rw [hsp, pc_app]
          have hphX : ∀ r ∈ runsAux X [] (strDirs off ++ D ++ zs), runPhB okPc ph lab (lab r.1) ra r.2 = true :=
            fun r hr => hph1 r (List.mem_cons_of_mem _ hr)
          have hrlX : ∀ r ∈ runsAux X [] (strDirs off ++ D ++ zs), ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat :=
            fun r hr => hrl1 r (List.mem_cons_of_mem _ hr)
          -- the store, after the fall-through's label
          have c2' := cd1_piece hf h1 h16 (l := X) (xs := []) (zs := D ++ zs)
            (by simpa only [List.append_assoc, List.nil_append] using hseg2) rfl hkS
            (by simpa only [List.append_assoc, List.reverse_nil] using hphX)
          rw [List.length_nil, ofNat4_zero, hsp'] at c2'
          -- the rest of the block
          have c3 := code1_of_seg hgap htm is (k + 1) kt X c1' c2 (strDirs off) zs hs'.2 hc1 ht
            (by rw [hDd]; simpa only [List.append_assoc] using hseg2) hSi
            (by
              rw [hDd, ← List.append_nil (strDirs off).reverse, ← runsAux_shift _ _ _ _ (noLabel_of_isIns hSi)]
              simpa only [List.append_assoc] using hphX)
            (by
              rw [hDd, ← List.append_nil (strDirs off).reverse, ← runsAux_shift _ _ _ _ (noLabel_of_isIns hSi)]
              simpa only [List.append_assoc] using hrlX)
          rw [hsp', show (strDirs off).length = 1 from rfl, show Int64.ofNat (4 * 1) = 4 from rfl] at c3
          exact ⟨la, lb, off, ha, hb, hd, c1, c2', c3⟩
        | subSat d a b =>
          obtain ⟨la, lb, off, ha, hb, hd, hds⟩ := inst_subSat_inv hf h1 hci
          rw [hds] at hseg hph hrl
          have hkA : Kind1 cx (subDirs la lb) := .inl ⟨a, b, la, lb, ha, hb, .inr (.inl rfl)⟩
          have hkS : Kind1 cx (strDirs off) := .inr (.inl ⟨d, off, hd, rfl⟩)
          have hAi := kind1_ins hf h1 hkA
          have hSi := kind1_ins hf h1 hkS
          have hxA : (xs ++ subDirs la lb).all isIns = true := by rw [List.all_append, hx, hAi]; rfl
          have hxAS : (xs ++ subDirs la lb ++ strDirs off).all isIns = true := by
            rw [List.all_append, hxA, hSi]; rfl
          have c1 := cd1_piece hf h1 h16 (zs := strDirs off ++ D ++ zs)
            (by simpa only [List.append_assoc] using hseg) hx hkA (by simpa only [List.append_assoc] using hph)
          have c2' := cd1_piece hf h1 h16 (xs := xs ++ subDirs la lb) (zs := D ++ zs)
            (by simpa only [List.append_assoc] using hseg) hxA hkS
            (by rw [← runs_shift l xs hAi]; simpa only [List.append_assoc] using hph)
          rw [pc_app] at c2'
          have c3 := code1_of_seg hgap htm is (k + 1) kt l c1' c2 (xs ++ subDirs la lb ++ strDirs off) zs hs'.2 hc1
            ht (by rw [hDd]; simpa only [List.append_assoc] using hseg) hxAS
            (by rw [hDd, ← runs_shift _ _ hSi, ← runs_shift l xs hAi]; simpa only [List.append_assoc] using hph)
            (by rw [hDd, ← runs_shift _ _ hSi, ← runs_shift l xs hAi]; simpa only [List.append_assoc] using hrl)
          rw [pc_app, pc_app, show (strDirs off).length = 1 from rfl, show Int64.ofNat (4 * 1) = 4 from rfl] at c3
          exact ⟨la, lb, off, ha, hb, hd, c1, c2', c3⟩
        | _ => exact (hs'.1).elim

end Code

/-! ## From the placement checks -/

section Place

variable {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
  {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {ra : Int64}
  {lo : Nat}

include hf h1 h16 in
/-- **A placed block's code gives `Code1`** at its label: its code after
the label (`segIn`) and its runs' phase facts at the code labels
(`labC`), every label read resolving, which `lab` agrees with (`hlab`),
every run's label in the phase of `ra`, and `lab` following the labels'
gaps (`hgap`). -/
theorem code1_block (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    {b : Scc.IR.Block} (hs : BlkOK1 b.insts b.term) {k : Nat} {l : Label} {code : List Item}
    (hc : blockItems cx k b = .ok code) (hseg : segIn prog l (directives code) = true)
    (hph : ∀ r ∈ runs l (directives code),
      runPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) ra r = true ∧
        ph (labC lo prog r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    Code1 cx (Cd1 prog okPc ph lab cx ra) (lab l) b.insts b.term := by
  cases hi : instsItems cx k b.insts with
  | error e => simp [blockItems, hi, bind, Except.bind] at hc
  | ok c1 =>
    cases ht : cx.term (k + b.insts.length) b.term with
    | error e => simp [blockItems, hi, ht, bind, Except.bind] at hc
    | ok c2 =>
      simp [blockItems, hi, ht, bind, Except.bind, pure, Except.pure] at hc
      subst hc
      have := code1_of_seg (okPc := okPc) (ph := ph) (ra := ra) hf h1 h16 hgap hs.2 b.insts k _ l c1 c2 [] []
        hs.1 hi ht (by simpa using hseg) rfl
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
      simpa [ofNat4_zero] using this

include hf h1 h16 in
/-- **The later blocks' code** (`BlocksCode`) at `Cd1`, from the
function's `blocksOk` and `blocksPh` (the blocks `bs` after `pre`). -/
theorem blocksCode1 (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    {pre bs : List Scc.IR.Block} (hok : blocksOk prog cx 0 (pre ++ bs) = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0 (pre ++ bs) = true)
    (hs : ∀ b ∈ bs, BlkOK1 b.insts b.term) :
    BlocksCode cx (Cd1 prog okPc ph lab cx ra) lab bs := by
  intro b hb
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hb
  have e : pre ++ (s ++ b :: t) = (pre ++ s) ++ b :: t := by simp only [List.append_assoc]
  rw [e] at hok hph
  obtain ⟨l, code, hl, hc, hseg⟩ := blocksOk_block hok
  obtain ⟨l', code', hl', hc', hr⟩ := blocksPh_blockPh hph
  rw [hl] at hl'; cases hl'
  rw [hc] at hc'; cases hc'
  exact ⟨l, hl, code1_block hf h1 h16 hgap hlab (hs b hb) hc hseg hr⟩

include hf h1 h16 in
/-- **The entry block's code** (`Code1` at the entry's label) from the
function's `blocksOk` and `blocksPh`. -/
theorem entryCode1 (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    {b : Scc.IR.Block} {bs : List Scc.IR.Block} {entry : Label} (hent : cx.blockLabel b.label = .ok entry)
    (hok : blocksOk prog cx 0 (b :: bs) = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0 (b :: bs) = true)
    (hs : BlkOK1 b.insts b.term) :
    Code1 cx (Cd1 prog okPc ph lab cx ra) (lab entry) b.insts b.term := by
  obtain ⟨l, code, hl, hc, hseg⟩ := blocksOk_block (pre := []) hok
  obtain ⟨l', code', hl', hc', hr⟩ := blocksPh_blockPh (pre := []) hph
  rw [hl] at hl'; cases hl'
  rw [hc] at hc'; cases hc'
  rw [hent] at hl; cases hl
  exact code1_block hf h1 h16 hgap hlab hs hc hseg hr

end Place

end Spike.Lib.LowerA64
