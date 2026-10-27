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
  emitter's code of each, split into the constructs' blocks.
- `Kind1`, `kind1_ins`, `kind1_ok`: a construct's block is instructions
  only and covered at the frame's offsets.
- `code1_of_seg`: a block's code after its label (`segIn`) passing its
  run's phase check gives `Code1` at `Cd1`.
- `code1_block`, `blocksCode1`: from a block's `blocksOk`/`blocksPh` facts.
-/
import Spike.Lib.LowerA64.Body1
import Spike.Lib.LowerA64.MainCode1

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (blockAt isIns)
open Scc.Cert.Code1A64 (blocksOk blockItems instsItems kAfter segIn blockAt_of_segIn blocksOk_block)
open Scc.Cert.Ph1A64 (runs runsAux runPh runPhB blocksPh blocksPh_block blkPh_of_runPhB runsAux_nil)
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
/-- **The code of a checked `+`**: the add's block, then the store's. -/
theorem inst_addChk_inv {k : Nat} {d : Scc.IR.Reg} {a b : Scc.IR.Operand} {ci : List Item}
    (h : cx.inst k (.addChk d a b) = .ok ci) :
    ∃ la lb off, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧ cx.slotOff d = .ok off ∧
      directives ci = addDirs cx la lb ++ strDirs off := by
  cases ha : cx.getOp .X9 a <;> cases hb : cx.getOp .X10 b <;> cases hd : cx.slotOff d
  case ok.ok.ok la lb off =>
    rw [inst_addChk hf (by omega) k ha hb hd] at h
    cases h
    exact ⟨la, lb, off, rfl, rfl, rfl, by simp only [addDirs, strDirs, directives_append, List.append_assoc]⟩
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
`ret`. -/
theorem term_ret_inv {k : Nat} {w : Scc.IR.Operand} {c2 : List Item} (h : cx.term k (.ret [w]) = .ok c2) :
    ∃ lw, cx.getOp .X0 w = .ok lw ∧ c2 = lw ++ cx.leave ++ [ret] := by
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

/-- **The code predicate of a call-free `Accepted1` body**: `blk` is a
construct's block (`Kind1`) at `pc`, `k` instructions after the label `l`
(`blockAt`), passing the phase check at `pc` with no dead target and the
return address `ra`. -/
def Cd1 (prog : List Directive) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (cx : FnCtx)
    (ra : Int64) (pc : Int64) (blk : List Directive) : Prop :=
  Kind1 cx blk ∧ ∃ l k, lab l + Int64.ofNat (4 * k) = pc ∧ blockAt prog l k blk = true ∧
    blkPh okPc ph (fun _ => false) lab pc ra blk = true

theorem pc_app (a : Int64) (xs ys : List Directive) :
    a + Int64.ofNat (4 * (xs ++ ys).length) = a + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * ys.length) := by
  rw [List.length_append, ofNat4_add]

section Code

variable {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
  {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab0 : Label → Int64} {ra : Int64}
  {l : Label}

include hf h1 h16 in
/-- **A construct's block inside a placed run** is at `Cd1`: the run
`xs ++ ys ++ zs` after `l` (`segIn`) passing its phase check at the
check's labels `lab0`, which agree with `lab` on the run's targets. -/
theorem cd1_of {xs ys zs : List Directive} (hseg : segIn prog l (xs ++ ys ++ zs) = true)
    (hx : xs.all isIns = true) (hk : Kind1 cx ys)
    (hph : runPhB okPc ph lab0 (lab l) ra (xs ++ ys ++ zs) = true)
    (hL : ∀ L ∈ blkLabs (xs ++ ys ++ zs), lab0 L = lab L) :
    Cd1 prog okPc ph lab cx ra (lab l + Int64.ofNat (4 * xs.length)) ys := by
  refine ⟨hk, l, xs.length, rfl, blockAt_of_segIn hseg hx (kind1_ins hf h1 hk), ?_⟩
  have hb := blkPh_of_runPhB hph (classify_of_okBlk (kind1_ok hf h1 h16 hk))
  rwa [blkPh_congr fun L hL' => hL L (by
    simp only [blkLabs, List.filterMap_append, List.mem_append] at hL' ⊢; exact .inl (.inr hL'))] at hb

include hf h1 h16 in
/-- **A block's code after its label gives `Code1`**: the block's
instructions' code `c1` (`instsItems`) and its terminator's `c2`, after the
instructions `xs` and before `zs` in the run after `l`. -/
theorem code1_of_seg {tm : Scc.IR.Term} (htm : TermOK1 tm) :
    ∀ (is : List Scc.IR.Inst) (k kt : Nat) (c1 c2 : List Item) (xs zs : List Directive),
      (∀ i ∈ is, InstOK1 i) → instsItems cx k is = .ok c1 → cx.term kt tm = .ok c2 →
      segIn prog l (xs ++ directives (c1 ++ c2) ++ zs) = true → xs.all isIns = true →
      runPhB okPc ph lab0 (lab l) ra (xs ++ directives (c1 ++ c2) ++ zs) = true →
      (∀ L ∈ blkLabs (xs ++ directives (c1 ++ c2) ++ zs), lab0 L = lab L) →
      Code1 cx (Cd1 prog okPc ph lab cx ra) (lab l + Int64.ofNat (4 * xs.length)) is tm
  | [], k, kt, c1, c2, xs, zs, _, hi, ht, hseg, hx, hph, hL => by
    simp only [instsItems] at hi
    cases hi
    simp only [List.nil_append] at hseg hph hL
    match tm, htm, ht with
    | .ret [w], _, ht =>
      obtain ⟨lw, hg, rfl⟩ := term_ret_inv ht
      exact ⟨lw, hg, cd1_of hf h1 h16 hseg hx (.inr (.inr (.inr ⟨w, lw, hg, rfl⟩))) hph hL⟩
    | .br .eq a b t f, _, ht =>
      obtain ⟨la, lb, T, Fl, ha, hb, hT, hF, hds⟩ := term_br_inv ht
      rw [hds] at hseg hph hL
      have e : ∀ zs' : List Directive, xs ++ (brDirs la lb T ++ jmpDirs Fl) ++ zs' =
          xs ++ brDirs la lb T ++ (jmpDirs Fl ++ zs') := by intro; simp only [List.append_assoc]
      have e' : ∀ zs' : List Directive, xs ++ (brDirs la lb T ++ jmpDirs Fl) ++ zs' =
          (xs ++ brDirs la lb T) ++ jmpDirs Fl ++ zs' := by intro; simp only [List.append_assoc]
      have hkb : Kind1 cx (brDirs la lb T) := .inl ⟨a, b, la, lb, ha, hb, .inr (.inr ⟨T, rfl⟩)⟩
      refine ⟨la, lb, T, Fl, ha, hb, hT, hF, ?_, ?_⟩
      · rw [e] at hseg hph hL
        exact cd1_of hf h1 h16 hseg hx hkb hph hL
      · rw [e'] at hseg hph hL
        have := cd1_of hf h1 h16 hseg (by rw [List.all_append, hx, kind1_ins hf h1 hkb]; rfl)
          (.inr (.inr (.inl ⟨Fl, rfl⟩))) hph hL
        rwa [pc_app] at this
  | i :: is, k, kt, c1, c2, xs, zs, hs, hi, ht, hseg, hx, hph, hL => by
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
        -- the construct's block `A` and its store `S`
        have step : ∀ (A : List Directive) (off : Int), Kind1 cx A → (∃ d, cx.slotOff d = .ok off) →
            directives ci = A ++ strDirs off →
            Cd1 prog okPc ph lab cx ra (lab l + Int64.ofNat (4 * xs.length)) A ∧
            Cd1 prog okPc ph lab cx ra (lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * A.length))
              (strDirs off) ∧
            Code1 cx (Cd1 prog okPc ph lab cx ra)
              (lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * A.length) + 4) is tm := by
          intro A off hkA ⟨d, hd⟩ hds
          have hkS : Kind1 cx (strDirs off) := .inr (.inl ⟨d, off, hd, rfl⟩)
          have hdc : directives (ci ++ c1' ++ c2) = A ++ strDirs off ++ directives (c1' ++ c2) := by
            rw [List.append_assoc, directives_append, hds, List.append_assoc]
          rw [hdc] at hseg hph hL
          have hxA : (xs ++ A).all isIns = true := by rw [List.all_append, hx, kind1_ins hf h1 hkA]; rfl
          have hxAS : (xs ++ A ++ strDirs off).all isIns = true := by
            rw [List.all_append, hxA, kind1_ins hf h1 hkS]; rfl
          have e1 : ∀ X : List Directive, xs ++ (A ++ strDirs off ++ directives (c1' ++ c2)) ++ zs = X →
              X = xs ++ A ++ (strDirs off ++ directives (c1' ++ c2) ++ zs) → True := fun _ _ _ => trivial
          clear e1
          refine ⟨?_, ?_, ?_⟩
          · have r : xs ++ (A ++ strDirs off ++ directives (c1' ++ c2)) ++ zs =
                xs ++ A ++ (strDirs off ++ directives (c1' ++ c2) ++ zs) := by simp only [List.append_assoc]
            rw [r] at hseg hph hL
            exact cd1_of hf h1 h16 hseg hx hkA hph hL
          · have r : xs ++ (A ++ strDirs off ++ directives (c1' ++ c2)) ++ zs =
                (xs ++ A) ++ strDirs off ++ (directives (c1' ++ c2) ++ zs) := by simp only [List.append_assoc]
            rw [r] at hseg hph hL
            have := cd1_of hf h1 h16 hseg hxA hkS hph hL
            rwa [pc_app] at this
          · have r : xs ++ (A ++ strDirs off ++ directives (c1' ++ c2)) ++ zs =
                (xs ++ A ++ strDirs off) ++ directives (c1' ++ c2) ++ zs := by simp only [List.append_assoc]
            rw [r] at hseg hph hL
            have := code1_of_seg htm is (k + 1) kt c1' c2 _ zs hs'.2 hc1 ht hseg hxAS hph hL
            rwa [pc_app, pc_app, show (strDirs off).length = 1 from rfl,
              show Int64.ofNat (4 * 1) = 4 from rfl] at this
        cases i with
        | addChk d a b =>
          obtain ⟨la, lb, off, ha, hb, hd, hds⟩ := inst_addChk_inv hf h1 hci
          exact ⟨la, lb, off, ha, hb, hd,
            step _ off (.inl ⟨a, b, la, lb, ha, hb, .inl rfl⟩) ⟨d, hd⟩ hds⟩
        | subSat d a b =>
          obtain ⟨la, lb, off, ha, hb, hd, hds⟩ := inst_subSat_inv hf h1 hci
          exact ⟨la, lb, off, ha, hb, hd,
            step _ off (.inl ⟨a, b, la, lb, ha, hb, .inr (.inl rfl)⟩) ⟨d, hd⟩ hds⟩
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
(`labC`), every label read resolving, which `lab` agrees with (`hlab`). -/
theorem code1_block (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    {b : Scc.IR.Block} (hs : BlkOK1 b.insts b.term) {k : Nat} {l : Label} {code : List Item}
    (hc : blockItems cx k b = .ok code) (hseg : segIn prog l (directives code) = true)
    (hph : ∀ r ∈ runs l (directives code),
      runPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) ra r = true) :
    Code1 cx (Cd1 prog okPc ph lab cx ra) (lab l) b.insts b.term := by
  cases hi : instsItems cx k b.insts with
  | error e => simp [blockItems, hi, bind, Except.bind] at hc
  | ok c1 =>
    cases ht : cx.term (k + b.insts.length) b.term with
    | error e => simp [blockItems, hi, ht, bind, Except.bind] at hc
    | ok c2 =>
      simp [blockItems, hi, ht, bind, Except.bind, pure, Except.pure] at hc
      subst hc
      -- the block's code is instructions only, so one run
      have hins : (directives (c1 ++ c2)).all isIns = true := by
        have hi1 : ∀ (is : List Scc.IR.Inst) (k : Nat) (c1 : List Item), (∀ i ∈ is, InstOK1 i) →
            instsItems cx k is = .ok c1 → (directives c1).all isIns = true := by
          intro is
          induction is with
          | nil => intro k c1 _ h; simp only [instsItems] at h; cases h; rfl
          | cons i is ih =>
            intro k c1 hs h
            have hs' := List.forall_mem_cons.mp hs
            simp only [instsItems] at h
            cases hci : cx.inst k i with
            | error e => simp [hci, bind, Except.bind] at h
            | ok ci =>
              cases hc1 : instsItems cx (k + 1) is with
              | error e => simp [hci, hc1, bind, Except.bind] at h
              | ok c1' =>
                simp [hci, hc1, bind, Except.bind, pure, Except.pure] at h
                subst h
                rw [directives_append, List.all_append, ih (k + 1) c1' hs'.2 hc1, Bool.and_true]
                cases i with
                | addChk d a b =>
                  obtain ⟨la, lb, off, ha, hb, hd, hds⟩ := inst_addChk_inv hf h1 hci
                  rw [hds, List.all_append, kind1_ins hf h1 (.inl ⟨a, b, la, lb, ha, hb, .inl rfl⟩),
                    kind1_ins hf h1 (.inr (.inl ⟨d, off, hd, rfl⟩))]; rfl
                | subSat d a b =>
                  obtain ⟨la, lb, off, ha, hb, hd, hds⟩ := inst_subSat_inv hf h1 hci
                  rw [hds, List.all_append, kind1_ins hf h1 (.inl ⟨a, b, la, lb, ha, hb, .inr (.inl rfl)⟩),
                    kind1_ins hf h1 (.inr (.inl ⟨d, off, hd, rfl⟩))]; rfl
                | _ => exact hs'.1.elim
        rw [directives_append, List.all_append, hi1 _ k c1 hs.1 hi, Bool.true_and]
        obtain ⟨-, htm⟩ := hs
        match b.term, htm, ht with
        | .ret [w], _, ht =>
          obtain ⟨lw, hg, rfl⟩ := term_ret_inv ht
          exact kind1_ins hf h1 (.inr (.inr (.inr ⟨w, lw, hg, rfl⟩)))
        | .br .eq a b t f, _, ht =>
          obtain ⟨la, lb, T, Fl, ha, hb, -, -, hds⟩ := term_br_inv ht
          rw [hds, List.all_append, kind1_ins hf h1 (.inl ⟨a, b, la, lb, ha, hb, .inr (.inr ⟨T, rfl⟩)⟩),
            kind1_ins hf h1 (.inr (.inr (.inl ⟨Fl, rfl⟩)))]; rfl
      have hnl : ∀ d ∈ directives (c1 ++ c2), ∀ l'', d ≠ .label l'' := by
        intro d hd l'' he
        have := List.all_eq_true.mp hins d hd
        subst he
        simp [isIns] at this
      have hr := hph (l, directives (c1 ++ c2)) (by rw [runs, runsAux_nil l [] _ hnl]; simp)
      simp only [runPh, Bool.and_eq_true] at hr
      obtain ⟨⟨hres, hlabs⟩, hrun⟩ := hr
      rw [labC_eq hlab hres] at hrun
      have := code1_of_seg (lab0 := labC lo prog) hf h1 h16 hs.2 b.insts k _ c1 c2 [] []
        hs.1 hi ht (by simpa using hseg) rfl (by simpa using hrun)
        (fun L hL => labC_eq hlab (List.all_eq_true.mp hlabs L (by simpa using hL)))
      simpa [ofNat4_zero] using this

include hf h1 h16 in
/-- **The later blocks' code** (`BlocksCode`) at `Cd1`, from the
function's `blocksOk` and `blocksPh` (the blocks `bs` after `pre`). -/
theorem blocksCode1 (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    {pre bs : List Scc.IR.Block} (hok : blocksOk prog cx 0 (pre ++ bs) = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0 (pre ++ bs) = true)
    (hs : ∀ b ∈ bs, BlkOK1 b.insts b.term) :
    BlocksCode cx (Cd1 prog okPc ph lab cx ra) lab bs := by
  intro b hb
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hb
  have e : pre ++ (s ++ b :: t) = (pre ++ s) ++ b :: t := by simp only [List.append_assoc]
  rw [e] at hok hph
  obtain ⟨l, code, hl, hc, hseg⟩ := blocksOk_block hok
  obtain ⟨l', code', hl', hc', hr⟩ := blocksPh_block hph
  rw [hl] at hl'; cases hl'
  rw [hc] at hc'; cases hc'
  exact ⟨l, hl, code1_block hf h1 h16 hlab (hs b hb) hc hseg hr⟩

include hf h1 h16 in
/-- **The entry block's code** (`Code1` at the entry's label) from the
function's `blocksOk` and `blocksPh`. -/
theorem entryCode1 (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    {b : Scc.IR.Block} {bs : List Scc.IR.Block} {entry : Label} (hent : cx.blockLabel b.label = .ok entry)
    (hok : blocksOk prog cx 0 (b :: bs) = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0 (b :: bs) = true)
    (hs : BlkOK1 b.insts b.term) :
    Code1 cx (Cd1 prog okPc ph lab cx ra) (lab entry) b.insts b.term := by
  obtain ⟨l, code, hl, hc, hseg⟩ := blocksOk_block (pre := []) hok
  obtain ⟨l', code', hl', hc', hr⟩ := blocksPh_block (pre := []) hph
  rw [hl] at hl'; cases hl'
  rw [hc] at hc'; cases hc'
  rw [hent] at hl; cases hl
  exact code1_block hf h1 h16 hlab hs hc hseg hr

end Place

end Spike.Lib.LowerA64
