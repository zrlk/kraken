/-
**The slot order of an `Accepted1` code block's function** (ISA-neutral):
`Spike/Lib/SlotOrder.lean`'s `slots_eq_nodup` for `func1` of a body's
closed form `lowerC` (`Scc/Lower/InvC1.lean`), with or without the depth
counter.

- `Shape D U T`: per-instruction definitions `D`, uses `U` and terminator
  uses `T` that agree with `StackMap.instDefs`/`instUses`/`termUses` on the
  instructions and terminators `lowerC` emits (`shape_stackMap`;
  `instUsesR`, `shape_instUsesR`: the uses with `slotAddr`'s source, so that
  x64 `instRegs i = instDefs i ++ instUsesR i`);
- `resChunks`, `lowerC_chunks`: the chunks of a closed form; every use is in
  the environment's registers or defined before, and the definitions are
  pairwise distinct names `fresh` gave between the start and final counters
  (`Fresh`);
- `param_ne_regName`: a parameter register `x.0` is no `fresh` name;
- `usesDefined_func1`, `nodup_func1`: `slots_eq_nodup`'s hypotheses for
  `func1 name (params1R d) r`;
- `slots_func1`: the function's register slots are its parameter registers,
  then its definitions in order.
-/
import Spike.Lib.SlotOrder
import Scc.Lower.InvC1

namespace Spike.Lib.SlotOrder

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower
open Scc.Lower.Inv
open Scc.IR.StackMap (opRegs instDefs instUses termUses)

/-- **Definitions and uses of the instructions `lowerC` emits** (and of its
terminators), as `StackMap.instDefs`, `instUses`, `termUses`. -/
structure Shape (D U : Inst → List Reg) (T : Term → List Reg) : Prop where
  addChk : ∀ d p q, D (.addChk d p q) = [d] ∧ U (.addChk d p q) = opRegs p ++ opRegs q
  subSat : ∀ d p q, D (.subSat d p q) = [d] ∧ U (.subSat d p q) = opRegs p ++ opRegs q
  bin : ∀ op d p q, D (.bin op d p q) = [d] ∧ U (.bin op d p q) = opRegs p ++ opRegs q
  getTp : ∀ d, D (.getTp d) = [d] ∧ U (.getTp d) = []
  load : ∀ o w d a, D (.load o w d a) = [d] ∧ U (.load o w d a) = [a.base]
  store : ∀ o w a v, D (.store o w a v) = [] ∧ U (.store o w a v) = a.base :: opRegs v
  call : ∀ ds g args, D (.call ds g args) = ds ∧ U (.call ds g args) = args.flatMap opRegs
  ret : ∀ vs, T (.ret vs) = vs.flatMap opRegs
  br : ∀ c a b t f, T (.br c a b t f) = opRegs a ++ opRegs b
  unreachable : T .unreachable = []

theorem shape_stackMap : Shape instDefs instUses termUses where
  addChk _ _ _ := ⟨rfl, rfl⟩
  subSat _ _ _ := ⟨rfl, rfl⟩
  bin _ _ _ _ := ⟨rfl, rfl⟩
  getTp _ := ⟨rfl, rfl⟩
  load _ _ _ _ := ⟨rfl, rfl⟩
  store _ _ _ _ := ⟨rfl, rfl⟩
  call _ _ _ := ⟨rfl, rfl⟩
  ret _ := rfl
  br _ _ _ _ _ := rfl
  unreachable := rfl

/-- `StackMap.instUses`, with `slotAddr d s` using `s` (as the emitters'
per-instruction register lists, which list `s` after `d`). -/
def instUsesR (i : Inst) : List Reg :=
  match i with
  | .slotAddr _ s => [s]
  | i => instUses i

theorem shape_instUsesR : Shape instDefs instUsesR termUses where
  addChk _ _ _ := ⟨rfl, rfl⟩
  subSat _ _ _ := ⟨rfl, rfl⟩
  bin _ _ _ _ := ⟨rfl, rfl⟩
  getTp _ := ⟨rfl, rfl⟩
  load _ _ _ _ := ⟨rfl, rfl⟩
  store _ _ _ _ := ⟨rfl, rfl⟩
  call _ _ _ := ⟨rfl, rfl⟩
  ret _ := rfl
  br _ _ _ _ _ := rfl
  unreachable := rfl

/-! ## Chunks -/

/-- A block's chunks (as `funcChunks`). -/
def blockChunks (D U : Inst → List Reg) (T : Term → List Reg) (b : Block) : List Chunk :=
  b.insts.map (fun i => (D i, U i)) ++ [([], T b.term)]

/-- **The chunks of a closed form**: the open block's instructions and
terminator, then its blocks'. -/
def resChunks (D U : Inst → List Reg) (T : Term → List Reg) (r : Res1) : List Chunk :=
  r.insts.map (fun i => (D i, U i)) ++ [([], T r.term)] ++ r.blocks.flatMap (blockChunks D U T)

/-- The definitions of some chunks, in order. -/
def defsC (cs : List Chunk) : List Reg := cs.flatMap (·.1)

/-- **Fresh definitions**: pairwise distinct names `fresh` gave at counters
from `n` to below `m`. -/
def Fresh (n m : Nat) (ds : List Reg) : Prop :=
  n ≤ m ∧ ds.Nodup ∧ ∀ x ∈ ds, ∃ z k, n ≤ k ∧ k < m ∧ x = regName z k

theorem ud_append : ∀ (a b : List Chunk) (acc : List Reg),
    UsesDefined acc (a ++ b) ↔ UsesDefined acc a ∧ UsesDefined (acc ++ defsC a) b
  | [], b, acc => by simp [UsesDefined, defsC]
  | c :: a, b, acc => by
    simp only [List.cons_append, UsesDefined, ud_append a b, defsC, List.flatMap_cons, List.append_assoc]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩

theorem ud_mono : ∀ (cs : List Chunk) {acc acc' : List Reg}, (∀ x ∈ acc, x ∈ acc') →
    UsesDefined acc cs → UsesDefined acc' cs
  | [], _, _, _, _ => trivial
  | c :: cs, _, acc', h, ⟨hc, hcs⟩ => ⟨fun r hr => (hc r hr).imp_left (h r), ud_mono cs (acc' := acc' ++ c.1)
      (fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · simp [h x hx]
        · simp [hx]) hcs⟩

theorem fresh_append {n m p : Nat} {a b : List Reg} (ha : Fresh n m a) (hb : Fresh m p b) :
    Fresh n p (a ++ b) := by
  obtain ⟨hnm, ha1, ha2⟩ := ha
  obtain ⟨hmp, hb1, hb2⟩ := hb
  refine ⟨by omega, List.nodup_append.mpr ⟨ha1, hb1, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨z, k, -, hk, rfl⟩ := ha2 x hx
    obtain ⟨z', k', hk', -, rfl⟩ := hb2 y hy
    exact regName_ne (show k ≠ k' by omega) hxy
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨z, k, h1, h2, rfl⟩ := ha2 x hx
      exact ⟨z, k, h1, by omega, rfl⟩
    · obtain ⟨z, k, h1, h2, rfl⟩ := hb2 x hx
      exact ⟨z, k, by omega, h2, rfl⟩

theorem fresh_mono {n m n' m' : Nat} {ds : List Reg} (h : Fresh n m ds) (h1 : n' ≤ n) (h2 : m ≤ m') :
    Fresh n' m' ds := by
  obtain ⟨hnm, hd, hx⟩ := h
  refine ⟨by omega, hd, fun x hx' => ?_⟩
  obtain ⟨z, k, hk1, hk2, rfl⟩ := hx x hx'
  exact ⟨z, k, by omega, by omega, rfl⟩

theorem fresh_nil {n m : Nat} (h : n ≤ m) : Fresh n m [] := ⟨h, List.nodup_nil, by simp⟩

/-- One definition `d = regName z n` with uses in `acc`, before chunks
whose uses are defined and whose definitions are fresh from `n + 1`. -/
theorem step1 {acc : List Reg} {z : String} {n m : Nat} {u : List Reg} {cs : List Chunk}
    (hu : ∀ x ∈ u, x ∈ acc) (h : UsesDefined (acc ++ [regName z n]) cs ∧ Fresh (n + 1) m (defsC cs)) :
    UsesDefined acc (([regName z n], u) :: cs) ∧ Fresh n m (defsC (([regName z n], u) :: cs)) := by
  refine ⟨⟨fun x hx => .inl (hu x hx), h.1⟩, ?_⟩
  have h1 : Fresh n (n + 1) [regName z n] := ⟨by omega, by simp, by simp; exact ⟨z, n, by omega, by omega, rfl⟩⟩
  have := fresh_append h1 h.2
  simpa [defsC] using this

theorem resChunks_cons (D U : Inst → List Reg) (T : Term → List Reg) (r' : Res1) (i : Inst) (nx : Nat)
    (m : List Reg) (ms : List (Node × Point)) (h : Point) :
    resChunks D U T ⟨i :: r'.insts, r'.term, r'.blocks, nx, m, ms, h⟩ = (D i, U i) :: resChunks D U T r' := by
  simp [resChunks]

theorem resChunks_marked (D U : Inst → List Reg) (T : Term → List Reg) (r : Res1) (m : List Reg) :
    resChunks D U T { r with marked := m } = resChunks D U T r := rfl

theorem resChunks_call {D U : Inst → List Reg} {T : Term → List Reg} (hS : Shape D U T) (fr n : Nat)
    (g : String) (w : Operand) (lc : Label) (r : Res1) (nx : Nat) (m : List Reg) (ms : List (Node × Point))
    (h : Point) :
    resChunks D U T
        { insts := depthPre n, term := depthTerm fr n,
          blocks := deepBlock n :: ⟨lc, callPost g w n ++ r.insts, r.term⟩ :: r.blocks, next := nx,
          marked := m, marks := ms, here := h } =
    [([regName "tp" (n + 1)], []), ([regName "depth" (n + 2)], [regName "tp" (n + 1)]),
     ([regName "depth" (n + 3)], [regName "depth" (n + 2)]), ([], [regName "depth" (n + 3)]),
     ([], []), ([], []), ([], [regName "tp" (n + 1), regName "depth" (n + 3)]),
     ([regName "r" n], opRegs w), ([regName "tp" (n + 6)], []),
     ([], [regName "tp" (n + 6), regName "depth" (n + 2)])] ++ resChunks D U T r := by
  simp [resChunks, blockChunks, depthPre, depthTerm, deepBlock, callPost, hS.getTp, hS.load, hS.bin, hS.br,
    hS.call, hS.store, hS.unreachable, imm, opRegs]

theorem resChunks_if (D U : Inst → List Reg) (T : Term → List Reg) (hS : Shape D U T) (p q : Operand)
    (ly ln : Label) (ry rn : Res1) (nx : Nat) (m : List Reg) (ms : List (Node × Point)) (h : Point) :
    resChunks D U T
        { insts := [], term := .br .eq p q ly ln,
          blocks := ⟨ly, ry.insts, ry.term⟩ :: (ry.blocks ++ ⟨ln, rn.insts, rn.term⟩ :: rn.blocks), next := nx,
          marked := m, marks := ms, here := h } =
    [([], opRegs p ++ opRegs q)] ++ resChunks D U T ry ++ resChunks D U T rn := by
  simp [resChunks, blockChunks, hS.br]

/-! ## The closed form's chunks -/

/-- **The chunks of `lowerC`'s closed form**: from an environment whose
registers are in `acc`, every use is in `acc` or defined before
(`UsesDefined`), and the definitions are fresh names from the start counter
to the final one (`Fresh`). -/
theorem lowerC_chunks {D U : Inst → List Reg} {T : Term → List Reg} (hS : Shape D U T) (cx : Scc.Lower.Ctx) :
    ∀ (e : Expr) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res1) (acc : List Reg),
      lowerC cx env n l k e = some r → EnvIn env acc →
      UsesDefined acc (resChunks D U T r) ∧ Fresh n r.next (defsC (resChunks D U T r)) := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r acc hr he
    cases op with
    | atom a =>
      simp only [lowerC] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        match ws, hr with
        | [w], hr =>
        cases hr' : lowerC cx ((x, t, [w]) :: env) n l k e with
        | none => cases ht : scalar1 t <;> simp [ht, hr'] at hr
        | some r' =>
          cases ht : scalar1 t <;> simp [ht, hr'] at hr
          subst hr
          rw [resChunks_marked]
          exact ih _ _ _ _ _ _ hr' (envIn_cons he x t (atomV_regs ha he))
    | add a b | sub a b =>
      simp only [lowerC] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        match ws, hr with
        | [p], hr =>
        cases hb : atomV env b with
        | none => simp [hb] at hr
        | some u =>
          obtain ⟨t', us⟩ := u
          rw [hb] at hr
          match us, hr with
          | [q], hr =>
          cases hr' : lowerC cx ((x, .int, [.reg (regName x n)]) :: env) (n + 1) l (k + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp [hr'] at hr
            subst hr
            rw [resChunks_cons D U T r']
            first
              | rw [(hS.addChk _ _ _).1, (hS.addChk _ _ _).2]
              | rw [(hS.subSat _ _ _).1, (hS.subSat _ _ _).2]
            refine step1 (fun y hy => ?_) (ih _ _ _ _ _ _ hr'
              (envIn_cons (envIn_mono he (fun y hy => by simp [hy])) x .int (by simp [opRegs])))
            rcases List.mem_append.mp hy with hy | hy
            · exact atomV_regs ha he y (by simpa using hy)
            · exact atomV_regs hb he y (by simpa using hy)
    | call g is a ts =>
      simp only [lowerC] at hr
      cases hx : (cx.externs.find? (·.1 == g)).isNone with
      | false => simp [hx] at hr
      | true =>
      cases hd : cx.prog.find? (·.name == g) with
      | none => simp [hx, hd] at hr
      | some dg =>
      cases hrt : dg.retTy == .int with
      | false => simp only [beq_eq_false_iff_ne] at hrt; simp [hx, hd] at hr; exact absurd hr.1 hrt
      | true =>
      cases ha : atomV env a with
      | none => simp [hx, hd, ha] at hr
      | some v =>
      obtain ⟨t, ws⟩ := v
      simp only [hx, hd, hrt, ha, ite_true, Option.bind_eq_bind, Option.bind_some] at hr
      match ws, hr with
      | [w], hr =>
      have hw : ∀ y ∈ opRegs w, y ∈ acc := fun y hy => atomV_regs ha he y (by simpa using hy)
      cases hf : cx.frames with
      | none =>
        cases hr' : lowerC cx ((x, .int, [.reg (regName "r" n)]) :: env) (n + 1) l (k + 1) e with
        | none => simp [hf, hr'] at hr
        | some r' =>
          simp [hf, hr'] at hr
          subst hr
          rw [resChunks_cons D U T r', (hS.call _ _ _).1, (hS.call _ _ _).2]
          have hw' : ∀ y ∈ [w].flatMap opRegs, y ∈ acc := by simpa using hw
          exact step1 hw' (ih _ _ _ _ _ _ hr'
            (envIn_cons (envIn_mono he (fun y hy => by simp [hy])) x .int (by simp [opRegs])))
      | some fr =>
        cases hr' : lowerC cx ((x, .int, [.reg (regName "r" n)]) :: env) (n + 7) (labName "call" (n + 5)) 4 e
          with
        | none => simp [hf, hr'] at hr
        | some r' =>
          simp [hf, hr'] at hr
          subst hr
          rw [resChunks_call hS, ud_append]
          have hih := ih _ _ _ _ _ (acc ++ [regName "tp" (n + 1), regName "depth" (n + 2),
            regName "depth" (n + 3), regName "r" n, regName "tp" (n + 6)]) hr'
            (envIn_cons (envIn_mono he (fun y hy => by simp [hy])) x .int (by simp [opRegs]))
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := callRegs_ne n
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · simp only [UsesDefined]
            refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp,
              fun y hy => .inl (by simp [hw y hy]), by simp, by simp, trivial⟩
          · refine ud_mono _ (fun y hy => ?_) hih.1
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hy
            simp only [defsC, List.mem_append, List.flatMap_cons, List.flatMap_nil, List.mem_cons,
              List.mem_nil_iff]
            rcases hy with hy | hy | hy | hy | hy | hy <;> simp [hy]
          · rw [defsC, List.flatMap_append]
            refine fresh_append (m := n + 7) ⟨by omega, ?_, ?_⟩ hih.2
            · simp only [List.flatMap_cons, List.flatMap_nil, List.nil_append, List.cons_append,
                List.append_nil]
              exact List.nodup_cons.mpr ⟨by simp [h7, h8, Ne.symm h1, h5],
                List.nodup_cons.mpr ⟨by simp [h6, Ne.symm h3, Ne.symm h9],
                List.nodup_cons.mpr ⟨by simp [Ne.symm h4, Ne.symm h10], List.nodup_cons.mpr ⟨by simp [h2],
                by simp⟩⟩⟩⟩
            · intro y hy
              simp at hy
              rcases hy with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, by omega, by omega, rfl⟩
    | _ => simp [lowerC] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n l k r acc hr he
    simp only [lowerC] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v =>
      obtain ⟨t, ws⟩ := v
      rw [ha] at hr
      match ws, hr with
      | [p], hr =>
      cases hb : atomV env b with
      | none => simp [hb] at hr
      | some u =>
        obtain ⟨t', us⟩ := u
        rw [hb] at hr
        match us, hr with
        | [q], hr =>
        cases hy : lowerC cx env (n + 2) (labName "then" n) 0 yes with
        | none => simp [hy] at hr
        | some ry =>
          cases hn : lowerC cx env ry.next (labName "else" (n + 1)) 0 no with
          | none => simp [hy, hn] at hr
          | some rn =>
            simp [hy, hn] at hr
            subst hr
            rw [resChunks_if D U T hS]
            have hiy := ihy _ _ _ _ _ acc hy he
            have hin := ihn _ _ _ _ _ acc hn he
            refine ⟨?_, ?_⟩
            · rw [ud_append, ud_append]
              refine ⟨⟨⟨fun y hy' => .inl ?_, trivial⟩, ud_mono _ (fun y hy' => by simp [hy']) hiy.1⟩,
                ud_mono _ (fun y hy' => by simp [hy']) hin.1⟩
              rcases List.mem_append.mp hy' with hy' | hy'
              · exact atomV_regs ha he y (by simpa using hy')
              · exact atomV_regs hb he y (by simpa using hy')
            · have := fresh_mono (n' := n) (fresh_append hiy.2 hin.2) (by omega) (Nat.le_refl _)
              simpa [defsC] using this
  | ret a =>
    intro env n l k r acc hr he
    simp only [lowerC] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v =>
      obtain ⟨t, ws⟩ := v
      simp [ha] at hr
      subst hr
      refine ⟨⟨fun y hy => .inl ?_, trivial⟩, ?_⟩
      · exact atomV_regs ha he y (by simpa [hS.ret] using hy)
      · simpa [resChunks, defsC] using fresh_nil (n := n) (Nat.le_refl _)
  | _ => intro env n l k r acc hr; simp [lowerC] at hr

/-! ## Parameters -/

private theorem dropDigits {c : Char} (hc : c.isDigit = false) :
    ∀ (l rest : List Char), (∀ x ∈ l, x.isDigit = true) →
      (l ++ c :: rest).dropWhile Char.isDigit = c :: rest
  | [], rest, _ => by simp [hc]
  | x :: l, rest, h => by
    simp only [List.cons_append, List.dropWhile_cons, h x (by simp), ite_true]
    exact dropDigits hc l rest (fun y hy => h y (by simp [hy]))

private theorem sepHead {c : Char} (hc : c.isDigit = false) (a : List Char) (k : Nat) :
    ((a ++ [c] ++ Nat.toDigits 10 k).reverse.dropWhile Char.isDigit).head? = some c := by
  have : (a ++ [c] ++ Nat.toDigits 10 k).reverse = (Nat.toDigits 10 k).reverse ++ c :: a.reverse := by simp
  rw [this, dropDigits hc]
  · rfl
  · intro x hx
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) (List.mem_reverse.mp hx)

/-- **A parameter register is no `fresh` name**: the last non-digit of
`x.0` is `.`, that of `regName z k` is `%`. -/
theorem param_ne_regName (a z : String) (k : Nat) : s!"{a}.{0}" ≠ regName z k := by
  intro he
  have hl := congrArg (fun s => (s.toList.reverse.dropWhile Char.isDigit).head?) he
  simp only [regName, String.toList_append, Nat.toString_eq_repr, Nat.toList_repr] at hl
  have h1 : (toString ".").toList = ['.'] := rfl
  have h2 : (toString "%").toList = ['%'] := rfl
  rw [h1, h2, sepHead (by decide), sepHead (by decide)] at hl
  simp at hl

theorem envIn_env1 (d : Decl) : EnvIn (env1 d) (params1R d) := by
  intro v hv y hy
  simp only [env1, List.mem_singleton] at hv
  subst hv
  simp only [params1R] at hy ⊢
  split at hy <;> simp_all [opRegs]

/-! ## The function of an `Accepted1` code block -/

theorem funcChunks_func1 (D U : Inst → List Reg) (T : Term → List Reg) (name : Sym) (ps : List Reg)
    (r : Res1) : funcChunks D U T (func1 name ps r) = resChunks D U T r := by
  simp [funcChunks, func1, resChunks]
  rfl

/-- **Every use in `func1` of a closed form is a parameter or defined
before.** -/
theorem usesDefined_func1 {D U : Inst → List Reg} {T : Term → List Reg} (hS : Shape D U T) (cx : Scc.Lower.Ctx)
    {d : Decl} {r : Res1} (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r) (name : Sym) :
    UsesDefined (func1 name (params1R d) r).params (funcChunks D U T (func1 name (params1R d) r)) := by
  rw [funcChunks_func1]
  exact (lowerC_chunks hS cx _ _ _ _ _ _ _ hr (envIn_env1 d)).1

/-- **The definitions of `func1` of a closed form are fresh names** from
counter 0 to the final one. -/
theorem fresh_func1 {D U : Inst → List Reg} {T : Term → List Reg} (hS : Shape D U T) (cx : Scc.Lower.Ctx)
    {d : Decl} {r : Res1} (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r) (name : Sym) :
    Fresh 0 r.next (defsOf D (func1 name (params1R d) r)) := by
  rw [← funcChunks_defs D U T, funcChunks_func1]
  exact (lowerC_chunks hS cx _ _ _ _ _ _ _ hr (envIn_env1 d)).2

/-- **The parameters and definitions of `func1` of a closed form are
pairwise distinct.** -/
theorem nodup_func1 {D U : Inst → List Reg} {T : Term → List Reg} (hS : Shape D U T) (cx : Scc.Lower.Ctx)
    {d : Decl} {r : Res1} (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r) (name : Sym) :
    ((func1 name (params1R d) r).params ++ defsOf D (func1 name (params1R d) r)).Nodup := by
  obtain ⟨-, hn, hx⟩ := fresh_func1 hS cx hr name
  refine List.nodup_append.mpr ⟨?_, hn, ?_⟩
  · simp only [func1, params1R]; split <;> simp
  · intro y hy z hz hyz
    obtain ⟨w, k, -, -, rfl⟩ := hx z hz
    simp only [func1, params1R] at hy
    split at hy
    · simp only [List.mem_singleton] at hy
      subst hy
      exact param_ne_regName _ _ _ hyz
    · simp at hy

/-- **The slot order of an `Accepted1` code block's function**: for a
per-instruction register list `R` listing definitions `D i` before uses
`U i` (`Shape D U T`), the first occurrences of `func1`'s registers are its
parameter registers, then its definitions in order. -/
theorem slots_func1 {D U : Inst → List Reg} {T : Term → List Reg} (hS : Shape D U T) (R : Inst → List Reg)
    (hR : ∀ i, R i = D i ++ U i) (cx : Scc.Lower.Ctx) {d : Decl} {r : Res1}
    (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r) (name : Sym) :
    ((func1 name (params1R d) r).params ++ (func1 name (params1R d) r).blocks.flatMap fun b =>
        b.insts.flatMap R ++ T b.term).eraseDups =
      (func1 name (params1R d) r).params ++ defsOf D (func1 name (params1R d) r) :=
  slots_eq_nodup D U T R hR _ (usesDefined_func1 hS cx hr name) (nodup_func1 hS cx hr name)

end Spike.Lib.SlotOrder
