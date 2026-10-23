/-
**A lowered `Accepted0` body is one segment** (AArch64), symbolic in the
body, the frame, the IR registers' slots and the pc.

`body_seg`: by induction on the lowering's closed form (`lower0`), from the
node at the body's start (the source at the body, the lowering's
environment placed in the frame's cells: `bodyN`) to the return's exit
(`retN`) or the overflow abort label (`abortN`), given the code of each
emitted block at consecutive pcs (`BodyCode`), the environment's registers
fresh for the lowering's destinations (`Fresh`) and the blocks' states in
`W` (`hW`), and the lowering's environment at each point of its walk with
its immediates in the abort's table `i` (`hImm`, `ImmIn`).

- `let x = a`: no code, the node invariant moves past it (`NJ.atom`);
- `let x = a + b`: `add_seg` (to the pending store or the abort label),
  then `store_seg`;
- `ret a`: `ret_seg`.
-/
import Spike.Lib.LowerA64.Node

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (lower0 atomV Res scalar1)

set_option linter.unusedSimpArgs false

/-! ## The lowering's environment (ISA-neutral) -/

/-- **Every free variable of a lowered body is bound** in the lowering's
environment. -/
theorem lower0_fv :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (r : Res), lower0 env n e = some r →
      ∀ y ∈ Scc.Sem.exprFv e, (env.find? (·.1 == y)).isSome := by
  have hat : ∀ (env : Scc.Lower.Env) (a : At) v, atomV env a = some v →
      ∀ y ∈ Scc.Sem.atVars a, (env.find? (·.1 == y)).isSome := by
    intro env a v ha y hy
    cases a with
    | var x =>
      simp only [Scc.Sem.atVars, List.mem_singleton] at hy
      subst hy
      simp only [atomV, Option.map_eq_some_iff] at ha
      obtain ⟨b, hb, -⟩ := ha
      simp [hb]
    | _ => simp [Scc.Sem.atVars] at hy
  have hcons : ∀ (env : Scc.Lower.Env) (b : String × Ty × List Scc.IR.Operand) (y : String), b.1 ≠ y →
      ((b :: env).find? (·.1 == y)).isSome → (env.find? (·.1 == y)).isSome := by
    intro env b y hne h
    have : (b.1 == y) = false := by simp [hne]
    simpa [List.find?_cons, this] using h
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n r hr y hy
    cases op with
    | atom a =>
      simp only [lower0] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        match ws, hr with
        | [w], hr =>
        cases hr' : lower0 ((x, t, [w]) :: env) n e with
        | none => simp [hr'] at hr
        | some r' =>
          simp only [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hy
          rcases hy with hy | ⟨hy, hne⟩
          · exact hat env a _ ha y hy
          · exact hcons env (x, t, [w]) y (fun e => hne e.symm) (ih _ n r' hr' y hy)
    | add a b =>
      simp only [lower0] at hr
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
          cases hr' : lower0 ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp only [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hy
            rcases hy with (hy | hy) | ⟨hy, hne⟩
            · exact hat env a _ ha y hy
            · exact hat env b _ hb y hy
            · exact hcons env _ y (fun e => hne e.symm) (ih _ (n + 1) r' hr' y hy)
    | _ => simp [lower0] at hr
  | ret a =>
    intro env n r hr y hy
    simp only [lower0] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v => exact hat env a v ha y hy
  | _ => intro env n r hr; simp [lower0] at hr

/-- **The environment's registers are fresh from counter `n` on**: none is
a destination `regName y k`, `k ≥ n`, of the rest of the lowering. -/
def Fresh (env : Scc.Lower.Env) (n : Nat) : Prop :=
  ∀ v ∈ env, ∀ o ∈ v.2.2, ∀ r, o = .reg r → ∀ y k, n ≤ k → r ≠ Scc.Lower.Inv.regName y k

theorem Fresh.atom {env : Scc.Lower.Env} {n : Nat} (h : Fresh env n) {a : At} {t : Ty} {ws : List Scc.IR.Operand}
    (ha : atomV env a = some (t, ws)) (x : String) : Fresh ((x, t, ws) :: env) n := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · cases a with
    | var z =>
      simp only [atomV, Option.map_eq_some_iff] at ha
      obtain ⟨⟨z', u, vs⟩, hb, he⟩ := ha
      cases he
      exact h (z', u, vs) (List.mem_of_find?_eq_some hb)
    | lit m =>
      simp only [atomV] at ha
      split at ha
      · cases ha
      · cases ha
        intro o ho r hr
        simp only [List.mem_singleton] at ho
        subst ho; cases hr
    | unit =>
      simp only [atomV, Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨-, rfl⟩ := ha
      intro o ho; cases ho
  · exact h v hv

theorem Fresh.add {env : Scc.Lower.Env} {n : Nat} (h : Fresh env n) (x : String) :
    Fresh ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · intro o ho r hr y k hk
    simp only [List.mem_singleton] at ho
    subst ho; cases hr
    exact Scc.Lower.Inv.regName_ne (by omega)
  · intro o ho r hr y k hk
    exact h v hv o ho r hr y k (by omega)

/-- **The symbolic environment's placed registers are off `regName x n`.** -/
theorem Fresh.ofEnv {env : Scc.Lower.Env} {n : Nat} (h : Fresh env n) (x : String) :
    ∀ q ∈ ofEnv env, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ Scc.Lower.Inv.regName x n := by
  intro q hq pl hpl o ho r hr
  simp only [Spike.Lib.LowerNode.ofEnv, List.mem_map] at hq
  obtain ⟨b, hb, rfl⟩ := hq
  simp only [List.mem_map] at hpl
  obtain ⟨o', ho', rfl⟩ := hpl
  simp only [WordPl.opds, List.mem_singleton] at ho
  subst ho
  exact h b hb _ ho' r hr x n (Nat.le_refl n)

theorem ofEnv_cons (env : Scc.Lower.Env) (x : String) (t : Ty) (ws : List Scc.IR.Operand) :
    ofEnv ((x, t, ws) :: env) = (x, t, ws.map .one) :: ofEnv env := rfl

theorem isSome_lookupS_ofEnv {env : Scc.Lower.Env} {y : String} (h : (env.find? (·.1 == y)).isSome) :
    (lookupS (ofEnv env) y).isSome := by
  rw [lookupS_ofEnv]; simpa using h

/-! ## The body's code (AArch64) -/

/-- **The code of a lowered body at `pc`**: each checked `+`'s block, then
its store, then the rest; the `ret`'s load and epilogue last. `Cd pc blk`:
`blk` is the code at `pc`. -/
def BodyCode (cx : FnCtx) (Cd : Int64 → List Directive → Prop) : Int64 → List Scc.IR.Inst → List Scc.IR.Operand → Prop
  | pc, [], [w] => ∃ l, cx.getOp .X0 w = .ok l ∧ Cd pc (directives (l ++ cx.leave ++ [ret]))
  | pc, .addChk d a b :: is, ws => ∃ la lb off, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧
      cx.slotOff d = .ok off ∧
      Cd pc (directives (la ++ lb ++ addChecked .X9 .X9 .X10 (cx.local "abort_overflow"))) ∧
      Cd (pc + Int64.ofNat (4 * (directives (la ++ lb ++ addChecked .X9 .X9 .X10 (cx.local "abort_overflow"))).length))
        (directives [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 off, none⟩⟩)]) ∧
      BodyCode cx Cd
        (pc + Int64.ofNat (4 * (directives (la ++ lb ++ addChecked .X9 .X9 .X10 (cx.local "abort_overflow"))).length)
          + 4)
        is ws
  | _, _, _ => False

/-- The code predicate of an executable. -/
def CdOf (exe : _root_.Executable) (endPc : Int64) (pc : Int64) (blk : List Directive) : Prop :=
  ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc blk

section Body

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isaLSE2} {K : State → State → Prop}

/-- **A lowered `Accepted0` body is one segment**: from the node at the
body (the lowering's environment `env` placed in the frame) to the return's
exit or the overflow abort label. The code predicate `Cd` gives the code
(`hCd`); the blocks' states are inside `W` at the body's nodes (`hW`) and
pending stores (`hWp`) at the blocks `Cd` holds of; at each point of the
lowering's walk (`lowerEnvs`) its environment's immediates are `i`'s
(`hImm`) and the point satisfies `T`, which the overflow abort label's
invariant records. -/
theorem body_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {c0 : Ctl} {Cd : Int64 → List Directive → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hW : ∀ pc t s blk, Cd pc blk → BlkW W K exe endPc R F (bodyN p lbl cx fp ra c0 pc t s) blk)
    (hWp : ∀ pc t s k blk, Cd pc blk → BlkW W K exe endPc R F (pendN p lbl cx fp ra c0 pc t s k) blk)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (r : Res) (pc : Int64), lower0 env n e = some r →
      Fresh env n → BodyCode cx Cd pc r.insts r.ret →
      (∀ q ∈ lowerEnvs env n e, ImmIn i (ofEnv q.2.1) q.1 ∧ T q.1) →
      SegW W K p lbl ms (At exe endPc R F (bodyN p lbl cx fp ra c0 pc e (ofEnv env)))
        (fun s c => At exe endPc R F (retN p lbl fp ra c0) s c ∨
          At exe endPc R F (abortN i T p lbl cx (_root_.Executable.labels exe).label fp ra c0) s c) := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n r pc hr hfr hcode hImm
    cases op with
    | atom a =>
      have hr0 := hr
      simp only [lower0] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        match ws, hr with
        | [w], hr =>
        cases hr' : lower0 ((x, t, [w]) :: env) n e with
        | none => simp [hr'] at hr
        | some r' =>
          cases ht : scalar1 t <;> simp [ht, hr'] at hr
          subst hr
          have ih' := ih _ n r' pc hr' (hfr.atom ha x) hcode (immIn_tail_atom ha hImm)
          refine ih'.mono_pre fun s c ⟨he, hn, hd, hpc, σ, hA, hFm, hJ, hfj, hc0⟩ =>
            ⟨he, hn, hd, hpc, σ, hA, hFm, ?_, hfj, hc0⟩
          rw [ofEnv_cons]
          exact hJ.atom (sevalAt_ofEnv ha)
    | add a b =>
      have hr0 := hr
      simp only [lower0] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨ta, ws⟩ := v
        rw [ha] at hr
        match ws, hr with
        | [pa], hr =>
        cases hb : atomV env b with
        | none => simp [hb] at hr
        | some u =>
          obtain ⟨tb, us⟩ := u
          rw [hb] at hr
          match us, hr with
          | [pb], hr =>
          cases hr' : lower0 ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp [hr'] at hr
            subst hr
            obtain ⟨la, lb, off, hla, hlb, hd, hc1, hc2, hrest⟩ := hcode
            have hfv := lower0_fv (.let_ x (.add a b) e) env n _ hr0
            have hadd := add_seg (p := p) (lbl := lbl) (ms := ms) (fp := fp) (ra := ra) (c0 := c0) (x := x) (e := e)
              hf h1 h16 hla hlb hd (hCd _ _ hc1) hF hR hal hlo hhi
              (sevalAt_ofEnv ha) (sevalAt_ofEnv hb) (hfr.ofEnv x)
              (fun y hy => isSome_lookupS_ofEnv (hfv y hy)) (immIn_head hImm).1 (immIn_head hImm).2 (hW _ _ _ _ hc1)
            have hst := store_seg (p := p) (lbl := lbl) (ms := ms) (fp := fp) (ra := ra) (c0 := c0)
              (t := e) (s := (x, .int, [.one (.reg (Scc.Lower.Inv.regName x n))]) :: ofEnv env)
              hf h1 h16 hd (hCd _ _ hc2) hF hR hal hlo hhi (hWp _ _ _ _ _ hc2)
            have ih' := ih _ (n + 1) r' _ hr' (hfr.add x) hrest (immIn_tail_add hImm)
            rw [ofEnv_cons] at ih'
            refine (SegW.seq_left (hadd.mono_post fun s c h => h.elim (fun ⟨_, h⟩ => .inl h)
              fun ⟨_, h⟩ => .inr h) (hst.seq ih')).mono_post fun s c h => ?_
            rcases h with h | h
            · exact h
            · exact .inr h
    | _ => simp [lower0] at hr
  | ret a =>
    intro env n r pc hr hfr hcode _
    simp only [lower0] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v =>
      obtain ⟨t, ws⟩ := v
      simp [ha] at hr
      subst hr
      match ws, hcode with
      | [w], ⟨l, hl, hc⟩ =>
        exact (ret_seg (p := p) (lbl := lbl) (ms := ms) (fp := fp) (ra := ra) (c0 := c0) hf h1 h16 hl
          (hCd _ _ hc) hF hR hal hlo hhi (sevalAt_ofEnv ha) (hW _ _ _ _ hc)).mono_post fun _ _ h => .inl h
  | _ => intro env n r pc hr; simp [lower0] at hr

end Body

end Spike.Lib.LowerA64
