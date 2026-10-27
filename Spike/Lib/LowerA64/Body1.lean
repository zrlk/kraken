/-
**A lowered call-free `Accepted1` body is one segment** (AArch64),
symbolic in the body, the frame, the IR registers' slots and the pcs; next
to `Spike/Lib/LowerA64/Body.lean`'s one-block `Accepted0` body.

`body1_seg`: by induction on the lowering's closed form (`lower1`), from the
node at the body's start to the return's exit (`retN`) or the overflow abort
label (`abortN`), given the code of the open block at `pc` (`Code1`) and of
each later block at its label (`BlocksCode`), the environment's registers
fresh for the lowering's destinations (`Fresh`), the blocks' states in `W`,
and the lowering's environment at each point of its walk (`lowerEnvs1`) with
its immediates in the abort's table `i`.

- `let x = a`: no code (`NJ.atom`);
- `let x = a + b`: `add_seg`, then `store_seg`;
- `let x = a - b`: `sub_seg`, then `store_seg`;
- `if a = b then yes else no`: `br_seg` to the `then` block's label, or
  falling through to `b else` (`jmp_seg`) and the `else` block's label;
- `ret a`: `ret_seg`.
-/
import Spike.Lib.LowerA64.Body
import Spike.Lib.LowerA64.Node1
import Spike.Lib.LowerEnvImm1
import Spike.Lib.LowerA64.Checks

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (lower1 atomV Res1 scalar1)

set_option linter.unusedSimpArgs false

/-! ## The blocks' code (AArch64) -/

/-- The sub construct's directives: both operands' loads, the saturating
subtraction. -/
def subDirs (la lb : List Item) : List Directive :=
  directives (la ++ lb ++ subSat .X9 .X9 .X10)

/-- **The code of a lowered block at `pc`**: each checked `+`'s or
saturating `-`'s block, then its store, then the rest; then the
terminator's: a `ret`'s load and epilogue, or an `if`'s compare-and-branch to
the `then` block's label followed by `b` to the `else` block's label.
`Cd pc blk`: `blk` is the code at `pc`. -/
def Code1 (cx : FnCtx) (Cd : Int64 → List Directive → Prop) :
    Int64 → List Scc.IR.Inst → Scc.IR.Term → Prop
  | pc, [], .ret [w] => ∃ l, cx.getOp .X0 w = .ok l ∧ Cd pc (directives (l ++ cx.leave ++ [ret]))
  | pc, [], .br .eq a b t f => ∃ la lb T Fl, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧
      cx.blockLabel t = .ok T ∧ cx.blockLabel f = .ok Fl ∧ Cd pc (brDirs la lb T) ∧
      Cd (pc + Int64.ofNat (4 * (brDirs la lb T).length)) (jmpDirs Fl)
  | pc, .addChk d a b :: is, tm => ∃ la lb off, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧
      cx.slotOff d = .ok off ∧
      Cd pc (addDirs cx la lb) ∧
      Cd (pc + Int64.ofNat (4 * (addDirs cx la lb).length)) (strDirs off) ∧
      Code1 cx Cd (pc + Int64.ofNat (4 * (addDirs cx la lb).length) + 4) is tm
  | pc, .subSat d a b :: is, tm => ∃ la lb off, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧
      cx.slotOff d = .ok off ∧
      Cd pc (subDirs la lb) ∧
      Cd (pc + Int64.ofNat (4 * (subDirs la lb).length)) (strDirs off) ∧
      Code1 cx Cd (pc + Int64.ofNat (4 * (subDirs la lb).length) + 4) is tm
  | _, _, _ => False

/-- **The code of later blocks**: each at its assembler label (`lab`), as
`Code1`. -/
def BlocksCode (cx : FnCtx) (Cd : Int64 → List Directive → Prop) (lab : Label → Int64)
    (bs : List Scc.IR.Block) : Prop :=
  ∀ b ∈ bs, ∃ L, cx.blockLabel b.label = .ok L ∧ Code1 cx Cd (lab L) b.insts b.term

section Body

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isaLSE2} {K : State → State → Prop}

/-- **A lowered call-free `Accepted1` body is one segment**: from the node
at the body (the lowering's environment `env` placed in the frame) to the
return's exit or the overflow abort label. The code predicate `Cd` gives the
code (`hCd`): the open block's at `pc` (`Code1`), the later blocks' at their
labels (`BlocksCode`); the blocks' states are inside `W` at the body's nodes
(`hW`) and pending stores (`hWp`); at each point of the lowering's walk
(`lowerEnvs1`) its environment's immediates are `i`'s (`hImm`) and the point
satisfies `T`. -/
theorem body1_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {c0 : Ctl} {Cd : Int64 → List Directive → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hW : ∀ pc t s blk, Cd pc blk → BlkW W K exe endPc R F (bodyN p lbl cx fp ra c0 pc t s) blk)
    (hWp : ∀ pc t s k blk, Cd pc blk → BlkW W K exe endPc R F (pendN p lbl cx fp ra c0 pc t s k) blk)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (r : Res1) (pc : Int64), lower1 env n e = some r →
      Fresh env n → Code1 cx Cd pc r.insts r.term →
      BlocksCode cx Cd (_root_.Executable.labels exe).label r.blocks →
      (∀ q ∈ lowerEnvs1 env n e, ImmIn i (ofEnv q.2.1) q.1 ∧ T q.1) →
      SegW W K p lbl ms (At exe endPc R F (bodyN p lbl cx fp ra c0 pc e (ofEnv env)))
        (fun s c => At exe endPc R F (retN p lbl fp ra c0) s c ∨
          At exe endPc R F (abortN i T p lbl cx (_root_.Executable.labels exe).label fp ra c0) s c) := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n r pc hr hfr hcode hbl hImm
    cases op with
    | atom a =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        match ws, hr with
        | [w], hr =>
        cases hr' : lower1 ((x, t, [w]) :: env) n e with
        | none => cases ht : scalar1 t <;> simp [ht, hr'] at hr
        | some r' =>
          cases ht : scalar1 t <;> simp [ht, hr'] at hr
          subst hr
          have ih' := ih _ n r' pc hr' (hfr.atom ha x) hcode hbl (immIn_tail1_atom ha hImm)
          refine ih'.mono_pre fun s c ⟨he, hn, hd, hpc, σ, hA, hFm, hJ, hfj, hc0⟩ =>
            ⟨he, hn, hd, hpc, σ, hA, hFm, ?_, hfj, hc0⟩
          rw [ofEnv_cons]
          exact hJ.atom (sevalAt_ofEnv ha)
    | add a b =>
      have hr0 := hr
      simp only [lower1] at hr
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
          cases hr' : lower1 ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp [hr'] at hr
            subst hr
            obtain ⟨la, lb, off, hla, hlb, hd, hc1, hc2, hrest⟩ := hcode
            have hfv := lower1_fv (.let_ x (.add a b) e) env n _ hr0
            have hadd := add_seg (p := p) (lbl := lbl) (ms := ms) (fp := fp) (ra := ra) (c0 := c0) (x := x) (e := e)
              hf h1 h16 hla hlb hd (hCd _ _ hc1) hF hR hal hlo hhi
              (sevalAt_ofEnv ha) (sevalAt_ofEnv hb) (hfr.ofEnv x)
              (fun y hy => isSome_lookupS_ofEnv (hfv y hy)) (immIn_head1 hImm).1 (immIn_head1 hImm).2
              (hW _ _ _ _ hc1)
            have hst := store_seg (p := p) (lbl := lbl) (ms := ms) (fp := fp) (ra := ra) (c0 := c0)
              (t := e) (s := (x, .int, [.one (.reg (Scc.Lower.Inv.regName x n))]) :: ofEnv env)
              hf h1 h16 hd (hCd _ _ hc2) hF hR hal hlo hhi (hWp _ _ _ _ _ hc2)
            have ih' := ih _ (n + 1) r' _ hr' (hfr.add x) hrest hbl (immIn_tail1_add hImm)
            rw [ofEnv_cons] at ih'
            refine (SegW.seq_left (hadd.mono_post fun s c h => h.elim (fun ⟨_, h⟩ => .inl h)
              fun ⟨_, h⟩ => .inr h) (hst.seq ih')).mono_post fun s c h => ?_
            rcases h with h | h
            · exact h
            · exact .inr h
    | sub a b =>
      simp only [lower1] at hr
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
          cases hr' : lower1 ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp [hr'] at hr
            subst hr
            obtain ⟨la, lb, off, hla, hlb, hd, hc1, hc2, hrest⟩ := hcode
            have hsub := sub_seg (p := p) (lbl := lbl) (ms := ms) (fp := fp) (ra := ra) (c0 := c0) (x := x) (e := e)
              hf h1 h16 hla hlb hd (hCd _ _ hc1) hF hR hal hlo hhi
              (sevalAt_ofEnv ha) (sevalAt_ofEnv hb) (hfr.ofEnv x) (hW _ _ _ _ hc1)
            have hst := store_seg (p := p) (lbl := lbl) (ms := ms) (fp := fp) (ra := ra) (c0 := c0)
              (t := e) (s := (x, .int, [.one (.reg (Scc.Lower.Inv.regName x n))]) :: ofEnv env)
              hf h1 h16 hd (hCd _ _ hc2) hF hR hal hlo hhi (hWp _ _ _ _ _ hc2)
            have ih' := ih _ (n + 1) r' _ hr' (hfr.add x) hrest hbl (immIn_tail1_sub hImm)
            rw [ofEnv_cons] at ih'
            exact hsub.seq (hst.seq ih')
    | _ => simp [lower1] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n r pc hr hfr hcode hbl hImm
    simp only [lower1] at hr
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
        cases hy : lower1 env (n + 2) yes with
        | none => simp [hy] at hr
        | some ry =>
          cases hn : lower1 env ry.next no with
          | none => simp [hy, hn] at hr
          | some rn =>
            simp [hy, hn] at hr
            subst hr
            obtain ⟨la, lb, Tl, Fl, hla, hlb, hT, hFl, hc1, hc2⟩ := hcode
            have hby := hbl _ (List.mem_cons_self ..)
            have hbn := hbl ⟨Scc.Lower.Inv.labName "else" (n + 1), rn.insts, rn.term⟩ (by simp)
            obtain ⟨Ly, hLy, hcy⟩ := hby
            obtain ⟨Ln, hLn, hcn⟩ := hbn
            simp only [hT, Except.ok.injEq] at hLy
            simp only [hFl, Except.ok.injEq] at hLn
            subst hLy hLn
            have hbly : BlocksCode cx Cd (_root_.Executable.labels exe).label ry.blocks :=
              fun b hb => hbl b (by simp [hb])
            have hbln : BlocksCode cx Cd (_root_.Executable.labels exe).label rn.blocks :=
              fun b hb => hbl b (by simp [hb])
            have hnext := lower1_next yes env (n + 2) ry hy
            have segy := ihy env (n + 2) ry _ hy (hfr.mono (by omega)) hcy hbly (immIn_tail1_yes hImm)
            have segn := ihn env ry.next rn _ hn (hfr.mono (by omega)) hcn hbln
              (by rw [hnext]; exact immIn_tail1_no hImm)
            have hbr := br_seg (p := p) (lbl := lbl) (ms := ms) (fp := fp) (ra := ra) (c0 := c0)
              (yes := yes) (no := no) hf h1 h16 hla hlb Tl (hCd _ _ hc1) hF hR hal hlo hhi
              (sevalAt_ofEnv ha) (sevalAt_ofEnv hb) (hW _ _ _ _ hc1)
            have hj := jmp_seg (p := p) (lbl := lbl) (ms := ms) (fp := fp) (ra := ra) (c0 := c0) (t := no)
              (s := ofEnv env) (cx := cx) Fl (hCd _ _ hc2) hF hR hal hlo hhi (hW _ _ _ _ hc2)
            exact hbr.seq (SegW.or_pre segy (hj.seq segn))
  | ret a =>
    intro env n r pc hr hfr hcode _ _
    simp only [lower1] at hr
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
  | _ => intro env n r pc hr; simp [lower1] at hr

end Body

end Spike.Lib.LowerA64
