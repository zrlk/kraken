/-
**A lowered `Accepted0` body is one segment** (x86-64), symbolic in the
body, the frame, the IR registers' slots, the pc and the cell sizes; the
twin of `Spike/Lib/LowerA64/Body.lean`.

`body_seg`: by induction on the lowering's closed form (`lower0`), from the
node at the body's start (the source at the body, the lowering's
environment placed in the frame's cells: `bodyN`) to the return's exit
(`retN`) or the overflow abort label (`abortN`), given the code of each
emitted block at consecutive pcs, at some cell sizes (`BodyCode`), the
environment's registers fresh for the lowering's destinations (`Fresh`) and
the blocks' states in `W` (`hW`).

- `let x = a`: no code, the node invariant moves past it (`NJ.atom`);
- `let x = a + b`: `add_seg` (to the pending store or the abort label),
  then `store_seg`;
- `ret a`: `ret_seg`.

The ISA-neutral facts about the lowering's environment (`lower0_fv`,
`Fresh`, `ofEnv_cons`, `isSome_lookupS_ofEnv`) are in
`Spike/Lib/LowerEnv.lean`.
-/
import Spike.Lib.LowerX64.Node
import Spike.Lib.LowerEnv

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (Item)
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (lower0 atomV Res scalar1)

set_option linter.unusedSimpArgs false

/-! ## The body's code (x86-64) -/

/-- **The code of a lowered body at `pc`**: each checked `+`'s block, then
its store, then the rest; the `ret`'s load and epilogue last, each block at
some cell sizes of its length. `Cd pc blk`: `blk` is the code at `pc`. -/
def BodyCode (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop) :
    Int64 → List Scc.IR.Inst → List Scc.IR.Operand → Prop
  | pc, [], [w] => ∃ l zs, getOp fr .rax w = .ok l ∧ zs.length = (retDirs l).length ∧ Cd pc ((retDirs l).zip zs)
  | pc, .addChk d a b :: is, ws => ∃ la lb off zs z, getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧
      rsOf fr d = some off ∧ zs.length = (addDirs fr la lb).length ∧ Cd pc ((addDirs fr la lb).zip zs) ∧
      Cd (pc + Int64.ofNat zs.sum) [(stDir off, z)] ∧
      BodyCode fr Cd (pc + Int64.ofNat zs.sum + Int64.ofNat z) is ws
  | _, _, _ => False

/-- The code predicate of an executable. -/
def CdOf (exe : _root_.Executable) (endPc : Int64) (pc : Int64) (blk : List (Directive × Nat)) : Prop :=
  ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc blk

section Body

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isa} {K : State → State → Prop}

/-- **A lowered `Accepted0` body is one segment**: from the node at the
body (the lowering's environment `env` placed in the frame) to the return's
exit or the overflow abort label. The code predicate `Cd` gives the code
(`hCd`); the blocks' states are inside `W` at the body's nodes (`hW`) and
pending stores (`hWp`) at the blocks `Cd` holds of; at each point of the
lowering's walk (`lowerEnvs`) its environment's immediates are `i`'s
(`hImm`) and the point satisfies `T`, which the overflow abort label's
invariant records. -/
theorem body_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 16 ≤ R.hi) {fp ra : BitVec 64} {c0 : Ctl} {Cd : Int64 → List (Directive × Nat) → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hW : ∀ pc t s blk, Cd pc blk → BlkW W K exe endPc R F (bodyN p lbl fr fp ra c0 pc t s) blk)
    (hWp : ∀ pc t s k blk, Cd pc blk → BlkW W K exe endPc R F (pendN p lbl fr fp ra c0 pc t s k) blk)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (r : Res) (pc : Int64), lower0 env n e = some r →
      Fresh env n → BodyCode fr Cd pc r.insts r.ret →
      (∀ q ∈ lowerEnvs env n e, ImmIn i (ofEnv q.2.1) q.1 ∧ T q.1) →
      SegW W K p lbl ms (At exe endPc R F (bodyN p lbl fr fp ra c0 pc e (ofEnv env)))
        (fun s c => At exe endPc R F (retN p lbl fp ra c0) s c ∨
          At exe endPc R F (abortN i T p lbl fr (_root_.Executable.labels exe).label fp ra c0) s c) := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n r pc hr hfr hcode hImm
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
            obtain ⟨la, lb, off, zs, z, hla, hlb, hd, hz, hc1, hc2, hrest⟩ := hcode
            have hfv := lower0_fv (.let_ x (.add a b) e) env n _ hr0
            have hadd := add_seg (p := p) (lbl := lbl) (ms := ms) (fp := fp) (ra := ra) (c0 := c0) (x := x) (e := e)
              hf h1 hla hlb hd hz (hCd _ _ hc1) hF hR hlo hhi
              (sevalAt_ofEnv ha) (sevalAt_ofEnv hb) (hfr.ofEnv x)
              (fun y hy => isSome_lookupS_ofEnv (hfv y hy)) (immIn_head hImm).1 (immIn_head hImm).2
                (hW _ _ _ _ hc1)
            have hst := store_seg (p := p) (lbl := lbl) (ms := ms) (fp := fp) (ra := ra) (c0 := c0)
              (t := e) (s := (x, .int, [.one (.reg (Scc.Lower.Inv.regName x n))]) :: ofEnv env)
              hf h1 hd (hCd _ _ hc2) hF hR hlo hhi (hWp _ _ _ _ _ hc2)
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
      | [w], ⟨l, zs, hl, hz, hc⟩ =>
        exact (ret_seg (p := p) (lbl := lbl) (ms := ms) (fp := fp) (ra := ra) (c0 := c0) hf h1 hl hz (hCd _ _ hc) hF hR
          hlo hhi (sevalAt_ofEnv ha) (hW _ _ _ _ hc)).mono_post fun _ _ h => .inl h
  | _ => intro env n r pc hr; simp [lower0] at hr

end Body

end Spike.Lib.LowerX64
