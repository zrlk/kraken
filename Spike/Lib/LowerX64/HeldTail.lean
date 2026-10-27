/-
**`W2` at a pair held through `main`'s return tail** (x86-64): the
held-pair obligation (`SegWS.lagF`'s `hW`, `xExitTail_segWSF`'s `hWx`) for
the walk's last construct a call or `print` whose continuation is a `ret`
of the call's result or of a literal (`HeldTail`). The source is held at
the callee's `ret a` one frame above `main`'s depth 0, the frame's
continuation `ret b` reading nothing but the result.

At such a pair the frame runs reach only the held pair and `main`'s `ret`
(`frameRun_heldTail`), so the run obligations (`RunOk2`, `W2.wr` off a
write) are vacuous; the frame has nothing to place, so the pair is placed
as soon as the callee's `ret a` is at depth 0 (`placedS_heldTail`), which
holds outright for a literal (`placedS_nil_of_fv`).

- `HeldTail`: the held shape; `heldTail_of_frame`: from the frame's origin;
- `frameRun_heldTail`, `runOk2_heldTail`, `placedS_heldTail`,
  `placedS_nil_of_fv`, `placedS_ret_reg` (the result's word in a register);
- `w2_heldTail`: `W2` at the held pair from the state's facts, the callee's
  `ret` placed at depth 0, no write, no abort site and no output `write`;
- `frOk2_heldTail`, `w2Part_heldTail`: the node and state parts of
  `BlkW.w2`/`NodeW.w2` (`Spike/Lib/LowerX64/W2Blk.lean`) at a held pair, so
  the tail's blocks are inside `W2` at the held frames with the abort sites
  excluded by `SFacts` at the source start's control as for every block;
- `Ret0`, `placedS_ret0`, `HeldS`, `blkW_heldTail`, `nodeW_heldTail`: the
  tail's blocks and nodes inside `W2` at the held frames in one step, from
  `SFacts` at the source start's control, the node's invariant `HeldTail`
  and the per-state inputs (`HeldS`: `AbSt`, the callee's `ret` a literal
  or a register word, no write, no output `write`); `blkW_heldTailN`,
  `nodeW_heldTailN`: the same at a held node, `SFacts` from the ordinary node's;
- `notWrite1_of_abs`: at `%rax = 231` the system call is no output `write`.
-/
import Spike.Lib.LowerX64.W2Blk
import Spike.Lib.X64Dead

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.LowerNode (RunOk2)

/-- **The held shape through `main`'s return tail**: a callee's `ret a` one
frame above depth 0, the frame (no pending regions) continuing with a
`ret b` that reads nothing but the frame's result `f.x` (the call's result,
or a literal). -/
def HeldTail (c : Ctl) (fs : List TermRun.Frame) : Prop :=
  ∃ a f b, c.term = .ret a ∧ fs = [f] ∧ f.σs = [] ∧ f.body = .ret b ∧ (atVars b).filter (· != f.x) = []

/-- **A held pair from its frame's origin**: the callee at a `ret`, one
frame pushed by `let x = call … in ret b` (no pending stores, its result
variable `x`, its body `ret b`) with `b` a literal or `x` itself. -/
theorem heldTail_of_frame {c : Ctl} {f : TermRun.Frame} {x : String} {a b : At} (hc : c.term = .ret a)
    (hσ : f.σs = []) (hf : f.x = x) (hb : f.body = .ret b) (hbx : (∃ n, b = .lit n) ∨ b = .var x) :
    HeldTail c [f] :=
  ⟨a, f, b, hc, rfl, hσ, hb, by rcases hbx with ⟨n, rfl⟩ | rfl <;> simp [atVars, hf]⟩

/-- **The frame runs from a held pair**: the pair itself, or `main`'s `ret`
at depth 0 past the callee's return. -/
theorem frameRun_heldTail {p : Prog} {c c' : Ctl} {fs fs' : List TermRun.Frame} (hH : HeldTail c fs)
    (hr : FrameRun p (c, fs) (c', fs')) : (c' = c ∧ fs' = fs) ∨ (fs' = [] ∧ ∃ b, c'.term = .ret b) := by
  obtain ⟨a, f, b, hc, rfl, -, hb, -⟩ := hH
  cases hr with
  | refl => exact .inl ⟨rfl, rfl⟩
  | step h1 h2 =>
    cases h1 with
    | loc hl => exact absurd hc (hl.not_ret a)
    | call hc' => rw [hc] at hc'; cases hc'
    | ret _ _ _ =>
      refine .inr ?_
      cases h2 with
      | refl => exact ⟨rfl, b, hb⟩
      | step h3 _ =>
        cases h3 with
        | loc hl => exact absurd hb (hl.not_ret b)
        | call hc' => rw [hb] at hc'; cases hc'

/-- **The run obligations at a held pair are vacuous**: every pair a frame
run reaches is a `ret`. -/
theorem runOk2_heldTail {p : Prog} {c : Ctl} {fs : List TermRun.Frame} (hH : HeldTail c fs) : RunOk2 p c fs := by
  have hret : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∃ b, c'.term = .ret b := by
    intro c' fs' hr
    rcases frameRun_heldTail hH hr with ⟨rfl, -⟩ | ⟨-, hb⟩
    · obtain ⟨a, -, -, hc, -⟩ := hH; exact ⟨a, hc⟩
    · exact hb
  refine ⟨fun c' fs' hr x a e ty w hm _ => ?_, fun c' fs' hr x a τ e hm => ?_⟩
  · obtain ⟨b, hb⟩ := hret c' fs' hr
    rcases hm with hm | ⟨_, hm⟩ <;> rw [hb] at hm <;> cases hm
  · obtain ⟨b, hb⟩ := hret c' fs' hr
    rw [hb] at hm; cases hm

/-- **A control reading nothing is placed at depth 0**, at no place. -/
theorem placedS_nil_of_fv {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} (h : exprFv c.term = []) :
    PlacedS Λ lbl s c [] := by
  refine ⟨fun _ _ _ => none, fun _ _ _ _ _ _ _ _ _ _ _ he => by simp at he, fun d env xs _ hxs x hx => ?_,
    fun _ _ _ _ _ _ he => by simp at he⟩
  cases d with
  | zero => simp only [fvOf, List.getElem?_cons_zero, Option.some.injEq] at hxs; subst hxs; rw [h] at hx; cases hx
  | succ d => simp [fvOf] at hxs

/-- **A `ret` of a one-word variable placed at one place** at depth 0: the
variable's word at the place `pl` (`hr`; a register, or a stack slot), the
only place the control reads. -/
theorem placedS_ret_reg {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {x : String} {ty : Ty}
    {w : TermRun.Word} (hc : c.term = .ret (.var x)) (hl : TermRun.lookupE c.env x = some (ty, [w]))
    {pl : Place (machine (kernel 1)).I.RegId} (hr : WordPlaceRep (machine (kernel 1)) lbl s (.one pl) w.val) :
    PlacedS Λ lbl s c [] := by
  refine ⟨fun d y k => if d = 0 ∧ y = x ∧ k = 0 then some (.one pl) else none, ?_, ?_, ?_⟩
  · intro d env hd y ty' ws hl' k wd wp hk he
    by_cases hc' : d = 0 ∧ y = x ∧ k = 0
    · obtain ⟨rfl, rfl, rfl⟩ := hc'
      simp only [envsOf, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      rw [hl] at hl'
      cases hl'
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp only [true_and, ite_true, Option.some.injEq] at he
      subst he
      exact hr
    · simp [hc'] at he
  · intro d env xs hd hxs y hy ty' ws hl' k hk
    cases d with
    | zero =>
      simp only [fvOf, List.getElem?_cons_zero, Option.some.injEq] at hxs
      subst hxs
      rw [hc] at hy
      simp only [exprFv, atVars, List.mem_singleton] at hy
      subst hy
      simp only [envsOf, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      rw [hl] at hl'
      cases hl'
      simp only [List.length_singleton, Nat.lt_one_iff] at hk
      subst hk
      exact ⟨.one pl, by simp⟩
    | succ d => simp [fvOf] at hxs
  · intro d e y k n _ he
    by_cases hc' : d = 0 ∧ y = x ∧ k = 0
    · simp [hc'] at he
    · simp [hc'] at he

/-- **A held pair is placed once the callee's `ret` is placed at depth 0**:
the frame reads nothing but its result. -/
theorem placedS_heldTail {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hH : HeldTail c fs) (h0 : PlacedS Λ lbl s c []) : PlacedS Λ lbl s c fs := by
  obtain ⟨a, f, b, -, rfl, -, hb, hfv⟩ := hH
  obtain ⟨envm, h1, h2, h3⟩ := h0
  refine ⟨fun d => if d = 0 then envm 0 else fun _ _ => none, ?_, ?_, ?_⟩
  · intro d env hd x ty ws hl k wd wp hk he
    cases d with
    | zero => exact h1 0 env (by simpa [envsOf] using hd) x ty ws hl k wd wp hk (by simpa using he)
    | succ d => simp at he
  · intro d env xs hd hxs x hx ty ws hl k hk
    cases d with
    | zero =>
      exact h2 0 env xs (by simpa [envsOf] using hd) (by simpa [fvOf] using hxs) x hx ty ws hl k hk
    | succ d =>
      cases d with
      | zero =>
        simp only [fvOf, List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hxs
        subst hxs
        rw [hb] at hx
        simp only [exprFv] at hx
        rw [hfv] at hx
        cases hx
      | succ d => simp [fvOf] at hxs
  · intro d e x k n hd he
    cases d with
    | zero => exact h3 0 e x k n (by simpa [termsOf] using hd) (by simpa using he)
    | succ d => simp at he

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop} {lbl : Lbl}
  {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}

/-- **`W2` at a held pair** of `main`'s return tail (`HeldTail`): from the
state's facts (`SFactsSt`, `AbSt`), the callee's `ret` placed at depth 0
(`h0`; `placedS_nil_of_fv` for a literal), and at the state no write
(`hnw`), no abort site (`hnab`) and no output `write` (`hnw1`). -/
theorem w2_heldTail (hH : HeldTail c fs) (hst : SFactsSt Λ μ own rS Tk s Dt) (hab : AbSt μ Ab s)
    (h0 : PlacedS Λ lbl s c []) (hnw : ∀ L, ¬ WrAt s L) (hnab : ∀ k a, μ.abortAt k = some a → pcOf s ≠ a)
    (hnw1 : abi.atSys s = true → ∀ b n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 b n)) :
    W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs := by
  refine ⟨hst, hab, ?_, runOk2_heldTail hH, .of_placedS (placedS_heldTail hH h0), ?_, ?_, ?_⟩
  · obtain ⟨_, f, _, _, rfl, _⟩ := hH
    intro h; cases h
  · exact fun _ _ _ _ => ⟨fun L hL => absurd hL (hnw L), fun hL => absurd hL (hnw _)⟩
  · exact fun k a hk ha => absurd ha (hnab k a hk)
  · exact fun hs b n hd => absurd hd (hnw1 hs b n)

/-- **A held pair is free of `ZBad`**: both terms are `ret`s. -/
theorem frOk2_heldTail {c : Ctl} {fs : List TermRun.Frame} (hH : HeldTail c fs) : LowerNode.FrOk2 c fs := by
  obtain ⟨a, f, b, hc, rfl, -, hb, -⟩ := hH
  refine ⟨by rw [hc]; trivial, fun fr hfr => ?_⟩
  rw [List.mem_singleton] at hfr
  subst hfr
  rw [hb]; trivial

/-- **The node part of `BlkW.w2` at a held pair**: `main`'s `ret` excluded
(the pair is at depth) and `FrOk2`. -/
theorem nodeJ_heldTail {c : Ctl} {fs : List TermRun.Frame} (hH : HeldTail c fs) :
    (fs = [] → ∀ a, c.term ≠ .ret a) ∧ LowerNode.FrOk2 c fs := by
  refine ⟨?_, frOk2_heldTail hH⟩
  obtain ⟨_, f, _, _, rfl, _⟩ := hH
  intro h; cases h

/-- **The state part of `BlkW.w2` at a held pair** (`W2Part`): the abort
phase's facts, the callee's `ret` placed at depth 0, no write and no output
`write`. -/
theorem w2Part_heldTail {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : Own} {ar : Arena} {J : InvS} {Ab : State → Prop} {lbl : Lbl} {lsize : Lsize}
    {s : State} {c : Ctl} {fs : List TermRun.Frame} (hH : HeldTail c fs) (hab : AbSt μ Ab s)
    (h0 : PlacedS Λ lbl s c []) (hnw : ∀ L, ¬ WrAt s L)
    (hnw1 : abi.atSys s = true → ∀ b n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 b n)) :
    W2Part Λ μ p rd G own ar J Ab lbl lsize fs s c :=
  ⟨hab, placedS_heldTail hH h0, fun _ _ _ _ => wrOkA_of_noWr hnw, fun hs b n hd => absurd hd (hnw1 hs b n)⟩

/-- **The callee's `ret` at depth 0 placed outright**: a `ret` reading
nothing (a literal, `placedS_nil_of_fv`), or of a one-word variable whose
word is at one place, a register or a stack slot (`placedS_ret_reg`). -/
def Ret0 (lbl : Lbl) (s : State) (c : Ctl) : Prop :=
  exprFv c.term = [] ∨ ∃ x ty w, ∃ pl : Place (machine (kernel 1)).I.RegId, c.term = .ret (.var x) ∧
    TermRun.lookupE c.env x = some (ty, [w]) ∧ WordPlaceRep (machine (kernel 1)) lbl s (.one pl) w.val

theorem placedS_ret0 {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} (h : Ret0 lbl s c) :
    PlacedS Λ lbl s c [] := by
  rcases h with h | ⟨x, ty, w, pl, hc, hl, hr⟩
  · exact placedS_nil_of_fv h
  · exact placedS_ret_reg hc hl hr

/-- **The per-state inputs of `W2` at a held pair**: the abort phase's
facts (`AbSt`), the callee's `ret` placed outright (`Ret0`), no write and
no output `write`. -/
def HeldS (μ : Marks) (Ab : State → Prop) (lbl : Lbl) : Frag isa := fun s c =>
  AbSt μ Ab s ∧ Ret0 lbl s c ∧ (∀ L, ¬ WrAt s L) ∧
    (abi.atSys s = true → ∀ b n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 b n))

section Blk

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop} {lbl lbl0 : Lbl}
  {lsize : Lsize} {fs : List TermRun.Frame} {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region}
  {F : MachineData → Prop} {K : State → State → Prop}

/-- **A tail block's states inside `W2` at the held frames** (`BlkW.w2`
at a held pair): `SFacts` at the source start's control (`dumN n`), every
control of the node's invariant `HeldTail`, and the per-state inputs
(`HeldS`). -/
theorem blkW_heldTail (hp : ProgNoS Spike.Lib.LowerNode.ZBad p) {n : Spike.Lib.X64.ND}
    {blk : List (Directive × Nat)}
    (hS : Spike.Lib.X64.BlkW (fun s c => SFacts Λ μ own rS Tk lbl0 s c) K exe endPc R F
      (Spike.Lib.X64.AllocG.dumN n) blk)
    (hH : ∀ σ c, n.J σ c → HeldTail c fs)
    (hP : Spike.Lib.X64.BlkW (HeldS μ Ab lbl) (fun _ _ => False) exe endPc R F n blk) :
    Spike.Lib.X64.BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk :=
  BlkW.w2 hp hS
    (fun s σ c he hn hd hpc hA hF hJn k hk m hA' hD =>
      let h := (hP s σ c he hn hd hpc hA hF hJn k hk m hA' hD).1
      ⟨w2Part_heldTail (hH σ c hJn) h.1 (placedS_ret0 h.2.1) h.2.2.1 h.2.2.2, fun _ h => h⟩)
    fun σ c hJn => nodeJ_heldTail (hH σ c hJn)

/-- **A tail node's states inside `W2` at the held frames** (as
`blkW_heldTail`, at `NodeW.w2`). -/
theorem nodeW_heldTail (hp : ProgNoS Spike.Lib.LowerNode.ZBad p) {n : Spike.Lib.X64.ND}
    (hS : Spike.Lib.X64.NodeW (fun s c => SFacts Λ μ own rS Tk lbl0 s c) K exe endPc R F
      (Spike.Lib.X64.AllocG.dumN n))
    (hH : ∀ σ c, n.J σ c → HeldTail c fs)
    (hP : Spike.Lib.X64.NodeW (HeldS μ Ab lbl) (fun _ _ => False) exe endPc R F n) :
    Spike.Lib.X64.NodeW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n :=
  NodeW.w2 hp hS
    (fun s c hA => by
      obtain ⟨h1, h2, h3, h4, σ, hAb, hF, hJn⟩ := hA
      have h := (hP s c ⟨h1, h2, h3, h4, σ, hAb, hF, hJn⟩).1
      exact ⟨w2Part_heldTail (hH σ c hJn) h.1 (placedS_ret0 h.2.1) h.2.2.1 h.2.2.2, fun _ h => h⟩)
    fun σ c hJn => nodeJ_heldTail (hH σ c hJn)

/-- **A tail block at a held node inside `W2`, `SFacts` from the ordinary
node's**: the held node `⟨n.pc, n.o, J'⟩` (e.g. `heldRN p fs n`) has `n`'s
pc and offsets, and each of its controls is `HeldTail` with a control at
`n`'s invariant (`hJ`), so `SFacts` at the source start's control at `n`
(`hS`, which reads no control) serves it; then `blkW_heldTail`. -/
theorem blkW_heldTailN (hp : ProgNoS Spike.Lib.LowerNode.ZBad p)
    {n : Spike.Lib.X64.ND} {J' : Spike.Lib.X64.AS → Ctl → Prop}
    {blk : List (Directive × Nat)}
    (hS : Spike.Lib.X64.BlkW (fun s c => SFacts Λ μ own rS Tk lbl0 s c)
      K exe endPc R F (Spike.Lib.X64.AllocG.dumN n) blk)
    (hJ : ∀ σ c, J' σ c → HeldTail c fs ∧ ∃ c', n.J σ c')
    (hP : Spike.Lib.X64.BlkW (HeldS μ Ab lbl) (fun _ _ => False) exe endPc R F ⟨n.pc, n.o, J'⟩ blk) :
    Spike.Lib.X64.BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs)
      K exe endPc R F ⟨n.pc, n.o, J'⟩ blk :=
  blkW_heldTail hp (fun s σ c he hn hd hpc hA hF hJn k hk m hA' hD => by
      obtain ⟨hc, c1, h1⟩ := hJn
      exact hS s σ c he hn hd hpc hA hF ⟨hc, (hJ σ c1 h1).2⟩ k hk m hA' hD)
    (fun σ c h => (hJ σ c h).1) hP

/-- **A tail node at a held node inside `W2`, `SFacts` from the ordinary
node's** (as `blkW_heldTailN`, at `nodeW_heldTail`). -/
theorem nodeW_heldTailN (hp : ProgNoS Spike.Lib.LowerNode.ZBad p)
    {n : Spike.Lib.X64.ND} {J' : Spike.Lib.X64.AS → Ctl → Prop}
    (hS : Spike.Lib.X64.NodeW (fun s c => SFacts Λ μ own rS Tk lbl0 s c) K exe endPc R F (Spike.Lib.X64.AllocG.dumN n))
    (hJ : ∀ σ c, J' σ c → HeldTail c fs ∧ ∃ c', n.J σ c')
    (hP : Spike.Lib.X64.NodeW (HeldS μ Ab lbl) (fun _ _ => False) exe endPc R F ⟨n.pc, n.o, J'⟩) :
    Spike.Lib.X64.NodeW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs)
      K exe endPc R F ⟨n.pc, n.o, J'⟩ :=
  nodeW_heldTail hp (fun s c hA => by
      obtain ⟨h1, h2, h3, h4, σ, hAb, hF, hc, c1, hJ1⟩ := hA
      exact hS s c ⟨h1, h2, h3, h4, σ, hAb, hF, hc, (hJ σ c1 hJ1).2⟩)
    (fun σ c h => (hJ σ c h).1) hP

end Blk

/-- **At `%rax = 231` the system call is `exit_group`**, so no output
`write` (the `exit_group` tail's `syscall`, `xExitNx`). -/
theorem notWrite1_of_abs {R : Spike.Lib.Region} {o : Spike.Lib.X64.SO} {s : State} {σ : Spike.Lib.X64.AS}
    (hA : Spike.Lib.X64.Abs R o s.st.1 σ) (h231 : σ.regs.rax.toNat = 231) :
    ∀ b n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 b n) := by
  intro b n hd
  have he : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup σ.regs.rdi.toNat) := by
    rw [← Spike.Lib.X64.syscallCall_exitGroup h231, Spike.Lib.X64.syscallCall, ← hA.regs]; rfl
  rw [he] at hd; cases hd

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.w2_heldTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms w2_heldTail

/-- info: 'Spike.Lib.LowerX64.heldTail_of_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms heldTail_of_frame

/-- info: 'Spike.Lib.LowerX64.placedS_nil_of_fv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms placedS_nil_of_fv

/-- info: 'Spike.Lib.LowerX64.placedS_ret_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms placedS_ret_reg

/-- info: 'Spike.Lib.LowerX64.w2Part_heldTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms w2Part_heldTail

/-- info: 'Spike.Lib.LowerX64.notWrite1_of_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms notWrite1_of_abs

/-- info: 'Spike.Lib.LowerX64.blkW_heldTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_heldTail

/-- info: 'Spike.Lib.LowerX64.nodeW_heldTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_heldTail

/-- info: 'Spike.Lib.LowerX64.blkW_heldTailN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_heldTailN

/-- info: 'Spike.Lib.LowerX64.nodeW_heldTailN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_heldTailN

end Spike.Lib.LowerX64
