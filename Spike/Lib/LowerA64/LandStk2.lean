/-
**An allocation's landing with its suspended frames** (AArch64): the
landing family `E` of the levels' starts (`StartsN`, `nodes2_of_starts`'
`h1`) for an `Accepted2` program, design A: at a fresh label's landing
from `scc_rt_alloc` (`Ea`), the allocating frame's context with its
suspended frames (`CxOkS`), its resumption point at the `newBuf` term
(`BodyPtW`, with the walk facts), the call's argument block and `bl` (`pcB`), the allocator's
call context (`AllocCtx` at the call node `nbJc` of `nbJ1`) and the thread
pointer (`TP`). The allocating frame runs no `TermRun` frame of its own, so
the frames `fs` are the context's.

- `LandStk`: the landing pairs at the placement `L`, `ls` (before the
  label `l` at the base `b` with `w` words);
- `landStk_xa`: a landing is in `msOfAX`'s allocation fragment over any
  family containing the starts `StartsN … S0 (LandStk …)` (`xa_of_landN`):
  the allocator's `hxa` once the landing is packed;
- `landStk_hxa`: `AllocW2`'s `hxa` at `msOfAX … (IN … J)` from the
  allocating frame's context, records, ghost and resumption point at the
  `newBuf` term (`LandStk` packed, `AllocLand` from `allocLand_of_ea`).

The memory side `ms0` (at each placement and frames) is the one whose
arena fields (`heap`, `cells`, `units`, `off`, the counter) `Ea`,
`Call.OK` and `AllocCtx` read; `msOfAX` at any two families differs only
in `xa` (`msOfAX_with_xa`), so `ms0` can be `msOfAX` at a fixed family and
`LandStk` need not mention the family the starts are taken in.
-/
import Spike.Lib.LowerA64.Stk2
import Spike.Lib.LowerA64.NewBufC2
import Spike.Lib.LowerA64.Levels2
import Spike.Lib.AllocLandOf

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode
open Scc.Lower.Inv (regName)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.A64.Flow.NewBuf (nbJc AllocCtx)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA

section Land

variable {p : Prog} {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop} {P : Prog}

/-- **An allocation's call arguments** (`lowerC2_newBuf_inv`'s data): the
count `cn` the immediate `kv` in `env`, the element counts `en`, `em` of
`τ` with the header `h`, the units `u` the `unitsOf` of `τ`'s words. -/
def NbArgs (lcx : Scc.Lower.Ctx) (env : Scc.Lower.Env) (cn : At) (τ : Ty) (h : Nat) (kv : UInt64)
    (u : Scc.IR.Operand) : Prop :=
  ∃ tk en em, Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]) ∧
    Spike.Lib.LowerShape.countsO lcx.obj τ = some (en, em) ∧ Scc.Obj.header0 lcx.obj .array en em = some h ∧
    u = Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv

/-- **An allocation's landing with its suspended frames** at the placement
`L`, `ls`, the fresh label `l` at the base `b` with `w` words (see the
module docstring): some compiled block `j` whose context at the frames
`fs` has its records (`CxOkS` at `L`, `ls`), the return address `ra` of
`RaOk`, the ghost `c0` in `G0`; the term `let x = newBuf cn τ in e` a
resumption point at `pc`; the arguments `h`, `kv`, `u` (`NbArgs`) loaded by `la`, the
`bl scc_rt_alloc` at `pcB` after it, the call `q` returning past it; the
allocator's frame condition `F'` inside `F` with `q`'s call context at the
call node; the state at `Ea` in the allocator's region at `F'`, at the
thread pointer `tp`. -/
def LandStk (hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d)
    (CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop) (Bot : StkKey → List TermRun.Frame → Prop)
    (ms0 : Lbl → Lsize → List TermRun.Frame → MemSide isaLSE2) (L : Lbl) (ls : Lsize) (l : WeakMem.AllocLabel)
    (b w : Nat) :
    FragS isaLSE2 := fun s c fs =>
  ∃ (j : Nat) (d : Decl) (hd : P[j]? = some d) (R : Region) (F F' : MachineData → Prop) (fp ra : BitVec 64)
    (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isaLSE2) (c0 : Ctl) (pc pcB : Int64) (x : String) (cn : At)
    (τ : Ty) (e : Expr) (env : Scc.Lower.Env) (n : Nat) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)) (h : Nat) (kv : UInt64) (u : Scc.IR.Operand) (la : List Item)
    (q : {q : Call // q.OK (ms0 L ls fs) (_root_.Executable.labels exe).label}),
    CxOkS (p := p) (lbl := L) (lsize := ls) hcode CxOk Bot j R F fs fp ra tp G0 Ab ∧ RaOk ra ∧ G0 c0 ∧
    BodyPtW (hcode j d hd) ra pc (.let_ x (.newBuf cn τ) e) env n lits cs bufs ∧
    NbArgs (hcode j d hd).lcx env cn τ h kv u ∧
    (hcode j d hd).cx.getArgs [Scc.Lower.imm h, .imm kv, u] = .ok la ∧
    pcB = pc + Int64.ofNat (4 * (directives la).length) ∧ q.1.ra = (pcB + 4).toBitVec ∧
    (∀ m, F' m → F m) ∧
    (∀ m, F' m → AllocCtx (ms0 L ls fs) (_root_.Executable.labels exe).label R (hcode j d hd).cx.frame
      (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF (hcode j d hd).cx)
        (nbJ1 p L ls (hcode j d hd).cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs
          (Scc.Lower.imm h) (.imm kv) u)) q.1 m) ∧
    At exe endPc (R.callee (-((hcode j d hd).cx.frame : Int)) (-160) 0) F' (Ea (ms0 L ls fs) q.1 l b w) s c ∧
    TP tp s

variable {Λ : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {ab : Option (State → Prop)}

/-- **A landing is in the allocation fragment** (`xa_of_landN` at the
landings `LandStk`): at a reachable placement, a fresh label's landing
pair where the arena hands out `b`, `w` is in `msOfAX`'s allocation
fragment over `IN … J`, for every family `J` containing the starts. -/
theorem landStk_xa {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop} {Bot : StkKey → List TermRun.Frame → Prop}
    {ms0 : Lbl → Lsize → List TermRun.Frame → MemSide isaLSE2}
    {own' : OwnS} {S0 : FragS isaLSE2} {J : InvS} {L : Lbl} {ls : Lsize}
    (hP : ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs,
      StartsN ar L0 ls0 S0 (fun L ls l b w => LandStk (p := p) hcode CxOk Bot ms0 L ls l b w) L ls s c fs →
        J L ls s c fs)
    (hR : Reach ar L0 ls0 L ls) {l : WeakMem.AllocLabel} {b w : Nat} (hl : L l = none)
    (hAL : Spike.Lib.HeapLand.AllocLand ar.heap ar.cells b w) {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hE : LandStk (p := p) hcode CxOk Bot ms0 L ls l b w s c fs) :
    (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L ls fs).xa l b w s c :=
  xa_of_landN hP hR hl hAL hE

/-- **`AllocW2`'s allocation fragment from the allocating frame's context**
(`landStk_xa` at a packed `LandStk`): at a reachable placement `L`, `ls`,
for every family `J` containing the starts whose landings read the memory
side at a fixed family `I0`, the allocating frame's context with its records
(`CxOkS` at `fs`), its return address, its ghost and its resumption point at
`let x = newBuf cn τ in e` (`BodyPtW`) with the call's argument block `la`
give `AllocW2`'s `hxa` at `msOfAX … (IN … J)`: the call returns past the `bl`
(the call context's `x30`), and the landing is the arena's (`allocLand_of_ea`
under the arena's laws `hok`, the object fitting by the arena's units
`hfu`: an object whose units are within the cells takes `k · nWords us + 1`
of them, so the landing's own bound fits it). -/
theorem landStk_hxa {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop} {Bot : StkKey → List TermRun.Frame → Prop}
    {own' : OwnS} {S0 : FragS isaLSE2} {I0 J : InvS} {L : Lbl} {ls : Lsize} (hok : ar.OK)
    (hP : ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs,
      StartsN ar L0 ls0 S0
        (fun L ls l b w => LandStk (p := p) hcode CxOk Bot (msOfAX Λ μ p rd G own' ar I0 ab) L ls l b w) L ls s c fs →
        J L ls s c fs)
    (hR : Reach ar L0 ls0 L ls) {fs : List TermRun.Frame} {j : Nat} {d : Decl} (hd : P[j]? = some d)
    {R : Region} {F : MachineData → Prop} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop}
    {Ab : FragS isaLSE2}
    (hcx : CxOkS (p := p) (lbl := L) (lsize := ls) hcode CxOk Bot j R F fs fp ra tp G0 Ab) (hra : RaOk ra)
    {c0 : Ctl} (hc0 : G0 c0) {pc : Int64} {x : String} {cn : At} {τ : Ty} {e : Expr} {env : Scc.Lower.Env}
    {n : Nat} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (hpt : BodyPtW (hcode j d hd) ra pc (.let_ x (.newBuf cn τ) e) env n lits cs bufs)
    {h : Nat} {kv : UInt64} {u : Scc.IR.Operand} {la : List Item}
    (hnb : NbArgs (hcode j d hd).lcx env cn τ h kv u)
    (hla : (hcode j d hd).cx.getArgs [Scc.Lower.imm h, .imm kv, u] = .ok la)
    (hfu : ∀ k τ us, TermRun.accs (TermRun.close [] τ) = some us → ar.units k τ ≤ ar.cells →
      ar.units k τ = k * TermRun.nWords us + 1) :
    ∀ q : {q : Call // q.OK (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L ls fs)
        (_root_.Executable.labels exe).label},
      ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → AllocCtx (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L ls fs)
        (_root_.Executable.labels exe).label R (hcode j d hd).cx.frame
        (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc]
          (pc + Int64.ofNat (4 * (directives la).length)) (oF (hcode j d hd).cx)
          (nbJ1 p L ls (hcode j d hd).cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs
            (Scc.Lower.imm h) (.imm kv) u)) q.1 m) →
      ∀ l b w s c, L l = none →
        At exe endPc (R.callee (-((hcode j d hd).cx.frame : Int)) (-160) 0) F'
          (Ea (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L ls fs) q.1 l b w) s c →
        TP tp s → (msOfAX Λ μ p rd G own' ar (IN ar L0 ls0 J) ab L ls fs).xa l b w s c := by
  intro q F' hF' hctx l b w s c hl hAt htp
  -- the memory sides at the two families differ only in `xa`
  have hq0 : q.1.OK (msOfAX Λ μ p rd G own' ar I0 ab L ls fs) (_root_.Executable.labels exe).label := by
    have h := q.2
    cases ab <;>
      exact ⟨h.term, h.ev, h.num, h.hold, h.n_lt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, h.accs, h.rt,
        h.mp, h.grow, h.hdr⟩
  have hctx0 : ∀ m, F' m → AllocCtx (msOfAX Λ μ p rd G own' ar I0 ab L ls fs)
      (_root_.Executable.labels exe).label R (hcode j d hd).cx.frame
      (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc]
        (pc + Int64.ofNat (4 * (directives la).length)) (oF (hcode j d hd).cx)
        (nbJ1 p L ls (hcode j d hd).cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs
          (Scc.Lower.imm h) (.imm kv) u)) q.1 m := by
    intro m hm
    have h := hctx m hm
    cases ab <;> exact h
  have hAt0 : At exe endPc (R.callee (-((hcode j d hd).cx.frame : Int)) (-160) 0) F'
      (Ea (msOfAX Λ μ p rd G own' ar I0 ab L ls fs) q.1 l b w) s c := by
    cases ab <;> exact hAt
  -- the call returns past the `bl`
  obtain ⟨-, -, -, -, σ, -, hFm, hJ⟩ := id hAt
  obtain ⟨mC, σC, c1, -, ⟨σ0, -, hσC⟩, hN, -⟩ := hctx _ hFm
  have hra' : q.1.ra = (pc + Int64.ofNat (4 * (directives la).length) + 4).toBitVec := by
    rw [← hN.2.2.1]
    show σC.regs.X30.toBitVec = _
    rw [hσC]
    erw [blD_run]
    simp only [Reg64s.setXReg]
  -- the landing is the arena's
  obtain ⟨ini, old, -, -, hb, hold, -, -, -, us, hus, hw⟩ := hJ
  have hold' : old + ar.units q.1.n q.1.τ ≤ ar.cells := by cases ab <;> exact hold
  have hu' := hfu q.1.n q.1.τ us hus (by omega)
  have hb' : b = ar.heap + 16 * old + ar.off q.1.n q.1.τ := by cases ab <;> exact hb
  have hAL : Spike.Lib.HeapLand.AllocLand ar.heap ar.cells b w :=
    Spike.Lib.AllocReach.allocLand_of_ea hok hus hb' hold' hw (by omega)
  exact landStk_xa hP hR hl hAL ⟨j, d, hd, R, F, F', fp, ra, tp, G0, Ab, c0, pc, _, x, cn, τ, e, env, n, lits,
    cs, bufs, h, kv, u, la, ⟨q.1, hq0⟩, hcx, hra, hc0, hpt, hnb, hla, rfl, hra', hF', hctx0, hAt0, htp⟩

end Land

/-- info: 'Spike.Lib.LowerA64.landStk_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.landStk_xa

/-- info: 'Spike.Lib.LowerA64.landStk_hxa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.landStk_hxa

end Spike.Lib.LowerA64
