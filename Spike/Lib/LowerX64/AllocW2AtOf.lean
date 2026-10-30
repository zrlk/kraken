/-
**Every allocation's `AllocW2` at `W₀ := W2`** (x86-64; the twin of
`Spike/Lib/LowerA64/AllocW2AtOf.lean`): `AllocW2At` (the premise `hAW` of
`newBufC_of` and `CxLB`) from `allocW2_w2Full` at each allocation of a body,
the walk facts `allocW2_w2Full` asks at the `let` and its continuation taken
from the allocation's resumption facts (`PtC2`).

- `PtC2.newBufW`: at a `PtC2` at `let x = newBuf cn τ in e`, the `let`'s
  free variables bound (`lowerC2_fv`), its immediates, grouping and register
  bases (the walk's head), the count atom in the literal walk (`LitPt`), and
  the continuation's free variables, immediates and register bases at the
  extended environment (`lowerC2_newBuf_inv`, `walk2_tail_newBuf`);
- `AllocPtW`: the per-allocation premises `allocW2_w2Full` takes beyond the
  walk facts (the count a literal leaf, the units, the element's accesses,
  the call's memory-side fields, the continuation no `main` return, and the
  allocator's `hxa` at the call's argument block and `callq`, `hxaF`,
  `hstub` at every `callq` pc and size);
- `allocW2At_of`: `AllocW2At` at the code `CdCLE … ra0`, the calls
  `BlC2L … fr ra0` and the immediates `Λ.imms` from `allocW2_w2Full`'s
  allocation-independent premises, the elements `elem2` (`hTn`), the ghosts
  `FrOk2` (`hG0F`) and `AllocPtW` at every allocation (`hpt`).
-/
import Spike.Lib.LowerX64.AllocW2Full

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun MemSide)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (BlkW At FStable CKept Abs AS)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff TakeK CallerCells)
open Spike.Lib.X64.Flow.NewBuf (AllocCtx nbJc)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.X64.Alloc (Call AllocW)
open Spike.Lib.X64.AllocG (allocPhOk allocAbOk)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.AllocReach (Reach IN)

/-- **The walk facts at an allocation from its resumption facts**: at a
`PtC2` at `let x = newBuf cn τ in e`, the `let`'s free variables bound
(`lowerC2_fv`), its register bases, immediates and grouping (the lowering
walk's head), the count atom bound in the literal walk (`LitPt` at its
head), and at the continuation's environment (`lowerC2_newBuf_inv`,
`walk2_tail_newBuf`) `e`'s free variables bound, immediates and register
bases. -/
theorem PtC2.newBufW {lcx : Scc.Lower.Ctx} {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} {lab : Label → Int64} {i : Expr → String → Nat → Option Nat}
    {T : Expr → Prop} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop} {kk : Nat} {pc : Int64}
    {env : Scc.Lower.Env} {n : Nat} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    {x : String} {cn : At} {τ : Ty} {e : Expr}
    (h : PtC2 lcx fr Cd Bl lab i T Lk kk pc env n lits cs bufs (.let_ x (.newBuf cn τ) e)) :
    (∀ y ∈ Scc.Sem.exprFv (.let_ x (.newBuf cn τ) e),
      (Spike.Lib.Form.lookupS (Spike.Lib.LowerNode.ofEnv2 env) y).isSome) ∧
    Spike.Lib.LowerNode.LocBaseRegAt (Spike.Lib.LowerNode.ofEnv2 env) (.let_ x (.newBuf cn τ) e) ∧
    Spike.Lib.LowerNode.ImmIn i (Spike.Lib.LowerNode.ofEnv2 env) (.let_ x (.newBuf cn τ) e) ∧
    Spike.Lib.LowerNode.GrpL env ∧ Spike.Lib.LowerNode.InLits lits cn ∧
    (∀ y ∈ Scc.Sem.exprFv e, (Spike.Lib.Form.lookupS (Spike.Lib.LowerNode.ofEnv2
      ((x, Spike.Lib.LowerShape.newBufTy τ, [.reg (Scc.Lower.Inv.regName x n), Scc.Lower.imm 0]) :: env)) y).isSome) ∧
    Spike.Lib.LowerNode.ImmIn i (Spike.Lib.LowerNode.ofEnv2
      ((x, Spike.Lib.LowerShape.newBufTy τ, [.reg (Scc.Lower.Inv.regName x n), Scc.Lower.imm 0]) :: env)) e ∧
    Spike.Lib.LowerNode.LocBaseRegAt (Spike.Lib.LowerNode.ofEnv2
      ((x, Spike.Lib.LowerShape.newBufTy τ, [.reg (Scc.Lower.Inv.regName x n), Scc.Lower.imm 0]) :: env)) e := by
  obtain ⟨l, k, r, hr, -, -, hWs, hLs, -, -⟩ := h
  have hh := Spike.Lib.LowerNode.walk2_head hWs
  obtain ⟨tk, kv, en, em, hh', sc, hq, r', ha, hc, hhd, hw, hm, hr', rfl⟩ :=
    Spike.Lib.LowerShape.lowerC2_newBuf_inv hr
  have h2 := Spike.Lib.LowerNode.walk2_head (Spike.Lib.LowerShape.walk2_tail_newBuf ha hc hhd hw hm hWs)
  refine ⟨fun y hy => isSome_lookupS_ofEnv2 (Spike.Lib.LowerShape.lowerC2_fv lcx _ _ _ _ _ _ hr y hy),
    hh.2.2.2.2, hh.1, hh.2.2.2.1, ?_,
    fun y hy => isSome_lookupS_ofEnv2 (Spike.Lib.LowerShape.lowerC2_fv lcx e _ _ _ _ _ hr' y hy),
    h2.1, h2.2.2.2.2⟩
  exact (hLs (.let_ x (.newBuf cn τ) e, lits) (by simp [Scc.Lower.litWalk2])).1.1 cn
    (by simp [Spike.Lib.LowerNode.headAtoms])

section Of

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop} {a : Int64}

set_option hygiene false in
/-- The rows' memory side at the placement `lbl`, `lsize` and frames `fs`
over `IN … J` (`allocW2_w2Full`'s). -/
local notation "MS" J:max => msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs

set_option hygiene false in
/-- The allocation's continuation at the `callq` at `pcB` of size `zc`. -/
local notation "NJ" pcB:max zc:max => nbJc (_root_.Executable.labels exe).label
  [(Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel Scc.Lower.Names.alloc)), zc)] pcB (oB fr)
  (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h) (.imm kv) u)

/-- **One allocation's premises of `allocW2_w2Full` beyond the walk
facts**, at the allocation `let x = newBuf cn τ in e` with the ghost `c0`,
the environment `env`, the literal walk `lits`, the known values `cs`,
`bufs`, the header `h`, the count `kv` and the units `u`: the count a
literal leaf (`hleaf`), the units (`hu`), the element's accesses (`hacc`),
the call's memory-side fields (`hms`), the continuation no `main` return at
no frame (`hnr`), and the allocator's landing fragment (`hxa`, at the
call's argument block `lw` at `pc` in the code `Cd` and the `callq` after it
at `Bl`, `landStk_hxa`'s shape) and heap abort (`hxaF`, `hstub`, at the
same argument block and `callq`; `hxaF` asked at `fsBase = tp`). -/
structure AllocPtW (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : Own) (rS : Range) (Tk : State → Prop) (ar : Arena) (L0 : Lbl) (ls0 : Lsize) (S0 : FragS isa)
    (Es : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (J : InvS) (ab : Option (State → Prop))
    (Dt : State → Prop) (lab : Label → Int64) (a : Int64) (lbl : Lbl) (lsize : Lsize) (fs : List TermRun.Frame)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (fr : Scc.Emit.X64.Frame)
    (Cd : Int64 → List (Directive × Nat) → Prop) (Bl : Int64 → Nat → Label → Nat → Prop)
    (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (pc : Int64) (x : String) (cn : At) (τ : Ty) (e : Expr)
    (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) (h : Nat)
    (kv : UInt64) (u : Scc.IR.Operand) : Prop where
  hleaf : ∃ o, Scc.Lower.litAt lits cn = .leaf o
  hu : ∀ sl, Spike.Lib.Form.opdVal (rsOf fr) sl u = some ((MS J).units kv.toNat τ)
  hacc : ∃ us, TermRun.accs (TermRun.close [] τ) = some us
  hms : ∀ q : Call, q.n = kv.toNat → q.τ = τ → q.h = BitVec.ofNat 64 h →
    CallMsOK (MS J) (_root_.Executable.labels exe).label q
  hnr : fs = [] → ∀ a, e ≠ .ret a
  hxa : ∀ (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc k : Nat),
    getOps fr ([Scc.Lower.imm h, .imm kv, u].zip Scc.Emit.X64.argRegs) = .ok lw → zs.length = (dirs lw).length →
    Cd pc ((dirs lw).zip zs) → Bl (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k →
    ∀ q : {q : Call // q.OK (MS J) (_root_.Executable.labels exe).label}, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → AllocCtx (MS J) (_root_.Executable.labels exe).label R fr.size
        (NJ (pc + Int64.ofNat zs.sum) zc) q.1 m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-(fr.size : Int) - 8) (-160) 8) F'
        (Spike.Lib.X64.Alloc.Ea (MS J) q.1 l b w) s c → TP tp s → (MS J).xa l b w s c
  hxaF : ∀ (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc k : Nat),
    getOps fr ([Scc.Lower.imm h, .imm kv, u].zip Scc.Emit.X64.argRegs) = .ok lw → zs.length = (dirs lw).length →
    Cd pc ((dirs lw).zip zs) → Bl (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k →
    ∀ q : Call, q.OK (MS J) (_root_.Executable.labels exe).label →
      ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ l b w s c, lbl l = none →
        At exe endPc (R.callee (-(fr.size : Int) - 8) (-160) 8)
          (fun m => F m ∧ CallerCells R (-(fr.size : Int) - 8) (-160) 8 m ∧
            AllocCtx (MS J) (_root_.Executable.labels exe).label R fr.size (NJ (pc + Int64.ofNat zs.sum) zc) q m)
          (Spike.Lib.X64.Alloc.Ea (MS J') q l b w) s c →
        TP tp s → (MS J').xa l b w s c
  hstub : ∀ (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc k : Nat),
    getOps fr ([Scc.Lower.imm h, .imm kv, u].zip Scc.Emit.X64.argRegs) = .ok lw → zs.length = (dirs lw).length →
    Cd pc ((dirs lw).zip zs) → Bl (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k →
    ∀ q : Call, q.OK (MS J) (_root_.Executable.labels exe).label →
      ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ m0 σC c0', (HeldAb (_root_.Executable.labels exe).label (MS J') q lbl R fr.size
        (fun σC => (NJ (pc + Int64.ofNat zs.sum) zc) σC q.c0)).J σC c0' →
      StubHN (fun s c => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J') Dt (Ab lab) lbl lsize s c fs)
        (TakeK a rS) (MS J') exe endPc
        (R.callee (-(fr.size : Int) - 8 + -160 - 8) (-24) 16)
        (fun m => F m ∧ CKept R (-(fr.size : Int) - 8 + -160 - 8) (-24) 16 m0 m ∧
          Abs R ⟨-(fr.size : Int) - 8 + -160, []⟩ m0 σC) c0'

/-- **`AllocW2At` at `W₀ := W2`** for every allocation of a body at the code
`CdCLE … ra0`, the calls `BlC2L … fr ra0` and the immediates `Λ.imms`
(`allocW2_w2Full` at each): `allocW2_w2Full`'s allocation-independent
premises, the allocations' elements `elem2` (`hTn`), the ghosts `FrOk2` at
the frames (`hG0F`), and at each allocation (`AllocW2At`'s data) the rest
(`AllocPtW`, `hpt`); the walk facts from the resumption facts
(`PtC2.newBufW`). -/
theorem allocW2At_of {rS : Range} (hI : InstOk exe endPc cells lab μ own Tk (TakeK a rS) okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hprA : Scc.Cert.Rt.X64.Abort.abortIn cells = true) {Λ : Scc.Sem.Layout} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (h16 : fr.size % 16 = 0) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 8 + -160 - 32) (hhi : 16 ≤ R.hi) (hFS : FStable R F)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {L0 : Lbl} {ls0 : Lsize} {S0 : FragS isa} {Es : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {J : InvS} {ab : Option (State → Prop)} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    {fs : List TermRun.Frame}
    (hJ : ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs,
      StartsS ar L0 ls0 (Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt (Ab lab) a ab) S0 Es L ls s c fs → J L ls s c fs)
    (hRe : Reach ar L0 ls0 lbl lsize)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {ra0 : Int64} (hrs : ∀ r k, rsOf fr r = some k → R.Off k)
    (hmem : ∀ q : Call, q.OK (MS J) (_root_.Executable.labels exe).label →
      ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (MS J) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ q : Call, q.OK (MS J) (_root_.Executable.labels exe).label →
      ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (MS J) o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64)
    (hsz : ∀ q : Call, q.OK (MS J) (_root_.Executable.labels exe).label → ∀ l b old, lbl l = some b →
      (MS J).lo old → b = ar.heap + 16 * old + ar.off q.n q.τ → old + ar.units q.n q.τ ≤ ar.cells → q.n ≤ lsize l)
    {lcx : Scc.Lower.Ctx} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {T : Expr → Prop}
    {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hTn : ∀ x cn τ e, T (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs)
    (hpt : ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (x : String) (cn : At) (τ : Ty) (e : Expr)
      (env : Scc.Lower.Env) (n : Nat) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat))
      (tk : Ty) (kv : UInt64) (en em h : Nat), G0 c0 → T (.let_ x (.newBuf cn τ) e) →
      Spike.Lib.LowerNode.Fresh env n → Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]) →
      Spike.Lib.LowerShape.countsO lcx.obj τ = some (en, em) → Scc.Obj.header0 lcx.obj .array en em = some h →
      PtC2 lcx fr (CdCLE cells okPc ph lab ra0) (BlC2L cells okPc ph lab fr ra0) (_root_.Executable.labels exe).label
        Λ.imms T Lk kk pc env n lits cs bufs (.let_ x (.newBuf cn τ) e) →
      AllocPtW Λ μ p rd G own rS Tk ar L0 ls0 S0 Es J ab Dt lab a lbl lsize fs exe endPc R F fr
        (CdCLE cells okPc ph lab ra0) (BlC2L cells okPc ph lab fr ra0) fp ra tp c0 pc x cn τ e env lits cs bufs h kv (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)) :
    AllocW2At p lbl lsize lcx fr (CdCLE cells okPc ph lab ra0) (BlC2L cells okPc ph lab fr ra0)
      (fun lbl lsize s c => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt (Ab lab) lbl lsize s c fs) (TakeK a rS)
      exe endPc R F (MS J) fp ra tp G0 Λ.imms T Lk := by
  intro c0 pc kk x cn τ e env n lits cs bufs tk kv en em h hc0 hT hfr hat hco hhd hpc
  obtain ⟨htot, hlb, himm, hg, hsc, hIt, hIc, hlbe⟩ := PtC2.newBufW hpc
  have P := hpt c0 pc kk x cn τ e env n lits cs bufs tk kv en em h hc0 hT hfr hat hco hhd hpc
  exact allocW2_w2Full hI hA hph habk hpr hprA hown hf h1 h16 hR hR8 hl hh hlo hhi hFS hsub hfit hFO hp hJ hRe hfp
    hrs htot hlb himm (hG0F c0 hc0) (hTn x cn τ e hT) hfr P.hnr hIt hIc hlbe hg hat hsc P.hleaf P.hu P.hacc P.hms
    hmem hno hlt h64 P.hxa P.hxaF P.hstub hsz

end Of

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.PtC2.newBufW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.PtC2.newBufW

/-- info: 'Spike.Lib.LowerX64.allocW2At_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocW2At_of
