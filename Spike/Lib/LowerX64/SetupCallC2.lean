/-
**The setup block called by `scc_rt_main`, from the setup function's
segment** (x86-64, `Accepted2`; the twin of
`Spike/Lib/LowerA64/SetupCallC2.lean`): `h0_ofPlaceOK_setupFN`'s `hS`
(`SetupCallWS` at `SRetR`, `Spike/Lib/LowerX64/SetupCall2.lean`) from the
setup function's `FnSpecC2` (`Spike/Lib/LowerX64/ProgC2.lean`) and its
context's premises at each call (`CalleePre2`), the prologue's edge into
the body (`CalleePre2.hedge`) discharged at the interface's entry `uN0`
(`proEdge2_ofUN0`).

- `setupCallWS_ofFnSpec`: at every frame condition `F'`, ghost `g` and
  call frame `fr` of the interface, a context's premises for the setup
  function's code facts `c` but its edge (`hpre`, `CalleePre2` given
  `ProEdge2`), at the entry invariant of `uN0` and some aborts `Ab` never
  ending; with `c`'s function the interface's (`hfn`), its parameter
  `Unit` with no words (`hu`, `hna`), the limit room its frame (`hZU`), the
  call's entry control `d`'s body on the unit (`hcE`) and the limit word's
  facts at the empty frames carried to `[fr]` (`hms`), `SetupCallWS` at
  `SRetR` at `d`'s return type;
- `MainCallWSF.ofCtl`: `MainCallWSF` at `Pre` from the interfaces with the
  source control pinned to each control meeting `Pre`.

Left open (per call): `FnSpecC2` of the setup function at the context
predicate `CxOk`, and `CalleePre2`'s other fields. `main`'s call
(`MainCallWSF`) is not routed through `FnSpecC2` at the empty frames: its
body's paths end in held returns (`mainCallWSF_ofHeld`,
`Spike/Lib/LowerX64/MainHeldX.lean`).
-/
import Spike.Lib.LowerX64.SetupCall2
import Spike.Lib.LowerX64.ProEdge2UN0
import Spike.Lib.LowerX64.MainExitF

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (CallTo)
open Spike.Lib.X64.Flow.Ret0 (LimOk WcG CallerCells)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
  {cells : List (Directive × Nat)} {endPc : Int64} {W : FragS isa} {K : State → State → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The setup block from the setup function's segment** (`SetupCallWS`
at `SRetR`, `setupCallWS_framed`): the callee's segment `CalleePre2.seg`
at the interface's entry `uN0` (`c`'s label, `hfn`), its edge by
`proEdge2_ofUN0` (see the module docstring). -/
theorem setupCallWS_ofFnSpec {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (hs : FnSpecC2 W K p lbl lsize ms CxOk c)
    (hu : d.argTy = .unit) (hna : c.na = 0)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {ra : BitVec 64}
    {c0 : Ctl} {tp : UInt64} (hfn : fn = c.fn) (hZU : ZU = Int64.ofInt c.fr.size)
    (hcE : ∀ cE fr, CallTo p c0 cE fr → cE = ⟨d.body, [(d.arg, d.argTy, [])], none⟩)
    (hms : ∀ fr a Z', LimOk (ms []) F a Z' → LimOk (ms [fr]) F a Z')
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ (g : WcG) (fr : TermRun.Frame), g.ra = ra → g.tp = tp → CallTo p c0 g.c0 fr →
      (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isa),
        (ProEdge2 p lbl lsize (ms [fr]) F' c g.fp g.ra tp g.c0
            (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F fn ZU g).J →
          CalleePre2 W K p lbl lsize ms CxOk c (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' [fr] g.fp g.ra tp G0
            Ab (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F fn ZU g).J g.c0) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.SetupCallWS W K p lbl ms exe endPc R F fn Z D ZU (SRetR lbl d.retTy) ra c0 tp := by
  refine setupCallWS_framed fun F' hR0 hF' hFF g fr hra htp hct hbase => ?_
  obtain ⟨G0, Ab, hP, hAb⟩ := hpre F' hR0 hF' hFF g fr hra htp hct hbase
  obtain ⟨zs, hsp⟩ := c.hsp
  rw [hna] at hsp
  have hedge := proEdge2_ofUN0 (p := p) (lbl := lbl) (lsize := lsize) c hu (hna ▸ c.henv) c.hlits hsp
    (hcE _ _ hct) hZU (hms fr) (fun m hm => (hFF m hm).1)
    (J := (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F fn ZU g).J)
    fun _ _ h => h
  rw [htp] at hedge
  have H := (hP hedge).seg hs (List.cons_ne_nil _ _)
  subst hfn
  exact ⟨Ab, g.c0, H, hAb⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **`MainCallWSF` control by control**: the interface at `Pre` from the
interfaces at `Pre` with the source control pinned to each `cP` some
registers meet `Pre` at (the entry at `uNM` reassembled with
`SegWS.exists_pre` over those controls). -/
theorem MainCallWSF.ofCtl {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64}
    {Pre : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop} {ra : BitVec 64}
    {tp : UInt64}
    (h : ∀ cP : Ctl, (∃ rs, Pre cP rs) → Spike.Lib.X64.Rt.MainCallWSF W K p lbl ms exe endPc R F fn Z D ZU
      (fun c rs => Pre c rs ∧ c = cP) Post ra tp) :
    Spike.Lib.X64.Rt.MainCallWSF W K p lbl ms exe endPc R F fn Z D ZU Pre Post ra tp := by
  intro F' hR0 hF' hFF g hra htp
  refine (SegWS.exists_pre fun (q : {cP // ∃ rs, Pre cP rs}) => h q.1 q.2 F' hR0 hF' hFF g hra htp).mono_pre ?_
  rintro s c fs ⟨⟨he, hn, hd, hpc, σ, hA, hF, ⟨hP, h29, h30, hsp, htp⟩, hL⟩, rfl⟩
  exact ⟨⟨c, _, hP⟩, ⟨he, hn, hd, hpc, σ, hA, hF, ⟨⟨hP, rfl⟩, h29, h30, hsp, htp⟩, hL⟩, rfl⟩

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.LowerX64.setupCallWS_ofFnSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.setupCallWS_ofFnSpec

/-- info: 'Spike.Lib.LowerX64.MainCallWSF.ofCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.MainCallWSF.ofCtl
