/-
**The setup block called by `scc_rt_main`, from the setup function's
segment** (AArch64, `Accepted2`): `h0_ofPlaceOK_setupFN`'s `hS`
(`SetupCallWS` at `SRetR`, `Spike/Lib/LowerA64/SetupCall2.lean`) from the
setup function's `FnSpecC2` (`Spike/Lib/LowerA64/ProgC2.lean`) and its
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
predicate `CxOk`, and `CalleePre2`'s other fields (the context, the
return address, the region's bounds, the ghosts, the blocks' and the
prologue's states inside `W`, the aborts). `main`'s call (`MainCallWSF`)
is not routed through `FnSpecC2` at the empty frames: its body's paths end
in held returns (`mainCallWSF_ofHeld`, `Spike/Lib/LowerA64/MainHeldA.lean`).
-/
import Spike.Lib.LowerA64.SetupCall2
import Spike.Lib.LowerA64.ProEdge2UN0
import Spike.Lib.LowerA64.MainExitF

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (LimOk WcG CallerCells)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
  {prog : List Directive} {endPc : Int64} {W : FragS isaLSE2} {K : State → State → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The setup block from the setup function's segment** (`SetupCallWS`
at `SRetR`, `setupCallWS_framed`): the callee's segment `CalleePre2.seg`
at the interface's entry `uN0` (`c`'s label, `hfn`), its edge by
`proEdge2_ofUN0` (see the module docstring). -/
theorem setupCallWS_ofFnSpec {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (c : FnCode2 exe prog endPc RaOk Cd i T d) (hs : FnSpecC2 W K p lbl lsize ms CxOk c)
    (hu : d.argTy = .unit) (hna : c.na = 0)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {ra : BitVec 64}
    {c0 : Ctl} {tp : UInt64} (hfn : fn = c.fn) (hZU : ZU = Int64.ofInt c.cx.frame)
    (hcE : ∀ cE fr, CallTo p c0 cE fr → cE = ⟨d.body, [(d.arg, d.argTy, [])], none⟩)
    (hms : ∀ fr a Z', LimOk (ms []) F exe endPc a Z' → LimOk (ms [fr]) F exe endPc a Z')
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK →
      (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 → FStable (R.callee (-Z.toInt) (-D) 0) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
      ∀ (g : WcG) (fr : TermRun.Frame), g.ra = ra → g.tp = tp → CallTo p c0 g.c0 fr →
      (R.callee (-Z.toInt) (-D) 0).base = g.sp →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isaLSE2),
        (ProEdge2 p lbl lsize (ms [fr]) F' c g.fp g.ra tp g.c0
            (Spike.Lib.A64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F exe endPc fn ZU g).J →
          CalleePre2 W K p lbl lsize ms CxOk c (R.callee (-Z.toInt) (-D) 0) F' [fr] g.fp g.ra tp G0 Ab
            (Spike.Lib.A64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F exe endPc fn ZU g).J g.c0) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.A64.Rt.SetupCallWS W K p lbl ms exe endPc R F fn Z D ZU (SRetR lbl d.retTy) ra c0 tp := by
  refine setupCallWS_framed fun F' hR0 hal hF' hFF g fr hra htp hct hbase => ?_
  obtain ⟨G0, Ab, hP, hAb⟩ := hpre F' hR0 hal hF' hFF g fr hra htp hct hbase
  have hsp : Scc.Cert.Code1A64.spills c.cx (Spike.Lib.LowerShape.paramsR d 0) = some c.ps := hna ▸ c.hsp
  have hedge := proEdge2_ofUN0 (p := p) (lbl := lbl) (lsize := lsize) c hu (hna ▸ c.henv) c.hlits hsp
    (hcE _ _ hct) hZU (hms fr) (fun m hm => (hFF m hm).1)
    (J := (Spike.Lib.A64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F exe endPc fn ZU g).J)
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
    (h : ∀ cP : Ctl, (∃ rs, Pre cP rs) → Spike.Lib.A64.Rt.MainCallWSF W K p lbl ms exe endPc R F fn Z D ZU
      (fun c rs => Pre c rs ∧ c = cP) Post ra tp) :
    Spike.Lib.A64.Rt.MainCallWSF W K p lbl ms exe endPc R F fn Z D ZU Pre Post ra tp := by
  intro F' hR0 hal hF' hFF g hra htp
  refine (SegWS.exists_pre fun (q : {cP // ∃ rs, Pre cP rs}) => h q.1 q.2 F' hR0 hal hF' hFF g hra htp).mono_pre ?_
  rintro s c fs ⟨⟨he, hn, hd, hpc, σ, hA, hF, ⟨hP, h29, h30, hsp, htp⟩, hL⟩, rfl⟩
  exact ⟨⟨c, _, hP⟩, ⟨he, hn, hd, hpc, σ, hA, hF, ⟨⟨hP, rfl⟩, h29, h30, hsp, htp⟩, hL⟩, rfl⟩

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.LowerA64.setupCallWS_ofFnSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.setupCallWS_ofFnSpec

/-- info: 'Spike.Lib.LowerA64.MainCallWSF.ofCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.MainCallWSF.ofCtl
