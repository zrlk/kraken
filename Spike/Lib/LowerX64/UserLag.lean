/-
**`scc_rt_main`'s user function at depth, held back at its ghost**
(x86-64, H7a calls): `userCallWS_of_exitC` (`Spike/Lib/LowerX64/ProgC.lean`)
with the user function's segment over the source's real pairs (inside
`BodyWS0`, `Spike/Lib/LowerX64/BodyWS1.lean`) lagged at the ghost `c0` with no
frame (`bodyWS0_lag`), so the interface is inside `SFactsS … Dt`; its aborts
discharged after the lag (`LagS p (· = c0) Ab`, e.g. `hab_ofS`,
`Spike/Lib/LowerX64/AbortCallS.lean`); the return after the source's frame
run back to the ghost's depth, at the held-back ghost (`SegWS.post_run`).

- `SFactsS.dt_mono`: `SFactsS` at a weaker write tail.
- `SegWS.mono_W`: a segment inside a larger fragment.
- `userCallWS_of_exitCL`: the interface inside `SFactsS … Dt` from the
  segment inside `BodyWS0` (`hseg`), the held-back aborts (`hAb`) and the
  return (`hret`).
-/
import Spike.Lib.LowerX64.ProgC
import Spike.Lib.LowerX64.BodyWS1

namespace Spike.Lib.X64ConsumerS

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64

/-- **`SFactsS` at a weaker write tail.** -/
theorem SFactsS.dt_mono {Λ : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {p : Prog} {own : OwnS}
    {rS : Scc.Sem.Range} {Tk : State → Prop} {lbl : X64Consumer.Lbl} {cells ctr : Nat} {s : State}
    {c : Ctl} {fs : List TermRun.Frame} {Dt Dt' : State → Prop}
    (h : SFactsS Λ μ p own rS Tk lbl cells ctr s c fs Dt) (hD : ∀ s, Dt s → Dt' s) :
    SFactsS Λ μ p own rS Tk lbl cells ctr s c fs Dt' :=
  { h with wrTail := fun ha fd buf n hd => hD s (h.wrTail ha fd buf n hd) }

end Spike.Lib.X64ConsumerS

namespace Spike.Lib.SegWS

open CoreLang CoreTerm
open Kraken.Promising

variable {I : ISA} {W W' : FragS I} {K : I.State → I.State → Prop} {p : Prog}
  {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I} {P Q : FragS I}

/-- **A segment inside a larger fragment.** -/
theorem mono_W (h : SegWS W K p lbl ms P Q) (hW : ∀ s c fs, W s c fs → W' s c fs) : SegWS W' K p lbl ms P Q :=
  let ⟨inv, hP, hiW, hcl⟩ := h
  ⟨inv, hP, fun s c fs h => hW s c fs (hiW s c fs h), hcl⟩

end Spike.Lib.SegWS

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer (Own Lbl)
open Spike.Lib.X64ConsumerS (SFactsS)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {K : State → State → Prop}

/-- **`scc_rt_main`'s user function at depth inside `SFactsS … Dt`, held
back at its ghost** (`UserCallWS`): at every frame condition and ghost of
the interface, a segment over the source's real pairs (inside `BodyWS0` at
the ghost `c0`) from the entry `uN0` to the exits `ExitC` of a function
(`hseg`, e.g. `main`'s `FnSpecC` at `[]`; given the entry's `%rsp`, the
ghost's `sp`, at the callee region's base), lagged at `c0` (`bodyWS0_lag`,
for an `Accepted1` program, `hp`, under memory sides agreeing with depth 0's
whose kernel model is `Scc.Sem.X64.abi`, `hms`, `hK`, the words owned at the
frames owned at depth 0 where a row reads the runtime's memory, `hown`);
its aborts held back at `c0` never ending (`hAb`, e.g. `hab_ofS`) and its return node past `ret`
(after the source's frame run from the ghost) the interface's return `uNx`
(`hret`) at the held-back ghost `c0` (from which the source's frame run
reaches the return's control). -/
theorem userCallWS_of_exitCL {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range} {Tk : State → Prop}
    {lb : Lbl} {cl ctr : Nat} {Dt : State → Prop} (hp : Scc.Lower.Accepted1 p = true)
    (hK : (ms []).K = some Scc.Sem.X64.abi) (hms : MsAgree ms)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int}
    {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {ra : BitVec 64} {c0 : Ctl} {tp : UInt64}
    (hown : ∀ s c fs, BodyWS0 Λ μ p own rS Tk lb cl ctr c0 s c fs → ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) →
      ∀ L, RtReads s L → ∀ w, (L, w) ∈ (ms fs₁).own s → (L, w) ∈ (ms []).own s)
    (hseg : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ Spike.Lib.X64.Flow.Ret0.CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ g : Spike.Lib.X64.Flow.Ret0.WcG, g.ra = ra → g.c0 = c0 → g.tp = tp →
      (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp →
      ∃ (Ab : FragS isa) (fp ra' : BitVec 64) (c0' : Ctl),
        SegWS (BodyWS0 Λ μ p own rS Tk lb cl ctr c0) K p lbl ms
          ((At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
            (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F fn ZU g)).at [])
          (ExitC p lbl exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' fp ra' tp c0' [] Ab) ∧
        SegWS (fun s c fs => SFactsS Λ μ p (fun s _ => own s) rS Tk lb cl ctr s c fs Dt) K p lbl ms
          (LagS p (· = c0) Ab) (fun _ _ _ => False) ∧
        ∀ c1 s c, FrameRun p (c0, []) (c, []) → FrameRun p (c0', []) (c1, []) →
          At exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' ((retN p lbl fp ra' c1).withTp tp) s c →
          At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' (Spike.Lib.X64.Rt.uNx Post g) s c0) :
    Spike.Lib.X64.Rt.UserCallWS (fun s c fs => SFactsS Λ μ p (fun s _ => own s) rS Tk lb cl ctr s c fs Dt) K p lbl
      ms exe endPc R F fn Z D ZU Post ra c0 tp := by
  intro F' hR0 hF' hFF g hra hc htp
  by_cases hbase : (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp
  case neg =>
    refine SegWS.empty fun s c fs h => hbase ?_
    obtain ⟨⟨-, -, -, -, σ, hA, -, ⟨-, -, -, hsp, -⟩, -⟩, -⟩ := h
    have := hA.so .rsp 0 (by simp [SO.get, Spike.Lib.X64.Rt.uN0])
    rw [← hsp]
    simpa [Region.addr, Reg64s.get64] using this.symm
  obtain ⟨Ab, fp, ra', c0', h1, hAb, hret⟩ := hseg F' hR0 hF' hFF g hra hc htp hbase
  have hL := (bodyWS0_lag hp hK hms hown h1).mono_W fun _ _ _ h => h.dt_mono (Dt' := Dt) fun _ h => h.elim
  refine SegWS.post_run ((SegWS.seq_left (Q := LagS p (· = c0) Ab)
    (E := Pend p ((At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' (Spike.Lib.X64.Rt.uNx Post g)).at []))
    ((hL.mono_pre ?_).mono_post ?_) hAb).mono_post ?_)
  · intro s c fs h
    obtain ⟨hA, rfl⟩ := h
    obtain ⟨-, -, -, -, σ, -, -, ⟨⟨hcg, -⟩, -⟩⟩ := id hA
    exact ⟨rfl, hcg.trans hc, c, [], ⟨hA, rfl⟩, .refl _⟩
  · intro s c fs h
    obtain ⟨rfl, rfl, c', fs', hx, hr⟩ := h
    rcases hx with ⟨rfl, c1, hr1, hA⟩ | hx
    · exact .inr ⟨_, [], .refl _, hret c1 s c' hr hr1 hA, rfl⟩
    · exact .inl ⟨rfl, rfl, c', fs', hx, hr⟩
  · exact fun _ _ _ h => h.elim False.elim id

end Spike.Lib.LowerX64
