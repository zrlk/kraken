/-
**`scc_rt_main`'s user function at depth, held back at its ghost**
(AArch64, H7a calls): the twin of `Spike/Lib/LowerX64/UserLag.lean`. The
user function's segment over the source's real pairs (inside `BodyWS0`,
`Spike/Lib/LowerA64/BodyWS1.lean`) to its exits `ExitC`
(`Spike/Lib/LowerA64/BodyC.lean`) is lagged at the ghost `c0` with no frame
(`bodyWS0_lag`), so the interface `UserCallWS` (`Spike/Lib/Rt/A64SegsS.lean`)
is inside `SFactsS … Dt`; its aborts are discharged after the lag
(`LagS p (· = c0) Ab`, e.g. `Spike/Lib/LowerA64/AbortCallS.lean`); the return
after the source's frame run back to the ghost's depth, at the held-back
ghost (`SegWS.post_run`).

- `SFactsS.dt_mono`: `SFactsS` at a weaker write tail.
- `userCallWS_of_exitCL`: the interface inside `SFactsS … Dt` from the
  segment inside `BodyWS0` (`hseg`), the held-back aborts (`hAb`) and the
  return (`hret`).
-/
import Spike.Lib.LowerA64.BodyC
import Spike.Lib.LowerA64.BodyWS1
import Spike.Lib.LowerA64.StartSegSG

namespace Spike.Lib.A64ConsumerS

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64

/-- **`SFactsS` at a weaker write tail.** -/
theorem SFactsS.dt_mono {Λ : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {p : Prog} {own : OwnS}
    {rS : Scc.Sem.Range} {Tk : State → Prop} {lbl : A64Consumer.Lbl} {cells ctr : Nat} {s : State}
    {c : Ctl} {fs : List TermRun.Frame} {Dt Dt' : State → Prop}
    (h : SFactsS Λ μ p own rS Tk lbl cells ctr s c fs Dt) (hD : ∀ s, Dt s → Dt' s) :
    SFactsS Λ μ p own rS Tk lbl cells ctr s c fs Dt' :=
  { h with wrTail := fun ha fd buf n hd => hD s (h.wrTail ha fd buf n hd) }

end Spike.Lib.A64ConsumerS

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Sem (Marks Range)
open Spike.Lib.A64Consumer (Own Lbl)
open Spike.Lib.A64ConsumerS (SFactsS)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {K : State → State → Prop}

/-- **`scc_rt_main`'s user function at depth inside `SFactsS … Dt`, held
back at its ghost** (`UserCallWS`): at every frame condition and ghost of
the interface, a segment over the source's real pairs (inside `BodyWS0` at
the ghost `c0`) from the entry `uN0` to the exits `ExitC` of a function in
the callee's region (`hseg`; given the entry's `sp`, the ghost's, at the
callee region's base), lagged at `c0` (`bodyWS0_lag`, for an
`Accepted1` program, `hp`, under memory sides agreeing with depth 0's whose
kernel model is `Scc.Sem.A64.abi`, `hms`, `hK`, the words owned at the
frames owned at depth 0 where a row reads the runtime's memory, `hown`); its
aborts held back at `c0` never ending (`hAb`) and its return node past `ret`
(after the source's frame run from the ghost) the interface's return `uNx`
(`hret`) at the held-back ghost `c0` (from which the source's frame run
reaches the return's control). -/
theorem userCallWS_of_exitCL {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range} {Tk : State → Prop}
    {lb : Lbl} {cl ctr : Nat} {Dt : State → Prop} (hp : Scc.Lower.Accepted1 p = true)
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hms : MsAgree ms)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int}
    {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {ra : BitVec 64} {c0 : Ctl} {tp : UInt64}
    (hown : ∀ s c fs, BodyWS0 Λ μ p own rS Tk lb cl ctr c0 s c fs → ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) →
      ∀ L, RtReads s L → ∀ w, (L, w) ∈ (ms fs₁).own s → (L, w) ∈ (ms []).own s)
    (hseg : ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK →
      (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 → FStable (R.callee (-Z.toInt) (-D) 0) F' →
      (∀ m, F' m → F m ∧ Spike.Lib.A64.Flow.Ret0.CallerCells R (-Z.toInt) (-D) 0 m) →
      ∀ g : Spike.Lib.A64.Flow.Ret0.WcG, g.ra = ra → g.c0 = c0 → g.tp = tp →
      (R.callee (-Z.toInt) (-D) 0).base = g.sp →
      ∃ (Ab : FragS isaLSE2) (fp ra' : BitVec 64) (c0' : Ctl),
        SegWS (BodyWS0 Λ μ p own rS Tk lb cl ctr c0) K p lbl ms
          ((At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
            (Spike.Lib.A64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F exe endPc fn ZU g)).at [])
          (ExitC p lbl exe endPc (R.callee (-Z.toInt) (-D) 0) F' fp ra' tp c0' [] Ab) ∧
        SegWS (fun s c fs => SFactsS Λ μ p (fun s _ => own s) rS Tk lb cl ctr s c fs Dt) K p lbl ms
          (LagS p (· = c0) Ab) (fun _ _ _ => False) ∧
        ∀ c1 s c, FrameRun p (c0, []) (c, []) → FrameRun p (c0', []) (c1, []) →
          At exe endPc (R.callee (-Z.toInt) (-D) 0) F' ((retN p lbl fp ra' c1).withTp tp) s c →
          At exe endPc (R.callee (-Z.toInt) (-D) 0) F' (Spike.Lib.A64.Rt.uNx Post g) s c0) :
    Spike.Lib.A64.Rt.UserCallWS (fun s c fs => SFactsS Λ μ p (fun s _ => own s) rS Tk lb cl ctr s c fs Dt) K p
      lbl ms exe endPc R F fn Z D ZU Post ra c0 tp := by
  intro F' hR0 hal hF' hFF g hra hc htp
  by_cases hbase : (R.callee (-Z.toInt) (-D) 0).base = g.sp
  case neg =>
    refine SegWS.empty fun s c fs h => hbase ?_
    obtain ⟨⟨-, -, -, -, σ, hA, -, ⟨-, -, -, hsp, -⟩, -⟩, -⟩ := h
    have := hA.so .SP 0 (by simp [SO.get, Spike.Lib.A64.Rt.uN0])
    rw [← hsp]
    simpa [Region.addr, Reg64s.getRegOrSp64] using this.symm
  obtain ⟨Ab, fp, ra', c0', h1, hAb, hret⟩ := hseg F' hR0 hal hF' hFF g hra hc htp hbase
  have hL := segWS_wmono (bodyWS0_lag hp hK hms hown h1) fun _ _ _ h => h.dt_mono (Dt' := Dt) fun _ h => h.elim
  refine SegWS.post_run ((SegWS.seq_left (Q := LagS p (· = c0) Ab)
    (E := Pend p ((At exe endPc (R.callee (-Z.toInt) (-D) 0) F' (Spike.Lib.A64.Rt.uNx Post g)).at []))
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

end Spike.Lib.LowerA64
