/-
**A source call at any index arguments on x86-64**: `X64CallS`'s source call
(`CallTo`, `CallGF`, `CallGF.ret`) at any index arguments, so hello's worker's call of `print`
(`let u = call print [q] sl in e`, the frame `uFrame` pushed) is taken by the same frame step.

- `CallToI`, `CallToI.step`: `CallTo` with the index arguments free (`FrameStep.call` ignores them).
- `CallGFI`, `CallGFI.ret`: `CallGF`, `CallGF.ret` at `CallToI` (the callee's entry offset `e0`, the
  return address pushed below the caller's stack pointer).

## Differences from the AArch64 version

`Spike/Lib/A64HelloCallTCS.lean`.

- The callee's frame is seen at `nC.o.sp - e0` (`e0` the callee's entry offset: x86-64's `call` pushes the
  return address), as in `X64CallS.CallGF`; the AArch64 version has `e0 = 0`.
- The return's abstract state also keeps the vector registers (`σR.zmms = σx.zmms`), as in `X64CallS`.
- Only the live constants are twinned: `call_ndTCS` and `CallTo.toI` are not (the x86-64 call over
  `SegTCSX` is `Spike/Lib/X64HelloCallTCSX.lean`'s `call_ndTCSX`, stated directly).
-/
import Spike.Lib.X64CallS

namespace Spike.Lib.X64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64

/-- **A source call at any index arguments** (`CallTo` with `is` free;
`FrameStep.call` ignores them): hello's `let u = call print [q] sl in e`. -/
def CallToI (p : Prog) (c cE : Ctl) (fr : TermRun.Frame) : Prop :=
  ∃ (x f : String) (is : List String) (a : CoreTerm.At) (e : Expr) (d : Decl) (t : Ty) (ws : List TermRun.Word),
    c.term = .let_ x (.call f is a []) e ∧ p.find? (·.name == f) = some d ∧
    TermRun.evalAt c.env a = some (t, ws) ∧ cE = ⟨d.body, [(d.arg, d.argTy, ws)], none⟩ ∧
    fr = ⟨x, e, c.env, [], d.retTy⟩

/-- A source call at any index arguments is a frame step. -/
theorem CallToI.step {p : Prog} {c cE : Ctl} {fr : TermRun.Frame} (h : CallToI p c cE fr)
    (fs : List TermRun.Frame) : FrameStep p (c, fs) (cE, fr :: fs) := by
  obtain ⟨x, f, is, a, e, d, t, ws, ht, hd, ha, rfl, rfl⟩ := h
  exact .call ht hd ha

section Fn

variable {p : Prog} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **The callee's ghost frame condition at a source call** (`CallGF` at `CallToI`):
at the ghost `G` (the machine data `G.1` and abstract state `G.2.1` at the
call node `nC`, the caller's control `G.2.2.1`, the callee's entry control
`G.2.2.2.1` and frame `G.2.2.2.2.1`, the callee's parameters `G.2.2.2.2.2`),
the caller's `F`, the caller's cells outside the callee's region
`R.callee (nC.o.sp - e0) lo' hi'` as in `G.1`, the caller's state at `nC` (`Abs`,
`nC.J`), its control calling (`CallToI`) and the callee's entry node holding
at the callee's control. -/
def CallGFI {γ : Type _} (p : Prog) (R : Region) (F : MachineData → Prop) (nC : ND) (e0 : Int) (lo' hi' : Int)
    (Ne : γ → ND) (G : MachineData × AS × Ctl × Ctl × TermRun.Frame × γ) (m : MachineData) : Prop :=
  F m ∧ (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) →
      Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt G.1.dmem (R.addr k) 8) ∧
    Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ CallToI p G.2.2.1 G.2.2.2.1 G.2.2.2.2.1 ∧
    (Ne G.2.2.2.2.2).J (enter (nC.o.sp - e0) G.2.1) G.2.2.2.1

/-- **The return to the caller from an exit under the ghost frame
condition** (`CallGF.ret` at `CallToI`): at an exit `Ex g x` of the callee in its
region, its frame condition `CallGFI` at the ghost `G`, the source runs from
the callee's control at the frames `G`'s frame `:: fs` back to `fs`
(`hret`), landing at a caller's node at `F₂` (the caller's abstract state
rebuilt as `leave` of the call's and the exit's). -/
theorem CallGFI.ret {F₂ : MachineData → Prop} {nC : ND} {γ : Type _} {κ' : Sort _} {e0 lo' hi' : Int}
    {Ne : γ → ND} {Ex : γ → κ' → ND} {fs : List TermRun.Frame}
    (hret : ∀ g x σC c cE fr σx c' (σR : AS), nC.J σC c → CallToI p c cE fr →
      (Ne g).J (enter (nC.o.sp - e0) σC) cE →
      (Ex g x).J σx c' → σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      ∃ c'', FrameRun p (c', fr :: fs) (c'', fs) ∧
        Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c'')
    {G : MachineData × AS × Ctl × Ctl × TermRun.Frame × γ} {x : κ'} {s : State} {c : Ctl}
    (hAt : At exe endPc (R.callee (nC.o.sp - e0) lo' hi') (CallGFI p R F nC e0 lo' hi' Ne G)
      (Ex G.2.2.2.2.2 x) s c)
    (hF₂ : F₂ s.st.1) :
    ∃ c'', FrameRun p (c, G.2.2.2.2.1 :: fs) (c'', fs) ∧ Next exe endPc R F₂ N E s c'' := by
  obtain ⟨mC, σC, cC, cE, fr, g⟩ := G
  obtain ⟨he, hn, hdc, hpc, σx, hAx, ⟨-, hDF, hAC, hJC, hCT, hJE⟩, hJx⟩ := hAt
  let kc := (nC.o.sp - e0)
  let R' := R.callee kc lo' hi'
  have hAR : Abs R ⟨kc + (Ex g x).o.sp, []⟩ s.st.1 (leave R' kc σC σx) := by
    refine ⟨hAx.regs, hAx.zmms, hAx.status, ?_, fun k hk => ?_⟩
    · intro r k' hr
      obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
      have := hAx.so .rsp (Ex g x).o.sp (by simp [SO.get])
      simp only [leave] at this ⊢
      rw [this, Region.callee_addr]
    · by_cases hin : R'.Off (k - kc)
      · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
        refine ⟨j, ?_, ?_⟩
        · rw [Region.callee_addr, show kc + (k - kc) = k by omega] at hj; exact hj
        · simp only [leave]; rw [ite_eq_left hin]; exact hv
      · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
        refine ⟨j, ?_, ?_⟩
        · rw [hDF k hk hin]
          exact hj
        · simp only [leave]; rw [ite_eq_right hin]; exact hv
  obtain ⟨c'', hrun, hL⟩ := hret g x σC cC cE fr σx c (leave R' kc σC σx) hJC hCT hJE hJx rfl rfl rfl
    (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
  have hs : s = { s with st := (s.st.1, (Ex g x).pc) } := by rw [← hpc]
  refine ⟨c'', hrun, ?_⟩
  rw [hs]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hAR hF₂⟩
  · exact .inr ⟨y, hy.at he hn hdc hAR hF₂⟩

end Fn

end Spike.Lib.X64.Flow

/-- info: 'Spike.Lib.X64.Flow.CallToI.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.CallToI.step

/-- info: 'Spike.Lib.X64.Flow.CallGFI.ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.CallGFI.ret
