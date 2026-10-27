/-
**The setup block called by `scc_rt_main`, from its body's exits by
placements** (AArch64, `Accepted2`; the twin of
`Spike/Lib/LowerX64/SetupCall2.lean`): the framed interface `SetupCallWS`
(`Spike/Lib/Rt/A64MainSS.lean`, the setup function's body run in the frame
`fr` its call pushes) at the post `SRetR` at the body's `ret`, from a
segment of the setup function's body to its exits `ExitC2SL` at `[fr]` at
its result type, whose aborts never end; and the bridge `hPS` of the
`h0` wrappers: the `ret` pops `fr` into the caller's continuation, the
post `SPostC` there.

- `SRetR`: the setup call's post at the body's `ret`: its words at the
  result type `ty` placed in the return registers (`RetJS` at the
  registers' `x29`/`x30`, `RetL ty`);
- `uPostSR_ret`: the return's exit by placements past `ret` in the callee
  region is the interface's return `uNxS` at `SRetR`, the thread pointer
  the ghost's, `sp` the region's base (`hbase`);
- `setupCallWS_framed`: `SetupCallWS` at `SRetR` from a segment from the
  interface's entry `uN0` at `[fr]` to `ExitC2SL` at `ty` at `[fr]`, its
  aborts never ending;
- `SPostC`: the post at the caller's continuation: the control the `ret` of
  a `SRetR` control pops the call's frame into, with the returned words
  bound to the call's variable;
- `hPS_framed`: from `SRetR` at the `ret`, the frame step back to `[]` lands
  in `SPostC` (`FrameStep.ret`).
-/
import Spike.Lib.LowerA64.MainCall2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.LowerNode (RetL)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {W : FragS isaLSE2} {K : State → State → Prop}

/-- **The setup call's post at the body's `ret`**: the control's returned
words at the result type `ty` placed in the registers `regs`' return
registers (`RetJS` at `regs`' `x29`/`x30`, `RetL ty`). -/
def SRetR (lbl : WeakMem.AllocLabel → Option Nat) (ty : Ty) (c : Ctl) (regs : Reg64s) : Prop :=
  ∃ σ : AS, σ.regs = regs ∧ RetJS lbl regs.X29.toBitVec regs.X30.toBitVec σ c ∧ RetL ty c

/-- **The setup function's return at the interface's post**: the return's
exit by placements at `ty` past `ret` in the callee region, at the ghost's
thread pointer (`htp`), is the interface's return `uNxS` at `SRetR`, `sp`
at the entry's `sp` the region's base (`hbase`). -/
theorem uPostSR_ret {R : Region} {F : MachineData → Prop} {g : Spike.Lib.A64.Flow.Ret0.WcG} {c0 c : Ctl}
    {s : State} {tp : UInt64} {ty : Ty} (hbase : R.base = g.sp) (htp : tp = g.tp)
    (hA : At exe endPc R F ((retNSL p lbl g.fp g.ra c0 ty).withTp tp) s c) :
    At exe endPc R F (Spike.Lib.A64.Rt.uNxS (SRetR lbl ty) g) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨⟨hJ, -⟩, hL⟩, htp'⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h29, h30⟩ := id hJ
  have hJ' : RetJS lbl σ.regs.X29.toBitVec σ.regs.X30.toBitVec σ c := by rw [h29, h30]; exact hJ
  have hsp := hA.so .SP 0 rfl
  refine ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨σ, rfl, hJ', hL⟩, h29, h30, ?_, htp'.trans htp⟩
  rw [← hbase]
  simpa [Region.addr, Reg64s.getRegOrSp64] using hsp

/-- **The framed setup block, from its exits** (`SetupCallWS` at `SRetR`):
at every frame condition, ghost `g` and call frame `fr` of the interface
with the callee region's base the entry's `sp`, a segment inside `W` at
`[fr]` from the entry `uN0` to the setup function's exits `ExitC2SL` at its
result type `ty` at `[fr]` with `g`'s frame pointer and return address and
the thread pointer `tp` (`hseg`), and one from its aborts `Ab` to nothing;
the return past `ret` is `uNxS` at `SRetR` (`uPostSR_ret`). -/
theorem setupCallWS_framed {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int}
    {ZU : Int64} {ty : Ty} {ra : BitVec 64} {c0 : Ctl} {tp : UInt64}
    (hseg : ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK →
      (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 → FStable (R.callee (-Z.toInt) (-D) 0) F' →
      (∀ m, F' m → F m ∧ Spike.Lib.A64.Flow.Ret0.CallerCells R (-Z.toInt) (-D) 0 m) →
      ∀ (g : Spike.Lib.A64.Flow.Ret0.WcG) (fr : TermRun.Frame), g.ra = ra → g.tp = tp → CallTo p c0 g.c0 fr →
      (R.callee (-Z.toInt) (-D) 0).base = g.sp →
      ∃ (Ab : FragS isaLSE2) (c0' : Ctl),
        SegWS W K p lbl ms
          ((At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
            (Spike.Lib.A64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F exe endPc fn ZU g)).at [fr])
          (ExitC2SL p lbl exe endPc (R.callee (-Z.toInt) (-D) 0) F' g.fp g.ra tp c0' [fr] ty Ab) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.A64.Rt.SetupCallWS W K p lbl ms exe endPc R F fn Z D ZU (SRetR lbl ty) ra c0 tp := by
  intro F' hR0 hal hF' hFF g fr hra htp hct
  by_cases hbase : (R.callee (-Z.toInt) (-D) 0).base = g.sp
  case neg =>
    refine SegWS.empty fun s c fs h => hbase ?_
    obtain ⟨⟨-, -, -, -, σ, hA, -, ⟨-, -, -, hsp, -⟩, -⟩, -⟩ := h
    have := hA.so .SP 0 (by simp [SO.get, Spike.Lib.A64.Rt.uN0])
    rw [← hsp]
    simpa [Region.addr, Reg64s.getRegOrSp64] using this.symm
  obtain ⟨Ab, c0', h1, hAb⟩ := hseg F' hR0 hal hF' hFF g fr hra htp hct hbase
  refine (SegWS.seq_left (Q := Ab) (E := (At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
      (Spike.Lib.A64.Rt.uNxS (SRetR lbl ty) g)).at [fr]) (h1.mono_post fun s c fs h => ?_) hAb).mono_post
      fun s c fs h => ?_
  · rcases h with ⟨rfl, c1, -, hA⟩ | h
    · exact .inr ⟨uPostSR_ret hbase htp.symm hA, rfl⟩
    · exact .inl h
  · exact h.elim False.elim id

/-- **The setup call's post at the caller's continuation**: `c` is the
control the `ret` of a control `cr` with `SRetR` at `regs` pops the frame
of a call from `c0` into: the call's continuation term, the returned words
bound to the call's variable at the call's result type in the caller's
environment. -/
def SPostC (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ty : Ty) (c0 : Ctl) (c : Ctl) (regs : Reg64s) :
    Prop :=
  ∃ (cE : Ctl) (fr : TermRun.Frame) (cr : Ctl) (a : CoreTerm.At) (t : Ty) (ws : List TermRun.Word),
    CallTo p c0 cE fr ∧ SRetR lbl ty cr regs ∧ cr.term = .ret a ∧ TermRun.evalAt cr.env a = some (t, ws) ∧
    c = ⟨fr.body, (fr.x, fr.ty, ws) :: fr.env, none⟩

/-- **The `h0` wrappers' bridge at `SPostC`** (`hPS`): from `SRetR` at the
setup body's `ret` at the call's frame `fr`, the frame step back to the
empty frames lands in `SPostC` (`FrameStep.ret`). -/
theorem hPS_framed {ty : Ty} {c0 : Ctl} :
    ∀ cE fr c rs, CallTo p c0 cE fr → SRetR lbl ty c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ SPostC p lbl ty c0 c'' rs := by
  intro cE fr c rs hct hR
  obtain ⟨σ, hσ, ⟨a, t, ws, -, -, -, hra, -, hev, -⟩, -⟩ := id hR
  have hσs : fr.σs = [] := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩ := hct
    rfl
  exact ⟨_, .step (.ret hra hσs hev) (.refl _), cE, fr, c, a, t, ws, hct, hR, hra, hev, rfl⟩

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.LowerA64.setupCallWS_framed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.setupCallWS_framed

/-- info: 'Spike.Lib.LowerA64.hPS_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.hPS_framed
