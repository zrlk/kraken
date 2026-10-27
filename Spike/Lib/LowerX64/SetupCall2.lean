/-
**The setup block called by `scc_rt_main`, from its body's exits by
placements** (x86-64, `Accepted2`): the framed interface `SetupCallWS`
(`Spike/Lib/Rt/X64MainSS.lean`, the setup function's body run in the frame
`fr` its call pushes) at the post `SRetR` at the body's `ret`, from a
segment of the setup function's body to its exits `ExitC2SL` at `[fr]` at
its result type, whose aborts never end; and the bridge `hPS` of the
`h0` wrappers: the `ret` pops `fr` into the caller's continuation, the
post `SPostC` there.

- `SRetR`: the setup call's post at the body's `ret`: its words at the
  result type `ty` placed in the return registers (`RetJS`, `RetL ty`);
- `uPostSR_ret`: the return's exit by placements past `ret` in the rebased
  region is the interface's return `uNxS` at `SRetR`, the thread pointer
  the ghost's;
- `setupCallWS_framed`: `SetupCallWS` at `SRetR` from a segment from the
  interface's entry `uN0` at `[fr]` to `ExitC2SL` at `ty` at `[fr]`, its
  aborts never ending;
- `SPostC`: the post at the caller's continuation: the control the `ret` of
  a `SRetR` control pops the call's frame into, with the returned words
  bound to the call's variable;
- `hPS_framed`: from `SRetR` at the `ret`, the frame step back to `[]` lands
  in `SPostC` (`FrameStep.ret`).
-/
import Spike.Lib.LowerX64.MainCall2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.LowerNode (RetL)
open Spike.Lib.X64.Flow (CallTo)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {W : FragS isa} {K : State → State → Prop}

/-- **The setup call's post at the body's `ret`**: the control's returned
words at the result type `ty` placed in the registers `regs`' return
registers (`RetJS`, `RetL ty`). -/
def SRetR (lbl : WeakMem.AllocLabel → Option Nat) (ty : Ty) (c : Ctl) (regs : Reg64s) : Prop :=
  ∃ σ : AS, σ.regs = regs ∧ RetJS lbl (regs.get64 .rbp) σ c ∧ RetL ty c

/-- **The setup function's return at the interface's post**: the return's
exit by placements at `ty` past `ret` in the rebased region, at the ghost's
thread pointer (`htp`), is the interface's return `uNxS` at `SRetR`,
`%rsp` past the return address at the entry's `%rsp` the region's base
(`hbase`, `at_of_rbR`). -/
theorem uPostSR_ret {R : Region} {F : MachineData → Prop} {g : Spike.Lib.X64.Flow.Ret0.WcG} {c0 c : Ctl}
    {s : State} {tp : UInt64} {ty : Ty} (hbase : R.base = g.sp) (htp : tp = g.tp)
    (hA : At exe endPc (rbR R) F ((retNSL p lbl g.fp g.ra c0 ty).withTp tp) s c) :
    At exe endPc R F (Spike.Lib.X64.Rt.uNxS (SRetR lbl ty) g) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD', ⟨⟨hJ, -⟩, hL⟩, hfs⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hbp⟩ := id hJ
  have hJ' : RetJS lbl (σ.regs.get64 .rbp) σ c := by rw [hbp]; exact hJ
  have h' : At exe endPc (rbR R) F ⟨Int64.ofBitVec g.ra, ⟨16, []⟩, fun σ' c' =>
      σ'.regs.get64 .rbp = g.fp ∧ σ'.regs.fsBase = g.tp ∧ SRetR lbl ty c' σ'.regs⟩ s c :=
    ⟨he, hn, hdc, hpc, σ, hA, hD', hbp, htp ▸ hfs, σ, rfl, hJ', hL⟩
  obtain ⟨he, hn, hdc, hpc, σ', hA', hD'', hbp', hfs', hP⟩ :=
    at_of_rbR (J' := fun σ' c' =>
      σ'.regs.get64 .rbp = g.fp ∧ σ'.regs.fsBase = g.tp ∧ SRetR lbl ty c' σ'.regs) (fun _ _ h => h) h'
  have hsp := hA'.so .rsp (16 - 8) (by simp [SO.get])
  refine ⟨he, hn, hdc, hpc, σ', hA', hD'', hP, hbp', ?_, hfs'⟩
  rw [show σ'.regs.rsp.toBitVec = σ'.regs.get64 .rsp from rfl, hsp, Region.addr, hbase]
  rfl

/-- **The framed setup block, from its exits** (`SetupCallWS` at `SRetR`):
at every frame condition, ghost `g` and call frame `fr` of the interface
with the callee region's base the entry's `%rsp`, a segment inside `W` at
`[fr]` from the entry `uN0` to the setup function's exits `ExitC2SL` at its
result type `ty` at `[fr]` with `g`'s frame pointer and return address and
the thread pointer `tp` (`hseg`), and one from its aborts `Ab` to nothing;
the return past `ret` is `uNxS` at `SRetR` (`uPostSR_ret`). -/
theorem setupCallWS_framed {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int}
    {ZU : Int64} {ty : Ty} {ra : BitVec 64} {c0 : Ctl} {tp : UInt64}
    (hseg : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ Spike.Lib.X64.Flow.Ret0.CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ (g : Spike.Lib.X64.Flow.Ret0.WcG) (fr : TermRun.Frame), g.ra = ra → g.tp = tp → CallTo p c0 g.c0 fr →
      (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp →
      ∃ (Ab : FragS isa) (c0' : Ctl),
        SegWS W K p lbl ms
          ((At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
            (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F fn ZU g)).at [fr])
          (ExitC2SL p lbl exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' g.fp g.ra tp c0' [fr]
            ty Ab) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.SetupCallWS W K p lbl ms exe endPc R F fn Z D ZU (SRetR lbl ty) ra c0 tp := by
  intro F' hR0 hF' hFF g fr hra htp hct
  by_cases hbase : (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp
  case neg =>
    refine SegWS.empty fun s c fs h => hbase ?_
    obtain ⟨⟨-, -, -, -, σ, hA, -, ⟨-, -, -, hsp, -⟩, -⟩, -⟩ := h
    have := hA.so .rsp 0 (by simp [SO.get, Spike.Lib.X64.Rt.uN0])
    rw [← hsp]
    simpa [Region.addr, Reg64s.get64] using this.symm
  obtain ⟨Ab, c0', h1, hAb⟩ := hseg F' hR0 hF' hFF g fr hra htp hct hbase
  refine (SegWS.seq_left (Q := Ab) (E := (At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
      (Spike.Lib.X64.Rt.uNxS (SRetR lbl ty) g)).at [fr]) (h1.mono_post fun s c fs h => ?_) hAb).mono_post
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
  ∃ (cE : Ctl) (fr : TermRun.Frame) (cr : Ctl) (a : At) (t : Ty) (ws : List TermRun.Word),
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

end Spike.Lib.LowerX64

/--
info: 'Spike.Lib.LowerX64.setupCallWS_framed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.setupCallWS_framed

/-- info: 'Spike.Lib.LowerX64.hPS_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.hPS_framed
