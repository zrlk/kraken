/-
**A code block's prologue inside the body's fragment at depth** (AArch64,
H7a calls): the prologue obligation `ProW` of a code block's segment
inside `BodyWS0` (`Spike/Lib/LowerA64/BodyWS1.lean`) at the frames `fs`,
from the prologue's code and phase facts, with no premise about the
calls. The twin of `Spike/Lib/LowerX64/ProWS.lean`.

- `mem_mapM_some`: a value of `l.mapM f` is `f`'s at a member of `l`;
- `spillsOk_of_spills`: the parameter spill `spills cx ps` (`fnOk1`'s, the
  stores of the argument registers) at cells of the frame, as
  `proW_sfactsP` takes it;
- `proW_bodyS`: a stack-checked prologue with saved registers `ps` in the
  frame (`proW_sfactsP` at the held-back control `c0`) inside `BodyWS0` at
  `fs`, every control of its invariant `Good1` at `fs` with no hold.
-/
import Spike.Lib.LowerA64.BodyWS1
import Spike.Lib.LowerA64.UserW
import Spike.Lib.LowerA64.Construct

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Sem (Marks Range)
open Spike.Lib.A64Consumer (CFacts SFacts Own Lbl)
open Spike.Lib.A64ConsumerS (SFactsS)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff limA)

/-- **A value of a mapped list is a mapped member**: every `b` in
`l.mapM f` is `f a` for some `a ∈ l`. -/
theorem mem_mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {ss : List β}, l.mapM f = some ss → ∀ b ∈ ss, ∃ a ∈ l, f a = some b
  | [], ss, h, b, hb => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; cases hb
  | y :: ys, ss, h, b, hb => by
    rw [List.mapM_cons] at h
    cases hy : f y with
    | none => rw [hy] at h; cases h
    | some c =>
      cases hys : ys.mapM f with
      | none => rw [hy, hys] at h; cases h
      | some cs =>
        rw [hy, hys] at h
        cases h
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨y, List.mem_cons_self .., hy⟩
        · obtain ⟨a, ha, hfa⟩ := mem_mapM_some hys b hb
          exact ⟨a, List.mem_cons_of_mem _ ha, hfa⟩

/-- **The parameter spill is at cells of the frame**: each store of
`spills cx prs` (an argument register to a parameter's slot `o`) writes
the cell `-frame + o` of the frame below the saved pair. -/
theorem spillsOk_of_spills {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {prs : List Scc.IR.Reg} {ps : List (XReg × Int64)} (hps : Scc.Cert.Code1A64.spills cx prs = some ps) :
    ∀ q ∈ ps, offOk (-(Int64.ofInt cx.frame).toInt) 0 (-(Int64.ofInt cx.frame).toInt + q.2.toInt) = true := by
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  rw [hF64]
  intro q hq
  unfold Scc.Cert.Code1A64.spills at hps
  split at hps
  · obtain ⟨⟨pr, r⟩, -, hq'⟩ := mem_mapM_some hps q hq
    cases ho : cx.slotOff pr with
    | error e => simp [ho, Except.toOption] at hq'
    | ok o =>
      simp only [ho, Except.toOption, Option.map_some, Option.some.injEq] at hq'
      subst hq'
      obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf ho
      have hoo : (Int64.ofInt o).toInt = o := toInt_ofInt_small (by omega) (by omega)
      simp only [hoo, offOk, decide_eq_true_eq]
      omega
  · cases hps

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop} {p : Prog} {c0 : Ctl}

/-- **A code block's prologue is inside `BodyWS0` at the frames `fs`**:
its code (`hin`, at the frame of `cx`, the limit at `Tcb.stackLimit`)
with its saved registers at cells of the frame (`hps`), its phase facts
(`hph`), every control of its invariant `Good1` at `fs` with no hold and
the thread pointer `tp` (`hJ`), the thread pointer's limit word mapped
(`hmr`) and unmapped in private memory (`hun`), in any 16-aligned region
holding the frame: `proW_sfactsP` at the held-back control `c0` (`Good1`
with no frame and no hold), its facts lifted to `SFactsS` at the empty
frames (`SFactsS.ofSFacts0`). -/
theorem proW_bodyS {ms : MemSide isaLSE2} {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {fn entry : Label}
    {ps : List (XReg × Int64)}
    (hin : prologueIn prog fn (cx.local "stack_check") entry (Int64.ofInt cx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL cx) ps = true)
    (hps : ∀ q ∈ ps, offOk (-(Int64.ofInt cx.frame).toInt) 0 (-(Int64.ofInt cx.frame).toInt + q.2.toInt) = true)
    (hph : ProPh okPc ph lab (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) ps)
    (hC0 : CFacts Λ lbl c0) (hp : Scc.Lower.Accepted1 p = true) (hg0 : Good1 p (c0, []))
    {cl ctr : Nat} {fs : List TermRun.Frame} {tp : UInt64} {J : AS → Ctl → Prop}
    (hJ : ∀ σ c, J σ c → σ.regs.TPIDR_EL0 = tp ∧ Good1 p (c, fs) ∧ c.hold = none)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    ProW (fun s c => BodyWS0 Λ μ p own rS Tk lbl cl ctr c0 s c fs) K exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) (Int64.ofInt cx.frame) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL cx) ps J := by
  have hge := frame_ge16 hf
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  have H := proW_sfactsP (J := fun σ c => c = c0 ∧ ∃ c1, J σ c1) (ms := ms) hI hin hps hC0 (fun _ _ h => h.1)
    (fun _ _ ⟨_, _, h⟩ => (hJ _ _ h).1) hph hR hal (by rw [hF64]; exact hlo) hhi hl hh (by rw [hF64]; omega)
    (by rw [hF64]; omega) hmr hun hsub hfit hFO
  exact ProW.mapC H fun σ c hJc =>
    ⟨c0, ⟨rfl, c, hJc⟩, fun _ hs => ⟨(hJ σ c hJc).2.1, (hJ σ c hJc).2.2, SFactsS.ofSFacts0 hs hp hg0⟩⟩

end W

end Spike.Lib.LowerA64
