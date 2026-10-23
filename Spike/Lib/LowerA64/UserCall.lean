/-
**The user `main` as `scc_rt_main`'s user function** (AArch64): the
interface `UserCallW` (`Spike/Lib/Rt/A64Main.lean`) inside the consumer's
facts, from the lowered function's segment `fn0_seg`
(`Spike/Lib/LowerA64/Fn.lean`) held back at the source start
(`SegW.lag`, `Spike/Lib/SegLag.lean`).

The source control at the call is the start's (`A64Consumer.c0`, a tail
call into `main`): `fn0_seg`'s entry invariant holds there, its body's
`NJ` a local run (the start's step, `start_step_main`) away
(`nj_start`). The segment's obligations are inside `BodyW0`
(`proW_body0`, `hWb_of`, `hWs_of`) and, held back at the start, inside
`SFacts`; its return reaches the return address with the start control
and the return value related by `UPost`; its overflow abort is the
premise `hab` (from the held-back abort block, `seg_localW_lag`).

- `RetV`, `UPost`: a control at `ret` of a one-word atom valued `v`;
  the start control with a local run to one (the return-value contract).
- `start_step_main`, `nj_start`: the start's step into `main`, `NJ` at the
  start.
- `userCallW_of_fn`: the interface from the function's code facts.
-/
import Spike.Lib.LowerA64.Main
import Spike.Lib.A64StubFacts
import Spike.Lib.LowerA64.UserW
import Spike.Lib.Rt.A64Main

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf)
open Scc.Sem (Marks Range ValRep)
open Spike.Lib.Form (NodeJ SEnv lookupS)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (lower0 Res)
open Spike.Lib.A64Consumer (CFacts SFacts Own Lbl)
open Spike.Lib.A64.Rt (InstOk UserCallW uN0 uNx)
open Spike.Lib.A64.Flow.Ret0 (StackOff WcG LimOk limA tcbA_limA)

/-! ## The return-value contract -/

/-- **A control at the return of a one-word atom valued `v`** (a number). -/
def RetV (lbl : WeakMem.AllocLabel → Option Nat) (c : Ctl) (v : BitVec 64) : Prop :=
  ∃ a t w, c.term = .ret a ∧ c.hold = none ∧ TermRun.evalAt c.env a = some (t, [w]) ∧ (∃ n, w.val = .num n) ∧
    ValRep lbl w.val v.toNat

/-- **The user function's post**: the source control is the start `c0`
(held back), from which a local run reaches the return of `v` (`RetV`). -/
def UPost (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (c0 c : Ctl) (v : BitVec 64) : Prop :=
  c = c0 ∧ ∃ c', LocalRun p c0 c' ∧ RetV lbl c' v

/-! ## The start -/

/-- **The source start's step into `main`** (`hd`): its body, its argument
bound to the start's unit. -/
theorem start_step_main {p : Prog} {d : Decl} (hd : p.find? (·.name == "main") = some d) :
    LocalStep p Spike.Lib.A64Consumer.c0 ⟨d.body, [(d.arg, TermRun.close [] d.argTy, [])], none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th hg ht he hs _
  simp only [TermRun.tstep, ht, TermRun.enter, hg, hd, he, Spike.Lib.A64Consumer.c0, TermRun.evalAt,
    TermRun.lookupE, List.find?, TermRun.ol, Option.map, Option.toList]
  obtain ⟨⟩ := th
  simp only at hs
  subst hs
  simp

/-- **`main`'s body node at the start**: a local run (the start's step)
reaches `main`'s body with its `Unit` argument, no word. -/
theorem nj_start {p : Prog} {d : Decl} (hd : p.find? (·.name == "main") = some d) (hu : d.argTy = .unit)
    {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64} :
    NJ p lbl rs d.body (ofEnv [(d.arg, .unit, [])]) sl Spike.Lib.A64Consumer.c0 := by
  refine ⟨_, .single (start_step_main hd), ⟨rfl, rfl, ?_⟩, ?_⟩
  · intro x t pls hl
    simp only [ofEnv, List.map, lookupS] at hl
    by_cases hx : d.arg = x
    · subst hx
      simp at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact ⟨[], by simp [TermRun.lookupE, hu]; rfl, trivial⟩
    · simp [hx] at hl
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    intro w hw; cases hw

/-! ## The interface -/

section Call

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}

/-- **The user `main` is `scc_rt_main`'s user function inside `SFacts`**
(`UserCallW`, write tail `Dt`, limit room `ZU` its frame, post `UPost`):
for an `Accepted0` program `[d]` (`hd`) whose `main` lowers to `r` (`hr`)
at a context `cx` with a valid frame (`hf`, `h1`, `h16`), its prologue and
body in `prog` (`hpro`, `hbody`), an instance's facts (`hI`), the
callee's depth `D` holding the frame and the abort call's 48 bytes
(`hD`, `hD8`), the body's and the prologue's phase facts at the return
address `ra` (`hphB`, `hphP`), the start's facts (`hC0`), the limit word
of `tp` mapped and unmapped under the frame condition (`hmr`, `hun`), `rS`
in the pool, not wrapping and off the callee's region (`hsub`, `hfit`,
`hFO`, given the caller's cells outside it), and the overflow abort from the held-back abort label (`hab`). -/
theorem userCallW_of_fn {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) {cx : FnCtx} {r : Res} {fn entry : Label}
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hpro : proInC prog cx fn entry = true) (hr : lower0 [(d.arg, .unit, [])] 0 d.body = some r)
    (hbody : bodyIn prog cx entry 0 r.insts r.ret = true)
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {Dt : State → Prop}
    {lbl : Lbl} {ms : MemSide isaLSE2} {R : Region} {F : MachineData → Prop} {Z : Int64} {D : Int}
    {tp : UInt64} {ra : BitVec 64} (hD : (cx.frame : Int) + 48 ≤ D) (hD8 : D % 8 = 0)
    (hphB : bodyPhOk okPc ph (fun _ => false) lab cx entry r.insts r.ret (Int64.ofBitVec ra) = true)
    (hphP : ProPh okPc ph lab (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) [])
    (hC0 : CFacts Λ lbl Spike.Lib.A64Consumer.c0)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → Spike.Lib.A64.Flow.Ret0.CallerCells R (-Z.toInt) (-D) 0 m →
      StackOff rS (R.callee (-Z.toInt) (-D) 0) m)
    (hab : ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK →
      (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 → FStable (R.callee (-Z.toInt) (-D) 0) F' →
      (∀ m, F' m → F m ∧ Spike.Lib.A64.Flow.Ret0.CallerCells R (-Z.toInt) (-D) 0 m) → ∀ fp ra' : BitVec 64,
      SegW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K [d] lbl ms
        (Lag [d] (· = Spike.Lib.A64Consumer.c0) (At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
          (abortN (immsOf d) (InWalk d) [d] lbl cx (_root_.Executable.labels exe).label fp ra'
            Spike.Lib.A64Consumer.c0)))
        (fun _ _ => False)) :
    UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K [d] lbl ms exe endPc R F fn Z D (Int64.ofInt cx.frame)
      (UPost [d] lbl Spike.Lib.A64Consumer.c0) ra Spike.Lib.A64Consumer.c0 tp := by
  intro F' hR0 hal0 hF' hFF g hra hc htp
  have hge := frame_ge16 hf
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  have hfind : [d].find? (·.name == "main") = some d := by
    simp only [Scc.Lower.Accepted0, Bool.and_eq_true, beq_iff_eq] at hd
    simp [List.find?, hd.1.1.1.1.1.1]
  have hu : d.argTy = .unit := by
    simp only [Scc.Lower.Accepted0, Bool.and_eq_true, beq_iff_eq] at hd
    exact hd.1.1.1.2
  have hQ := quiet_c0 hd
  have hlo0 : (R.callee (-Z.toInt) (-D) 0).lo ≤ -(cx.frame : Int) := by show -D ≤ _; omega
  have hhi0 : 0 ≤ (R.callee (-Z.toInt) (-D) 0).hi := Int.le_refl 0
  have hl0 : (R.callee (-Z.toInt) (-D) 0).lo % 8 = 0 := by show (-D) % 8 = 0; omega
  have hh0 : (R.callee (-Z.toInt) (-D) 0).hi % 8 = 0 := rfl
  have hFO' : ∀ m, F' m → StackOff rS (R.callee (-Z.toInt) (-D) 0) m :=
    fun m h => hFO m (hFF m h).1 (hFF m h).2
  have hseg := fn0_seg (W := BodyW0 Λ μ own rS Tk lbl Spike.Lib.A64Consumer.c0) (K := K) (p := [d]) (lbl := lbl)
    (ms := ms) (J := (uN0 (_root_.Executable.labels exe).label ms F exe endPc fn (Int64.ofInt cx.frame) g).J)
    (fp := g.fp) (ra := g.ra) (c0 := Spike.Lib.A64Consumer.c0)
    hf h1 h16 hI.lays hI.endOk hpro hr (fresh_unit d.arg) hbody (walk_immsOf d) hF' hR0 hal0 hlo0 hhi0
    (proW_body0 hI hf h1 h16 hpro hC0 (fun _ _ h => h.1.1.trans hc ▸ .refl _) hQ
      (fun _ _ h => h.1.2.2.2.2.trans htp) hphP hR0 hal0 hlo0 hhi0 hl0 hh0 hmr
      (fun m h => hun m (hFF m h).1) hsub hfit hFO')
    (hWb_of hI hf h1 h16 hbody (hra ▸ hphB) hR0 hal0 hlo0 hhi0 hl0 hh0 hsub hfit hFO' hC0 hQ)
    (hWs_of hI hf h1 h16 hbody (hra ▸ hphB) hR0 hal0 hlo0 hhi0 hl0 hh0 hsub hfit hFO' hC0 hQ)
    (fun σ c ⟨⟨hc0, h29, h30, hsp, htp0⟩, hlim⟩ => by
      have hc' : c = Spike.Lib.A64Consumer.c0 := hc0.trans hc
      subst hc'
      have hlim' := hlim.mono fun m h => (hFF m h).1
      refine ⟨?_, h29, h30, fun _ => nj_start hfind hu, .refl _⟩
      rw [show tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit) = limA g.tp from tcbA_limA htp0]
      refine ⟨hlim'.rt, hlim'.mp, hlim'.unmapped, fun v hv => ?_⟩
      rw [hsp]; exact hlim'.room v hv)
  have hlag := (bodyW0_lag hseg).mono_W (W' := fun s c => SFacts Λ μ own rS Tk lbl s c Dt)
    fun s c h => SFacts.dt_mono h fun _ h => h.elim
  refine (SegW.seq_left (Q := Lag [d] (· = Spike.Lib.A64Consumer.c0) (At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
      (abortN (immsOf d) (InWalk d) [d] lbl cx (_root_.Executable.labels exe).label g.fp g.ra
        Spike.Lib.A64Consumer.c0)))
    ((hlag.mono_pre fun s c hAt => by
        obtain ⟨-, -, -, -, σ, -, -, hJ, -⟩ := id hAt
        exact ⟨c, hAt, .refl c, hJ.1.trans hc⟩).mono_post fun s c h => by
      obtain ⟨c', hX, hr', hcc⟩ := h
      rcases hX with ⟨he, hn, hdc, hpc, σ, hA, hD', ⟨a, t, w, hta, hho, hev, hnm, hv, h29, h30⟩, hr0⟩ | hX
      · exact .inr ⟨he, hn, hdc, hpc, σ, hA, hD', ⟨hcc, c', hr0, a, t, w, hta, hho, hev, hnm, hv⟩, h29, h30⟩
      · exact .inl ⟨c', hX, hr', hcc⟩)
    (hab F' hR0 hal0 hF' hFF g.fp g.ra)).mono_post fun _ _ h => h.elim False.elim id

end Call

end Spike.Lib.LowerA64
