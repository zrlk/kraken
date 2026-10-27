/-
**`main`'s exit from its body's exits by placements** (x86-64, `Accepted2`):
the return of an `Accepted2` `main` (`ExitC2SL` at `int`,
`Spike/Lib/LowerX64/RetSL.lean`) as `scc_rt_main`'s user function's return
(`uNx`, `Spike/Lib/Rt/X64Main.lean`) and the `exit_group` after it as
`main`'s exit (`MainExitS`, `Spike/Lib/SegLagS.lean`), for `mainU_segWS`'s
`hU`/`hexit` (`Spike/Lib/Rt/X64SegsS.lean`) and the setup layout's.

- `UPostR`: the user function's post at a pair: a frame run from the pair's
  control at the empty frames reaches the return of `v` (`RetV`); the
  control is the real one (the empty run) or one held back;
- `RetJS.retV_int`: at `int` (`RetL`), the placements are the return of the
  number in `%rax`;
- `uPostR_ret`: the return's exit by placements past `ret` in the rebased
  region is the interface's return `uNx` at `UPostR`, from any control a
  frame run at `[]` reaches its control from;
- `uPostR_exit`: at a control `UPostR` relates to the number in `%rdi`,
  under any memory side whose placed pairs include `Placed` (`hpl`; `msOf`,
  `msOfS` and `msOfAX` at `[]`), `main`'s exit with that number mod 256
  after the frame run (`MainExitS`);
- `userCallWS_of_exitC2SL`: `UserCallWS` at `UPostR` from a segment from
  the interface's entry `uN0` to `ExitC2SL` at `int` at `[]`, its aborts
  never ending (the twin of `userCallWS_of_exitC`).
-/
import Spike.Lib.LowerX64.RetSL
import Spike.Lib.LowerX64.UPostS
import Spike.Lib.LowerX64.ProgC

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64Consumer (Lbl Placed)
open Spike.Lib.LowerNode (RetL)

/-- **The user function's post at a pair**: from the control `c`, a frame
run at the empty frames reaches the return of `v` (`RetV`). -/
def UPostR (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (c : Ctl) (v : BitVec 64) : Prop :=
  ∃ c', FrameRun p (c, []) (c', []) ∧ RetV lbl c' v

/-- The post at depth is the post at its pair. -/
theorem UPostS.toR {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {c0 c : Ctl} {v : BitVec 64}
    (h : UPostS p lbl c0 c v) : UPostR p lbl c v := by
  obtain ⟨rfl, h⟩ := h
  exact h

/-- **At `int`, the placements are the return of the number in `%rax`**
(`RetJS.toJ2_int`, the word a number by `RetL.int`). -/
theorem RetJS.retV_int {lbl : WeakMem.AllocLabel → Option Nat} {fp : BitVec 64} {σ : AS} {c : Ctl}
    (h : RetJS lbl fp σ c) (hL : RetL .int c) : RetV lbl c (σ.regs.get64 .rax) := by
  obtain ⟨a, t, ws, ht, hh, he, -, hv, -⟩ := h.toJ2_int hL
  obtain ⟨a', t', w, ht', he', n, hn, -⟩ := RetL.int hL
  rw [ht] at ht'
  cases ht'
  rw [he] at he'
  cases he'
  exact ⟨a, t, w, ht, hh, he, ⟨n, hn⟩, hv 0 (by simp) (by decide)⟩

/-- **`main`'s return at the interface's post** (`uPostS_ret` at
`retNSL`): the return's exit by placements at `int` past `ret` in the
rebased region, at a control a frame run at `[]` reaches from `cb`, is the
interface's return `uNx` at `UPostR` at `cb`, `%rsp` past the return
address at the entry's `%rsp` the region's base (`hbase`, `at_of_rbR`). -/
theorem uPostR_ret {p : Prog} {exe : _root_.Executable} {endPc : Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {R : Region} {F : MachineData → Prop} {g : Spike.Lib.X64.Flow.Ret0.WcG} {c0 cb c : Ctl} {s : State} {tp : UInt64}
    (hbase : R.base = g.sp) (hr : FrameRun p (cb, []) (c, []))
    (hA : At exe endPc (rbR R) F ((retNSL p lbl g.fp g.ra c0 .int).withTp tp) s c) :
    At exe endPc R F (Spike.Lib.X64.Rt.uNx (UPostR p lbl) g) s cb := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD', ⟨⟨hJ, -⟩, hL⟩, -⟩ := hA
  have hv := hJ.retV_int hL
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hbp⟩ := hJ
  have h' : At exe endPc (rbR R) F ⟨Int64.ofBitVec g.ra, ⟨16, []⟩, fun σ (_ : Ctl) =>
      σ.regs.get64 .rbp = g.fp ∧ RetV lbl c (σ.regs.get64 .rax)⟩ s c :=
    ⟨he, hn, hdc, hpc, σ, hA, hD', hbp, hv⟩
  obtain ⟨he, hn, hdc, hpc, σ', hA', hD'', hbp', hv'⟩ :=
    at_of_rbR (J' := fun σ (_ : Ctl) => σ.regs.get64 .rbp = g.fp ∧ RetV lbl c (σ.regs.get64 .rax))
      (fun _ _ h => h) h'
  have hsp := hA'.so .rsp (16 - 8) (by simp [SO.get])
  refine ⟨he, hn, hdc, hpc, σ', hA', hD'', ⟨c, hr, hv'⟩, hbp', ?_⟩
  rw [show σ'.regs.rsp.toBitVec = σ'.regs.get64 .rsp from rfl, hsp, Region.addr, hbase]
  rfl

/-- **`main`'s exit at the post `UPostR`** (`uPost_exit` after the frame
run), under any memory side whose placed pairs include `Placed` (`hpl`):
from the control a frame run at `[]` reaches `main`'s `ret` of the number in
`%rdi`, placed there, whose return is the exit with the number mod 256. -/
theorem uPostR_exit {p : Prog} {Λ : Scc.Sem.Layout} {lbl : Lbl} {ms : MemSide isa}
    (hpl : ∀ s c, Placed Λ lbl s c → ms.pl s c) {exe : _root_.Executable} {endPc : Int64} {pc : Int64} {o : SO} :
    ∀ (R' : Region) (F' : MachineData → Prop) s c (v : BitVec 64), UPostR p lbl c v →
      At exe endPc R' F' ⟨pc, o, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c → ¬ ms.abortAt s →
        MainExitS p ms s c v.toNat := by
  rintro R' F' s c v ⟨c', hr, a, t, w, hta, -, hev, ⟨n, hn⟩, hv⟩ ⟨-, -, -, -, σ, hA, -, hx⟩ -
  have hx0 : Scc.Sem.X64.regVal s (.r .rdi) = v := by
    show s.st.1.regs.rdi.toBitVec = v
    rw [hA.regs]; exact hx
  refine ⟨c', hr, c', .refl _, hpl s c' ?_, ?_⟩
  · cases a with
    | var y =>
      refine ⟨fun x k => if x = y ∧ k = 0 then some (.one (.reg (.r .rdi))) else none, ?_, ?_, ?_⟩
      · intro x ty ws hl k wd wp hk hp
        dsimp only at hp
        split at hp
        · obtain ⟨rfl, rfl⟩ := ‹x = y ∧ k = 0›
          cases hp
          have hw : (ty, ws) = (t, [w]) := Option.some.inj (hl.symm.trans hev)
          cases hw
          cases hk
          exact ⟨v.toNat, congrArg (fun b : BitVec 64 => some b.toNat) hx0, hv⟩
        · cases hp
      · intro x hx ty ws hl k hk
        rw [hta] at hx
        simp [Scc.Sem.exprFv, Scc.Sem.atVars] at hx
        subst hx
        have hw : (ty, ws) = (t, [w]) := Option.some.inj (hl.symm.trans hev)
        cases hw
        obtain rfl : k = 0 := by simpa using hk
        exact ⟨.one (.reg (.r .rdi)), by simp⟩
      · intro x k m h
        dsimp only at h
        split at h <;> cases h
    | lit m =>
      refine ⟨fun _ _ => none, ?_, ?_, ?_⟩
      · intro _ _ _ _ _ _ _ _ hp; cases hp
      · intro x hx
        rw [hta] at hx
        simp [Scc.Sem.exprFv, Scc.Sem.atVars] at hx
      · intro _ _ _ h; cases h
    | unit => cases hev
  · intro s0 th h0 ht he hs
    unfold Scc.Sem.SrcSem.mainExit
    rw [h0]
    simp only [ht, hta, hs, he, hev, hn]
    rw [hn] at hv
    rw [hv.2]
    rfl

/--
info: 'Spike.Lib.LowerX64.uPostR_exit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms uPostR_exit

section UserCall

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {W : FragS isa} {K : State → State → Prop}

/-- **`scc_rt_main`'s user function at depth from an `Accepted2` body's
exits** (`UserCallWS` at `UPostR`; `userCallWS_of_exitC` at `ExitC2SL`):
at every frame condition and ghost of the interface with the callee
region's base the entry's `%rsp`, a segment at the empty frames from the
entry `uN0` to the exits `ExitC2SL` at `int` with the interface's frame
pointer and return address (`hseg`, e.g. `main`'s at `[]`), its aborts `Ab`
never ending; the return past `ret` is `uNx` at `UPostR` (`uPostR_ret`,
the empty hold-back). -/
theorem userCallWS_of_exitC2SL {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int}
    {ZU : Int64} {ra : BitVec 64} {c0 : Ctl} {tp : UInt64}
    (hseg : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ Spike.Lib.X64.Flow.Ret0.CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ g : Spike.Lib.X64.Flow.Ret0.WcG, g.ra = ra → g.c0 = c0 → g.tp = tp →
      (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp →
      ∃ (Ab : FragS isa) (c0' : Ctl),
        SegWS W K p lbl ms
          ((At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
            (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F fn ZU g)).at [])
          (ExitC2SL p lbl exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' g.fp g.ra tp c0' []
            .int Ab) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.UserCallWS W K p lbl ms exe endPc R F fn Z D ZU (UPostR p lbl) ra c0 tp := by
  intro F' hR0 hF' hFF g hra hc htp
  by_cases hbase : (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp
  case neg =>
    refine SegWS.empty fun s c fs h => hbase ?_
    obtain ⟨⟨-, -, -, -, σ, hA, -, ⟨-, -, -, hsp, -⟩, -⟩, -⟩ := h
    have := hA.so .rsp 0 (by simp [SO.get, Spike.Lib.X64.Rt.uN0])
    rw [← hsp]
    simpa [Region.addr, Reg64s.get64] using this.symm
  obtain ⟨Ab, c0', h1, hAb⟩ := hseg F' hR0 hF' hFF g hra hc htp hbase
  refine (SegWS.seq_left (Q := Ab) (E := (At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
      (Spike.Lib.X64.Rt.uNx (UPostR p lbl) g)).at []) (h1.mono_post fun s c fs h => ?_) hAb).mono_post
      fun s c fs h => ?_
  · rcases h with ⟨rfl, c1, -, hA⟩ | h
    · exact .inr ⟨uPostR_ret hbase (.refl _) hA, rfl⟩
    · exact .inl h
  · exact h.elim False.elim id

/--
info: 'Spike.Lib.LowerX64.userCallWS_of_exitC2SL' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms userCallWS_of_exitC2SL

end UserCall

end Spike.Lib.LowerX64
