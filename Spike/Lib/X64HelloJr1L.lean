/-
**hello's `wc_main` entry invariants at rodata's own label** (x86-64; the twin of `Spike/Lib/A64HelloJr1L.lean`):
`HelloJr1`'s `JrR`/`Jr1H` with the slice's label fixed to the label `l` rodata allocated (level 1 is stated per
`l`, from `RdLandH … l b n`, whose `Ea` binds rodata's buffer to `⟨l, 0⟩`), so `wc_main`'s box `new` is on `slW l`
itself, not on some label.

- `JrRL lbl env l`, `Jr1L lbl mw l`: `JrR`, `Jr1H` at the label `l`.
- `jrRL_jrR`, `jr1L_jr1H`: they are instances (witness `l`).
- `jr1L_loc`: `MainWcPS.hloc` at these (as AArch64's `jr1H_loc`).

`Land.Jr1LH hpw i0 l b` is `Jr1L (upd LB l b) mwH l`.

Unlike AArch64, the slice's registers are `wc_rodata`'s x86-64 return registers (`SlRegs`: `%rax`, `%rdx`, `%rcx`,
`%rsi`; AArch64: `x0`–`x3`), and `HelloM.JrT` is x86-64's (`%fs` base, `%rsp = R.addr (-72)`).
-/
import Spike.Lib.X64HelloJr1
import Spike.Lib.X64HelloMainPostT

namespace Spike.Lib.X64.Flow.HelloJr1

open CoreLang CoreTerm TermRun
open Spike.Lib (Ctl LocalRun LocalRunS)
open Spike.Lib.X64 (AS)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloMainPreSrc (SlRep c0H c0H_run)
open Spike.Lib.X64HelloSplit (slTy)
open Spike.Lib.X64HelloRdCf (slW setupCont_run)
open Spike.Lib.X64.Flow.HelloM (JrT)

/-- **`scc_rt_main` back from `wc_rodata` on the slice at `l`**: the wrapper's continuation with `r` bound to
`slW l`, the slice in `wc_rodata`'s return registers. -/
def JrRL (lbl : WeakMem.AllocLabel → Option Nat) (env : Env) (l : WeakMem.AllocLabel) (σ : AS) (c : Ctl) : Prop :=
  c = ⟨SrcCalls.setupCont, ("r", slTy, slW l) :: env, none⟩ ∧ SlRegs lbl l σ

/-- **`scc_rt_main` at the box's `new` on the slice at `l`**: `c0H` on `slW l`'s words and `me`'s word `mw`, the
slice in `wc_rodata`'s return registers. -/
def Jr1L (lbl : WeakMem.AllocLabel → Option Nat) (mw : Word) (l : WeakMem.AllocLabel) (σ : AS) (c : Ctl) : Prop :=
  c = c0H (cst (.loc ⟨l, 0⟩ 0)) (cst (.num 2)) (cst (.num 13)) mw ∧ SlRegs lbl l σ

/-- `JrRL … l` is `JrR` at the witness `l`. -/
theorem jrRL_jrR {lbl : WeakMem.AllocLabel → Option Nat} {env : Env} {l : WeakMem.AllocLabel} {σ : AS} {c : Ctl}
    (h : JrRL lbl env l σ c) : JrR lbl env σ c :=
  ⟨l, h⟩

/-- `Jr1L … l` is `Jr1H` at the witness `l`. -/
theorem jr1L_jr1H {lbl : WeakMem.AllocLabel → Option Nat} {mw : Word} {l : WeakMem.AllocLabel} {σ : AS} {c : Ctl}
    (h : Jr1L lbl mw l σ c) : Jr1H lbl mw σ c :=
  ⟨l, h⟩

/-- **`MainWcPS.hloc` at the label `l`**: from `JrT (JrRL lbl env l) t R` the source's continuation, `main`'s split
and zero reach the box's `new` on `slW l` (`me` at `mw` in `env`), the registers unchanged. -/
theorem jr1L_loc {lbl : WeakMem.AllocLabel → Option Nat} {env : Env} {l : WeakMem.AllocLabel} {tm : Ty} {mw : Word}
    {t : UInt64} {R : Spike.Lib.Region} (hme : evalAt env (.var "me") = some (tm, [mw])) (σ : AS) (c : Ctl)
    (h : JrT (JrRL lbl env l) t R σ c) : ∃ c', LocalRun helloSrc c c' ∧ Jr1L lbl mw l σ c' := by
  obtain ⟨⟨rfl, hsl⟩, -, -⟩ := h
  exact ⟨_, ((setupCont_run hme).trans (c0H_run _ _ _ _)).toLocalRun, rfl, hsl⟩

end Spike.Lib.X64.Flow.HelloJr1

/-- info: 'Spike.Lib.X64.Flow.HelloJr1.jrRL_jrR' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloJr1.jrRL_jrR

/-- info: 'Spike.Lib.X64.Flow.HelloJr1.jr1L_jr1H' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloJr1.jr1L_jr1H

/-- info: 'Spike.Lib.X64.Flow.HelloJr1.jr1L_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloJr1.jr1L_loc
