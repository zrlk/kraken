/-
**The stack limit as an owned word in `hello1.w` on AArch64** (G6 D2, the
instance side of `Spike.Lib.OwnLim`, the twin of `Spike/Lib/A64Ret0Own.lean`).

The phase (`preStore`, `Lim`), the store's states (`atLim`), the state
predicate (`LimW`), the path (`limPath`) and the layout lemmas
(`layoutOk`, `pre_post_of_layoutOk`, `not_lim_of_layoutOk`) of
`Spike/Lib/A64OwnLimRt.lean` are generic in the executable and the program:
they read only the runtime's labels `preLabels`, which `hello1`'s runtime
prefix (from `_start` to `scc_rt_stack_release`) has as `ret0`'s does, with
the same code. `scc_rt_print` and the program's functions are past the
store, in the phase. This file instantiates them for `hello1Prog` at its
link's code address:

- `hello1_layoutOk`: the layout check (by `decide +kernel`);
- `hello1_pre_post`: the layout facts `hpre`, `hpost` of `limPath` in
  the loaded thread;
- `hello1_own0`, `hello1_ownInit`: the loaded thread owns nothing (`hown0`).
-/
import Spike.Lib.A64OwnLimRt
import Spike.Lib.A64Hello1Code

namespace Spike.Lib.A64.Flow.Hello1.Own

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.OwnLim
open Spike.Lib.A64.OwnLimRt
open Scc.Sem (Range)

/-- **The owned words of `hello1`'s thread**: the limit's word, in the phase. -/
noncomputable def hello1_own (exe : _root_.Executable) (tcb : BitVec 64) (rS : Range) (s : State) :
    List (Loc × Val) :=
  ownLim (I := isaLSE2) tcb rS (Lim exe) s

/-- **`hello1`'s layout check** at its link's code address. -/
theorem hello1_layoutOk : layoutOk SccCode.hello1Λ.code.lo SccCode.hello1Prog = true := by decide +kernel

/-- `hello1`'s symbols all lie at or above its code (by `decide +kernel`). -/
theorem hello1_above :
    ∀ p ∈ Scc.Sem.loadSyms SccCode.hello1Λ SccCode.hello1Secs.rodata, SccCode.hello1Λ.code.lo ≤ p.2 := by
  decide +kernel

/-- **`hello1`'s layout facts in the loaded thread** (`hpre`, `hpost` of
`limPath`), any entry state. -/
theorem hello1_pre_post (E : Scc.Sem.Entry) :
    let exe := (Scc.Sem.A64.threadAt E SccCode.hello1Λ.code.lo SccCode.hello1Prog
      (Scc.Sem.loadSyms SccCode.hello1Λ SccCode.hello1Secs.rodata)).exe
    preStore (labOf exe) (limPc (labOf exe)).toBitVec.toNat = true ∧
      preStore (labOf exe) (limPc (labOf exe) + Int64.ofNat 4).toBitVec.toNat = false :=
  have := Scc.Cert.Link.A64.validLayout_of_loadOk SccCode.hello1Λ_load E
  pre_post_of_layoutOk (Scc.Cert.Rt.A64.lays_threadAt _ _ _ _ hello1_above) rfl hello1_layoutOk

/-- **`hello1`'s loaded thread owns nothing** (`hown0` of `correctK`), any
entry state. -/
theorem hello1_own0 (E : Scc.Sem.Entry) (tcb : BitVec 64) (rS : Range) :
    let s0 := Scc.Sem.A64.threadAt E SccCode.hello1Λ.code.lo SccCode.hello1Prog
      (Scc.Sem.loadSyms SccCode.hello1Λ SccCode.hello1Secs.rodata)
    hello1_own s0.exe tcb rS s0 = [] :=
  have := Scc.Cert.Link.A64.validLayout_of_loadOk SccCode.hello1Λ_load E
  ownLim_of_not (not_lim_of_layoutOk (Scc.Cert.Rt.A64.lays_threadAt _ _ _ _ hello1_above) rfl hello1_layoutOk
    (by decide +kernel) rfl rfl)

/-- **`hello1`'s owned words at load** (`OwnInit`, `hown0` of `correctK`):
none, so any initial memory `tm`. -/
theorem hello1_ownInit (E : Scc.Sem.Entry) (tcb : BitVec 64) (rS : Range) (tm : Memory) :
    let s0 := Scc.Sem.A64.threadAt E SccCode.hello1Λ.code.lo SccCode.hello1Prog
      (Scc.Sem.loadSyms SccCode.hello1Λ SccCode.hello1Secs.rodata)
    Spike.Lib.Consumer1.OwnInit (hello1_own s0.exe tcb rS s0) tm := by
  intro s0
  rw [hello1_own0 E tcb rS]
  exact Spike.Lib.Consumer1.OwnInit.nil tm

end Spike.Lib.A64.Flow.Hello1.Own
