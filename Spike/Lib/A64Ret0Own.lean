/-
**The stack limit as an owned word in `ret0.w` on AArch64** (G6 D2, the
instance side of `Spike.Lib.OwnLim`): `ret0`'s facts for the generic phase,
path and layout check of `Spike.Lib.A64.OwnLimRt` (`Spike/Lib/A64OwnLimRt.lean`:
`preStore`, `Lim`, `atLim`, `LimW`, `limPath`, `layoutOk`).

- `ret0_own`: the owned words of `ret0`'s thread, the limit's word in the
  phase;
- `ret0_layoutOk`: the layout check at the link's code address (by
  `decide +kernel`);
- `ret0_pre_post`: the layout facts `hpre`, `hpost` of `limPath` in the
  loaded thread;
- `ret0_own0`, `ret0_ownInit`: the loaded thread owns nothing (`hown0`).
-/
import Spike.Lib.A64OwnLimRt
import Spike.Lib.A64Ret0ThreadInit

namespace Spike.Lib.A64.Flow.Ret0.Own

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.OwnLim
open Spike.Lib.A64.OwnLimRt
open Scc.Sem (Range)

/-- **The owned words of `ret0`'s thread**: the limit's word, in the phase. -/
noncomputable def ret0_own (exe : _root_.Executable) (tcb : BitVec 64) (rS : Range) (s : State) :
    List (Loc × Val) :=
  ownLim (I := isaLSE2) tcb rS (Lim exe) s

/-- **`ret0`'s layout check** at its link's code address. -/
theorem ret0_layoutOk : layoutOk SccCode.ret0Λ.code.lo SccCode.ret0Prog = true := by decide +kernel

/-- `ret0`'s symbols all lie at or above its code (by `decide +kernel`). -/
theorem ret0_above :
    ∀ p ∈ Scc.Sem.loadSyms SccCode.ret0Λ SccCode.ret0Secs.rodata, SccCode.ret0Λ.code.lo ≤ p.2 := by
  decide +kernel

/-- **`ret0`'s layout facts in the loaded thread** (`hpre`, `hpost` of
`limPath`), any entry state. -/
theorem ret0_pre_post (E : Scc.Sem.Entry) :
    let exe := (Scc.Sem.A64.threadAt E SccCode.ret0Λ.code.lo SccCode.ret0Prog
      (Scc.Sem.loadSyms SccCode.ret0Λ SccCode.ret0Secs.rodata)).exe
    preStore (labOf exe) (limPc (labOf exe)).toBitVec.toNat = true ∧
      preStore (labOf exe) (limPc (labOf exe) + Int64.ofNat 4).toBitVec.toNat = false :=
  have := Scc.Cert.Link.A64.validLayout_of_loadOk SccCode.ret0Λ_load E
  pre_post_of_layoutOk (Scc.Cert.Rt.A64.lays_threadAt _ _ _ _ ret0_above) rfl ret0_layoutOk

/-- **`ret0`'s loaded thread owns nothing** (`hown0` of `correctK`), any
entry state. -/
theorem ret0_own0 (E : Scc.Sem.Entry) (tcb : BitVec 64) (rS : Range) :
    let s0 := Scc.Sem.A64.threadAt E SccCode.ret0Λ.code.lo SccCode.ret0Prog
      (Scc.Sem.loadSyms SccCode.ret0Λ SccCode.ret0Secs.rodata)
    ret0_own s0.exe tcb rS s0 = [] :=
  have := Scc.Cert.Link.A64.validLayout_of_loadOk SccCode.ret0Λ_load E
  ownLim_of_not (not_lim_of_layoutOk (Scc.Cert.Rt.A64.lays_threadAt _ _ _ _ ret0_above) rfl ret0_layoutOk (by decide +kernel) rfl rfl)

/-- **`ret0`'s owned words at load** (`OwnInit`, `hown0` of `correctK`):
none, so any initial memory `tm`. -/
theorem ret0_ownInit (E : Scc.Sem.Entry) (tcb : BitVec 64) (rS : Range) (tm : Memory) :
    let s0 := Scc.Sem.A64.threadAt E SccCode.ret0Λ.code.lo SccCode.ret0Prog
      (Scc.Sem.loadSyms SccCode.ret0Λ SccCode.ret0Secs.rodata)
    Spike.Lib.Consumer1.OwnInit (ret0_own s0.exe tcb rS s0) tm := by
  intro s0
  rw [ret0_own0 E tcb rS]
  exact Spike.Lib.Consumer1.OwnInit.nil tm

/-! ## The store's pc -/

/-- `limPc` is `scc_rt_thread_init`'s store of field 1 (`storePc lab 1`). -/
example (lab : Label → Int64) : limPc lab = Spike.Lib.A64.Flow.Ret0.ThreadInit.storePc lab 1 := rfl

end Spike.Lib.A64.Flow.Ret0.Own
