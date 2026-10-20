/-
The initial state of MP: the ghost `mpGhost`, the thread resources `mpRes`
(thread `0` the writer, thread `1` the reader), initial erasure
(`erase_mpInit`, through the generic `erase_initGhost`) and the initial invariants
of both threads.

- `mpGhost`: the flag's release predicate is `φ`, every other location's
  `Pred.emp`; one acquire predicate, `φ` (id `0`); no release message, slot,
  pending mark, update id or claim. The initial flag message is relaxed: `φ`
  is pure at the initial value `0` (`flagPred_pure`).
- The writer holds all of `Dt`, `Fl` and `W` at their initial messages
  (`Res.initOf`); the reader holds nothing but the acquire id `0` of `Fl`.
  (Unlike the spinlock's `SpinInit.erase_init`, the initial total holds an
  acquire id; `mpGhost` is the generic `initGhost` with no release-mode
  location, and `erase_initGhost` applies.)

`mpGhost`, the resources and `erase_mpInit` are in `SLR/MpSpec.lean` (moved
unchanged); this file keeps the initial invariants of the old
rules (`invXW_init`, `invR_init`).
-/
import Kraken.Promising.SLR.MpRule
import Kraken.Promising.SLR.MpSpec
import Kraken.Promising.SLR.SpinInitRes
import Kraken.Promising.SLR.InitGhost

namespace Kraken.Promising.SLR.Mp

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.Spinlock

variable {sW sR : isa.State} {initMem : List (Loc × Val)}

/-! ## The initial invariants -/

variable [layout : _root_.Layout]

/-- **The writer's initial invariant.** -/
theorem invXW_init {P : Params} (hL : MpLocs P) (hF : FrameW P sW) (hp : AtPos mpWriter sW 0) :
    InvXW P 0 True (Config.init [sW, sR] initMem) (mpRes (Config.init [sW, sR] initMem).mem P 0) (mpGhost P) := by
  refine ⟨⟨⟨mpGhost_rel_Fl, fun v => by rw [mpGhost_rel_ne (Ne.symm hL.fl_dt)]; exact Pred.emp_pure v⟩,
    Thread.init sW, by simp [Config.init], hF, 0, hp, ?_, fun h => absurd h (by decide)⟩,
    fun ts h => absurd h (pend_mpGhost ts), fun t ht ts hts => ?_⟩
  · simp only [PhaseW, Own0, mpRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
    refine ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩
  · obtain ⟨s', -, rfl⟩ := Config.init_get?_thread ht
    cases hts

variable [hr : Executable.ValidLayout (layout mpReader)]

/-- **The reader's initial invariant.** -/
theorem invR_init {P : Params} (hF : FrameR P sR) (hp : AtPos mpReader sR 0) :
    InvR P 1 True (Config.init [sW, sR] initMem) (mpRes (Config.init [sW, sR] initMem).mem P 1) (mpGhost P) := by
  refine ⟨⟨mpGhost_rel_Fl, 0, Nat.zero_lt_one, rfl, by simp [mpRes, readerRes]⟩, Thread.init sR,
    by simp [Config.init], hF, 1, by show sR.st.2 = _; rw [r_addr_1]; exact hp, ?_⟩
  simp [PhaseR, FlFwd, Thread.init, Views.getFwd]

end Kraken.Promising.SLR.Mp
