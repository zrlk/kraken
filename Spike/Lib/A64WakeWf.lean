/-
**wake.w's states before the `clone` at the per-state level** (`Wf`,
AArch64): the fragments `W0`, `W1` the consumer's two levels take their
segments under (`WakeO.OPrem.h0`, `.h1`), and their `SFactsACH`
(`WakeO.OPrem.hW0`, `.hW1`), the analogue of hello1's `W0`/`hW0`
(`Spike/Test/A64Hello1W0.lean`).

`Wf` mentions no invariant of the consumer's (`I2 … inv0 inv1`): `inv0` is
the witness of `h0`'s `SegInvS`, whose fragment is `W0`. The one fact of
`SFactsACH` that does mention it, `wr`'s counter row (`WrOkA.ctr`: the
counter add's row lands in `PendA p I2 …`), is asked of `Wf` only as "a
write of the counter is in the context `Ctx`" and given at `hWf_at` by a
premise `hctr` at the state, which the instance proves once against `I2`
at `inv0`'s states (`hW0`'s guard).

- `ArenaWr`: every word the instruction writes but the counter is one the
  arena allows at the level `lbl`/`lsize`, from every control the source's
  frames run to (`WrOkA.arena`'s off-counter half), or the state is in
  `Ctx` writing no counter (the box's initialising store).
- `RunWf`: the source pair's run obligations (`SFactsACH.cell`, `.zero`;
  hello1's `RunOk`).
- `AbortWf`: the abort sites (`SFactsACH.abortOk`).
- `Wf`: the state's facts at the write tail `Dt` (`SFactsSt2`, ownership
  `own`), the write abort's and the threads abort's phases kept (`AbSt`,
  `AcSt`), the clone path `Cl` at a `clone` system call, no `ret` of `main`
  at no frame, the control and frames placed at `lbl` (`PlacedSE`),
  `ArenaWr`, a write of the counter only in `Ctx`, `RunWf`, `AbortWf`.
- `W0 frM X0`: `Wf` at the levels `L0`/`ls0` with the frames `[]` or
  `[frM]`, and the per-state facts `X0`;
  `W1 l b n`: `Wf` at `upd L0 l b`/`updN ls0 l n` with no counter write
  (an empty context: the one allocation comes before the level).
- `DtW`, `hdtW`, `dtW_of_fd2`, `SFactsSt2.mono_dt`: wake's write tail (no
  `write` to fd 1; the abort stubs' `write`s to fd 2 lie in the fragments),
  `OPrem.hdt` at it, a stub's `write` in it, the state's facts moved to it.
- `hWf_at`: `SFactsACH` at a state of `Wf` (`SFactsACH.ofSt`), given the
  counter row at it (`hctr`) and the box's store's premises (`hnew`, both
  in `Ctx`, at a counter write and off one); `hW0`, `hW1`: `WakeO.OPrem.hW0`/`.hW1`'s
  shapes from a counter row at the guard's states; `hW1F`: `hW1` with no
  premise.
- `clW`: the clone path at a layout `L`, the `clone` system call's pc
  (`WakeWc.clonePc`'s form, passed as `cpc`) decoding to a `clone`;
  `clW_svc`: `Wf`'s clone clause there.
-/
import Spike.Lib.A64SFactsACH

namespace Spike.Lib.A64.WakeWf

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Arena FragS OvfReady HeapAbortOblA FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA

/-- **The clone path**: the state at the `clone` system call's pc `cpc`
(`WakeWc.clonePc L`), at a system call decoding to a `clone`. -/
def clW (cpc : Nat) (s : State) : Prop :=
  pcOf s = cpc ∧ abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)

/-- `Wf`'s clone clause at `clW`. -/
theorem clW_svc {cpc : Nat} {s : State} (h : clW cpc s) :
    abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl) :=
  h.2

/-- **The arena's writes off the counter**: every word the instruction
writes, the counter's aside, is one the arena allows at the level
`lbl`/`lsize` from every control the source's frames run to, or the state
is in the context `Ctx` writing no counter (the box's initialising store,
whose `NewStM` `hWf_at` takes as a premise, `hnew`). -/
def ArenaWr (ar : Arena) (p : Prog) (lbl : Lbl) (lsize : Lsize) (Ctx : FragS isaLSE2) (s : State) (c : Ctl)
    (fs : List TermRun.Frame) : Prop :=
  ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ L, WrAt s L → L ≠ ar.ctrLoc →
    ArenaW ar lbl lsize c' L ∨ (Ctx s c fs ∧ ¬ WrAt s ar.ctrLoc)

/-- **The source pair's run obligations**: at every control a frame run
from `(c, fs)` reaches, a one-cell access type at a load or store, a
zero-able type at a buffer allocation. -/
structure RunWf (p : Prog) (c : Ctl) (fs : List TermRun.Frame) : Prop where
  cell : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a e ty w,
    (c'.term = .let_ x (.load true a) e ∨ ∃ b, c'.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c'.env a = some (ty, [w]) → OneCellTy ty
  zero : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a τ e, c'.term = .let_ x (.newBuf a τ) e →
    ZeroOkTy τ = true

/-- **The abort sites at a pair** (`SFactsACH.abortOk`). -/
def AbortWf (ar : Arena) (μ : Marks) (Ab Ac : State → Prop) (s : State) (c : Ctl) (fs : List TermRun.Frame) :
    Prop :=
  ∀ k a, μ.abortAt k = some a → pcOf s = a →
    ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
      (k = .heap ∧ HeapAbortOblA ar.cells ar.ctr c) ∨ (k = .threads ∧ Ac s)) ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus

/-- **wake.w's states at the per-state level** (see the module doc). -/
def Wf (Λ : Scc.Sem.Layout) (μ : Marks) (own : Own) (ar : Arena) (p : Prog) (Dt Ab Cl Ac : State → Prop)
    (Ctx : FragS isaLSE2) (lbl : Lbl) (lsize : Lsize) : FragS isaLSE2 := fun s c fs =>
  SFactsSt2 Λ μ own s Dt ∧ AbSt μ Ab s ∧ AcSt μ Cl Ac s ∧
    (Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) ∧
    (fs = [] → ∀ a, c.term ≠ .ret a) ∧ PlacedSE Λ lbl s c fs ∧ ArenaWr ar p lbl lsize Ctx s c fs ∧
    (WrAt s ar.ctrLoc → Ctx s c fs) ∧ RunWf p c fs ∧ AbortWf ar μ Ab Ac s c fs

/-- **The level before the allocation**: `Wf` at `L0`/`ls0`, the frames
none (the start: a pending tail call to `main`) or `[frM]`, the per-state
facts `X0` (those the maximal `inv0` owes at each of its states: off the
`clone`, the take's range) at the state. -/
def W0 (Λ : Scc.Sem.Layout) (μ : Marks) (own : Own) (ar : Arena) (p : Prog) (Dt Ab Cl Ac : State → Prop)
    (Ctx : FragS isaLSE2) (L0 : Lbl) (ls0 : Lsize) (frM : TermRun.Frame) (X0 : State → Prop) : FragS isaLSE2 :=
  fun s c fs => (fs = [] ∨ fs = [frM]) ∧ X0 s ∧ Wf Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 s c fs

/-- **The level after the allocation** of label `l` at base `b`, `n`
cells: `Wf` at `upd L0 l b`/`updN ls0 l n`, writing no counter (the
context is empty: wake's one allocation comes before the level, so no state
after it is the counter's add; `_Ctx` is kept for the signature). -/
def W1 (Λ : Scc.Sem.Layout) (μ : Marks) (own : Own) (ar : Arena) (p : Prog) (Dt Ab Cl Ac : State → Prop)
    (_Ctx : FragS isaLSE2) (L0 : Lbl) (ls0 : Lsize) (l : WeakMem.AllocLabel) (b n : Nat) : FragS isaLSE2 :=
  Wf Λ μ own ar p Dt Ab Cl Ac (fun _ _ _ => False) (A64ConsumerA.upd L0 l b) (A64ConsumerA.updN ls0 l n)

/-- **wake's write tail**: no `write` to the output at the state (the
abort stubs' `write`s, to fd 2, inside the fragments, are in it). -/
def DtW (s : State) : Prop :=
  ∀ buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n)

/-- **`WakeO.OPrem.hdt` at `DtW`.** -/
theorem hdtW : ∀ s buf n, DtW s → Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n) :=
  fun _ buf n h => h buf n

/-- **`DtW` at a `write` to the error output**: `x0 = 2`, `x8 = 64`. -/
theorem dtW_of_fd2 {s : State} (h0 : s.st.1.regs.X0 = 2) (h8 : s.st.1.regs.X8 = 64) : DtW s := by
  intro buf n hd
  simp [abi, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.a64, h0, h8, Scc.Sem.A64.xRegs] at hd

/-- **The state's facts at a larger write tail** (`SFactsSt2`'s `wrTail`
the only field reading it), e.g. from the default `Dt := False` to `DtW`. -/
theorem SFactsSt2.mono_dt {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {s : State} {Dt Dt' : State → Prop}
    (h : SFactsSt2 Λ μ own s Dt) (hd : Dt s → Dt' s) : SFactsSt2 Λ μ own s Dt' :=
  { h with wrTail := fun ha fd buf n hc => hd (h.wrTail ha fd buf n hc) }

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {ar : Arena} {p : Prog} {Dt Ab Cl Ac : State → Prop}
  {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {J : InvS}

/-- **`SFactsACH` at a state of `Wf`** (`SFactsACH.ofSt`), the counter
add's row at the state given (`hctr`, needed only where the instruction
writes the counter, so in `Ctx`), and the box's initialising store's
premises (`hnew`, needed only at a write off the arena, so in `Ctx` writing
no counter). -/
theorem hWf_at {s : State} {c : Ctl} {fs : List TermRun.Frame} (h : Wf Λ μ own ar p Dt Ab Cl Ac Ctx lbl lsize s c fs)
    (hctr : Ctx s c fs → WrAt s ar.ctrLoc → ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow (msOfA Λ μ rd G (fun s _ => own s) ar J lbl lsize fs') (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c')
    (hnew : Ctx s c fs → ¬ WrAt s ar.ctrLoc → ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      ∀ L, WrAt s L → ¬ ArenaW ar lbl lsize c' L →
        NewStM p lbl (msOfA Λ μ rd G (fun s _ => own s) ar J lbl lsize fs') s c') :
    SFactsACH Λ μ p rd G (fun s _ => own s) ar J lbl lsize s c fs Dt Ab Cl Ac := by
  obtain ⟨hst, hab, hac, hcl, hnr, hpl, hn, hcx, hr, habt⟩ := h
  refine SFactsACH.ofSt hst hab hac hcl hnr hr.cell hpl (fun c' fs' hrun hsys hL => hctr (hcx hL) hL c' fs' hrun hsys)
    (fun c' fs' hrun hsys L hL => ?_) hr.zero habt
  by_cases hc : L = ar.ctrLoc
  · exact .inl (.inl hc)
  by_cases ha : ArenaW ar lbl lsize c' L
  · exact .inl ha
  · obtain ⟨hC, hnc⟩ := (hn c' fs' hrun L hL hc).resolve_left ha
    exact .inr (hnew hC hnc c' fs' hrun hsys L hL ha)

/-- **`WakeO.OPrem.hW0`'s shape**: `SFactsACH` at every state of `W0` under
a guard `P` (`inv0`), at the levels `L0`/`ls0`, given the counter row and
the box's store's premises at the guard's states in `Ctx`. -/
theorem hW0 {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop} {P : FragS isaLSE2}
    (hctr : ∀ s c fs, P s c fs → Ctx s c fs → WrAt s ar.ctrLoc → ∀ c' fs', FrameRun p (c, fs) (c', fs') →
      abi.atSys s = false →
      CtrRow (msOfA Λ μ rd G (fun s _ => own s) ar J L0 ls0 fs') (fun s' c'' => PendA p J L0 ls0 s' c'' fs') s c')
    (hnew : ∀ s c fs, P s c fs → Ctx s c fs → ¬ WrAt s ar.ctrLoc → ∀ c' fs', FrameRun p (c, fs) (c', fs') →
      abi.atSys s = false → ∀ L, WrAt s L → ¬ ArenaW ar L0 ls0 c' L →
        NewStM p L0 (msOfA Λ μ rd G (fun s _ => own s) ar J L0 ls0 fs') s c') :
    ∀ s c fs, P s c fs → W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM X0 s c fs →
      SFactsACH Λ μ p rd G (fun s _ => own s) ar J L0 ls0 s c fs Dt Ab Cl Ac :=
  fun s c fs hP h => hWf_at h.2.2 (hctr s c fs hP) (hnew s c fs hP)

/-- **`WakeO.OPrem.hW1`'s shape** with no premise: `SFactsACH` at every
state of `W1 l b n` at the updated levels (`W1` writes no counter). -/
theorem hW1F {L0 : Lbl} {ls0 : Lsize} :
    ∀ l b n s c fs, W1 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 l b n s c fs →
      SFactsACH Λ μ p rd G (fun s _ => own s) ar J (A64ConsumerA.upd L0 l b) (A64ConsumerA.updN ls0 l n) s c fs Dt Ab Cl Ac :=
  fun _ _ _ _ _ _ h => hWf_at h nofun nofun

/-- **`WakeO.OPrem.hW1`'s shape** under a guard `Q` (`hW1F`; the counter
row `_hctr` is not used, kept for the signature). -/
theorem hW1 {L0 : Lbl} {ls0 : Lsize} {Q : WeakMem.AllocLabel → Nat → Nat → Prop}
    (_hctr : ∀ l b n, Q l b n → ∀ s c fs, Ctx s c fs → ∀ c' fs', FrameRun p (c, fs) (c', fs') →
      abi.atSys s = false →
      CtrRow (msOfA Λ μ rd G (fun s _ => own s) ar J (A64ConsumerA.upd L0 l b) (A64ConsumerA.updN ls0 l n) fs')
        (fun s' c'' => PendA p J (A64ConsumerA.upd L0 l b) (A64ConsumerA.updN ls0 l n) s' c'' fs') s c') :
    ∀ l b n s c fs, Q l b n → W1 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 l b n s c fs →
      SFactsACH Λ μ p rd G (fun s _ => own s) ar J (A64ConsumerA.upd L0 l b) (A64ConsumerA.updN ls0 l n) s c fs Dt Ab Cl Ac :=
  fun l b n s c fs _ h => hW1F l b n s c fs h

end Spike.Lib.A64.WakeWf

/-- info: 'Spike.Lib.A64.WakeWf.hWf_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.hWf_at

/-- info: 'Spike.Lib.A64.WakeWf.hW0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.hW0

/-- info: 'Spike.Lib.A64.WakeWf.hW1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.hW1

/-- info: 'Spike.Lib.A64.WakeWf.hW1F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.hW1F

/-- info: 'Spike.Lib.A64.WakeWf.dtW_of_fd2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.dtW_of_fd2
