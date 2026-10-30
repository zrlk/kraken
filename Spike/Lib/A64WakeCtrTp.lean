/-
**The counter row at a context carrying the thread pointer** (AArch64): `WakeCtr.hctr0_of` at the context `CtxT`, whose counter-add
disjunct also holds `TP t` at the state. The add (`ldadd`, no `MSR`) keeps
the thread pointer into every leaf (`KeepTP.exec_tp`), so the tail's
landing at `n4` (`hland`) may assume `TP t`.

- `CtxT`: `CtxW`'s shape with `TP t` on the counter add.
- `CtxT.ctxW`: `CtxT` is in `CtxW`.
- `hctr0_ofT`: `hctr0_of` at `CtxT`, `hland` under `TP t`.
-/
import Spike.Lib.A64WakeCtr
import Spike.Lib.A64Hello1RodataTP

namespace Spike.Lib.A64.WakeCtr

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Marks)
open Scc.Sem.A64 (abi)
open Spike.Lib (Region FrameRun MemSide Arena FragS)
open Spike.Lib.A64ConsumerA (CtrRow PendA WrAt msOfA I2)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Flow (At)
open Spike.Lib.A64.Alloc (Call Code N)
open Spike.Lib.A64.KeepTP (TP)

/-- **The context with the thread pointer at the counter add**: the
counter add (`CtrAt`) under `TP t`, or the box's store `St`. -/
def CtxT (ref : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64)
    (Gc : MemSide isaLSE2 → Region → (MachineData → Prop) → Call → Prop) (t : UInt64) (St : FragS isaLSE2) :
    FragS isaLSE2 :=
  fun s c fs => (CtrAt ref exe endPc Gc s c fs ∧ TP t s) ∨ St s c fs

variable {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Spike.Lib.A64ConsumerS.OwnS} {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {inv0 : FragS isaLSE2}
  {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {p : Prog} {St : FragS isaLSE2}
  {Gc : MemSide isaLSE2 → Region → (MachineData → Prop) → Call → Prop}
  {exe : _root_.Executable} {endPc : Int64} {t : UInt64}

/-- `CtxT` is in `CtxW`. -/
theorem CtxT.ctxW {ref : MemSide isaLSE2} {s : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}
    (h : CtxT ref exe endPc Gc t St s c fs) : CtxW ref exe endPc Gc St s c fs :=
  h.imp_left And.left

/-- **`OpenW.hctr0` at `Ctx := CtxT`**: as `hctr0_of`, the tail's landing at
`n4` (`hland`) under the thread pointer `t`, kept by the add (no `MSR`). -/
theorem hctr0_ofT (hcode : ∀ ms0 q, Code ms0 q exe endPc)
    (hSt : ∀ s c fs, St s c fs → ¬ WrAt s ar.ctrLoc)
    (hland : ∀ (ms0 : MemSide isaLSE2) R F q,
      ms0 = { msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) L0 ls0 [] with xa := ms0.xa } → Gc ms0 R F q →
      CtrOk ms0 (_root_.Executable.labels exe).label R F q →
      ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label ms0 q .n4) s c → TP t s → inv0 s c []) :
    ∀ s c fs, inv0 s c fs →
      CtxT (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) L0 ls0 []) exe endPc Gc t St s c fs →
      WrAt s ar.ctrLoc → ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0 fs')
        (fun s' c'' => PendA p (I2 ar L0 ls0 inv0 inv1) L0 ls0 s' c'' fs') s c' := by
  intro s c fs _ hC hW c' fs' hr _
  obtain ⟨⟨rfl, ms0, R, F, q, hms, hGc, hok, hAt⟩, htp⟩ := hC.resolve_right fun hS => hSt s c fs hS hW
  have hc : c = q.c0 := by obtain ⟨-, -, -, -, σ, -, -, ⟨h, -⟩, -⟩ := hAt; exact h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Spike.Lib.FrameNew.FrameRun.eq_of_new hr (hc ▸ hok.okb.term))
  have hnm : Spike.Lib.A64.KeepTP.NoMsrAt s := by
    obtain ⟨he, hn, -, hpc, -⟩ := id hAt
    exact Spike.Lib.A64.Flow.noMsrAt_of_code ((hcode ms0 q).rmw s he hn) (by decide) (j := 0) (by simp) rfl rfl
      (by rw [hpc]; simp)
  have hrow := ctrRow_allocS_n4 hok.fst hok.okb.toS (hcode ms0 q) hok.mem hAt
  refine ctrRow_xa ?_ (show _ = { ms0 with xa := _ } by rw [hms]; rfl)
  obtain ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, h7⟩ := hrow
  have hT := Spike.Lib.A64.KeepTP.exec_tp hnm htp h1
  refine ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, fun old hG hown hle hlo => ?_⟩
  obtain ⟨hG', hL⟩ := h7 old hG hown hle hlo
  refine ⟨hG', fun _ a h => ?_, _, _, .refl _, .inl ⟨rfl, rfl, ?_⟩⟩
  · revert h; rw [hc]; intro h
    have h2 : q.c0.term = .ret a := h
    rw [hok.okb.term] at h2
    cases h2
  · rcases hL with ⟨_, hj⟩ | ⟨y, _⟩
    · exact hland ms0 R F q hms hGc hok _ _ hj (hT old)
    · exact y.elim

end Spike.Lib.A64.WakeCtr

/-- info: 'Spike.Lib.A64.WakeCtr.CtxT.ctxW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeCtr.CtxT.ctxW

/-- info: 'Spike.Lib.A64.WakeCtr.hctr0_ofT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeCtr.hctr0_ofT
