/-
**The hello1 frame `WordsNone hello1Λ ∧ F₀` at a reachable thread** (x86-64):
connecting the G path's frame (`hwn` of `hello1_rodata_setupGW_priv`,
`hello1_mainS_segGW_priv`) to the consumer's thread state. For a thread of
a configuration reached from `hello1`'s load, every node fragment `At … F₀`
of its state is one of `At … (WordsNone hello1Λ ∧ F₀)` (`hello1_wordsNone`),
the frame `FStable` for a region in the entry stack or the stack pool when
`F₀` is (`Alloc.wordsNone_and_fstable`), and `hwn` its first conjunct. At
the entry stack's region `entryR Entry.linux` the side condition is
discharged (`hello1_frame_entry`).
-/
import Spike.Lib.X64Hello1SetupPriv
import Spike.Test.X64DmemPrivHello1
import Spike.Lib.RegionCells
import Spike.Lib.Rt.X64Layout

namespace Spike.Test.X64FrameHello1

open Kraken Kraken.Promising Scc.Sem Spike.Lib Spike.Lib.DmemPriv SccCode
open Spike.Lib.X64 (At FStable)

/-- **A reachable thread's node fragment carries `WordsNone hello1Λ`.** -/
theorem hello1_at_wordsNone {n : Nat} {μ : Marks} {syms : List (String × Nat)} {mem : List (Loc × Val)}
    {tr : List Ev} {c : (Scc.Sem.X64.machine (Scc.Sem.X64.kernel n)).Cfg}
    (hrun : (Scc.Sem.X64.machine (Scc.Sem.X64.kernel n)).Run μ
      (Scc.Sem.X64.loadProg (Scc.Sem.X64.kernel n) Entry.linux hello1Λ hello1Cells syms mem) tr c)
    {tid : Nat} {t : Thread Kraken.Promising.X64.isa} (htid : c.1.threads[tid]? = some t)
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F₀ : MachineData → Prop}
    {nd : Spike.Lib.X64.ND} {cc : Ctl}
    (h : At exe endPc R F₀ nd t.st cc) :
    At exe endPc R (fun m => WordsNone hello1Λ m.dmem ∧ F₀ m) nd t.st cc := by
  obtain ⟨h1, h2, h3, h4, σ, hA, hF, hJ⟩ := h
  exact ⟨h1, h2, h3, h4, σ, hA, ⟨Spike.Test.X64DmemPrivHello1.hello1_wordsNone syms mem hrun htid, hF⟩, hJ⟩

/-- **The frame's `FStable` and `hwn` at `hello1Λ`**, for a region in the
entry stack or the stack pool. -/
theorem hello1_frame {R : Region} {F₀ : MachineData → Prop} (hR : R.OK)
    (hS : Range.Sub ⟨(R.base.toNat + R.lo).toNat, (R.hi - R.lo).toNat⟩ Entry.linux.stack ∨
      Range.Sub ⟨(R.base.toNat + R.lo).toNat, (R.hi - R.lo).toNat⟩ hello1Λ.stackPool)
    (h₀ : FStable R F₀) :
    FStable R (fun m => WordsNone hello1Λ m.dmem ∧ F₀ m) ∧
      ∀ m, WordsNone hello1Λ m.dmem ∧ F₀ m → WordsNone hello1Λ m.dmem :=
  Spike.Lib.X64.Alloc.wordsNone_and_fstable hello1Λ_wf Spike.Test.X64DmemPrivHello1.hello1_clear hR hS h₀

/-- The Linux entry is admissible for `hello1Λ`. -/
theorem hello1_entry_ok : Entry.linux.Ok hello1Λ := by decide +kernel

/-- **The frame at the entry stack's region** (`entryR`, the region of the
segments before the stack switch): `hS` from `cellsR_entry`. A callee's
region inherits `FStable` (`FStable.callee`); a region in the taken stack
`rS0 L` takes `hS` from `rS0_sub` (`sub_trans`). -/
theorem hello1_frame_entry {F₀ : MachineData → Prop}
    (h₀ : FStable (Spike.Lib.X64.Rt.entryR Entry.linux) F₀) :
    FStable (Spike.Lib.X64.Rt.entryR Entry.linux) (fun m => WordsNone hello1Λ m.dmem ∧ F₀ m) ∧
      ∀ m, WordsNone hello1Λ m.dmem ∧ F₀ m → WordsNone hello1Λ m.dmem :=
  hello1_frame (Spike.Lib.X64.Rt.entryR_ok hello1_entry_ok) (.inl (cellsR_entry hello1_entry_ok)) h₀

/-- **The frame at a region in the first stack** `rS0 L` (the regions after
the stack switch) of a runtime layout over `hello1Λ`: `hS` from `rS0_sub`. -/
theorem hello1_frame_rS0 {L : Spike.Lib.X64.Rt.RuntimeLayout} (hL : L.Λ = hello1Λ) {R : Region}
    {F₀ : MachineData → Prop} (hR : R.OK) (hsub : (cellsR R).Sub (Spike.Lib.X64.Rt.rS0 L))
    (h₀ : FStable R F₀) :
    FStable R (fun m => WordsNone hello1Λ m.dmem ∧ F₀ m) ∧
      ∀ m, WordsNone hello1Λ m.dmem ∧ F₀ m → WordsNone hello1Λ m.dmem :=
  hello1_frame hR (.inr (hL ▸ sub_trans hsub (Spike.Lib.X64.Rt.rS0_sub L))) h₀

end Spike.Test.X64FrameHello1
