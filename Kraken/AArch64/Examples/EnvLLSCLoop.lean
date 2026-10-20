import Kraken.AArch64.EnvCfg
import Kraken.AArch64.Parser
import Kraken.Promising.EnvLinkSafeAArch64

/-!
# An `LDXR`/`STXR` retry loop, by control flow and carried to the Promising machine

`llscInc` increments the shared slot at `[x0]` with an exclusive pair and
`cbnz`-retries while the `stxr` fails. In `SharedEnv.lastWrite` a store-exclusive
may fail at any time, so the loop is only partially correct: some runs fail
forever. And a failed iteration can come back to `retry` in exactly the state it
started from, so the zero-step guard of `MachineWP.cfgEnv_partial` cannot be
discharged over `lastWrite` itself. The proof therefore runs in
`SharedEnv.counted (SharedEnv.lastWrite L)`, which also counts shared accesses:
every iteration moves the counter by two, so the back edge never returns to the
entry snapshot.

* `llscInc_correctCounted`: `cfgEnv_partial` with the one-label table at
  `retry`, `cfg_cases_env` and `vcgen`; the back edge is the only goal that
  needs the counter.
* `llscInc_promising`: `PartialTripleEnv.uncount` projects the counter away,
  `Program.instrStepEnv_of_partialTripleEnv` reads the triple as `Safely` from
  the start address, and `env_link_halt_safe` carries it to the Promising
  machine: every promise-free one-thread run that reaches the end of the text
  has read `v` into `x2` and left `v + 1` as the slot's last write. Runs that
  never reach the end are not constrained.
-/

open Std.WP
open Kraken
open Kraken.Promising
open Kraken.Promising.AArch64
open MachineWP

namespace MachineWP

set_option mvcgen.warning false
set_option experimental.vcgen true

open Kraken.AArch64.Parser

/-- Increment the shared counter at `[x0]` with an exclusive pair, retrying
while the store-exclusive fails. -/
def llscInc : Program := parseAArch64("
retry:
    ldxr x2, [x0]
    add x3, x2, #1
    stxr w4, x3, [x0]
    cbnz w4, retry
")

/-- The slot layout of `llscInc` is well formed. -/
theorem llscInc_layout_wf (a : BitVec 64) : SharedLayout.WF [(a, 8)] where
  pos _ _ h := by rw [List.mem_singleton] at h; cases h; decide
  le16 _ _ h := by rw [List.mem_singleton] at h; cases h; decide
  disj _ _ _ _ _ ha hb _ _ := by
    rw [List.mem_singleton] at ha hb
    cases ha; cases hb
    exact ⟨rfl, rfl⟩

variable [layout : _root_.Layout] [Executable.ValidLayout (layout llscInc)]

local instance llscInc.env : CodeEnv := ⟨layout llscInc⟩

/-- The loop's table: at `retry` the counter is shared and holds `v`. -/
private abbrev llscInc_table (a v : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.lastWrite [(a, 8)])).State → Prop
  | "retry", s, g => s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 8 = none ∧ (g.1 a).setWidth 64 = v
  | _, _, _ => False

theorem llscInc_correctCounted (a v : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.lastWrite [(a, 8)]))
      (fun s g => s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 8 = none ∧ (g.1 a).setWidth 64 = v)
      llscInc
      (fun s g => s.regs.X2.toBitVec = v ∧ (g.1 a).setWidth 64 = v + 1)
      (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (llscInc_table a v)
  cfg_cases_env [llscInc]
  intro s₀ g₀
  vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.tick_load, SharedEnv.tick_store] at *
  all_goals simp_all [SharedEnv.lastWrite, and_assoc]
  -- The back edge: a failed `stxr` leaves memory alone, but the counter has
  -- moved by two, so the loop head is never re-entered in the entry state.
  obtain ⟨hx, hc⟩ := ‹_ ∧ Prod.snd _ = Prod.snd _ + 1 + 1›
  refine Table.ofLabelsEnv_at ⟨rfl, ⟨by simp_all, by simp_all, by simp_all⟩, .inr fun _ hg => ?_⟩
  subst hg
  omega

/-- **`llscInc` on the Promising machine.** A promise-free one-thread run of
`llscInc` from `d`, the slot at `[x0]` shared (no bytes in `dmem`, its value
`v` in the message-free memory `mem`): if the thread has reached the end of the
text, `x2` is `v` and the slot's last write is `v + 1`. Partial correctness
only: runs that keep failing the `stxr` never reach the end and are not
constrained. `llscInc_correctCounted`, with the counter projected away, through
`env_link_halt_safe`. -/
theorem llscInc_promising (A : Arch) (fuel : Nat) (showPc : Int64 → String) (d : MachineData)
    (v : BitVec 64) (mem : Memory) (hm : mem.msgs = #[])
    (hsplit : ∀ k, SharedLayout.Covers [(d.regs.X0.toBitVec, 8)] k → d.dmem.get? k = none)
    (h_slot : (mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)).setWidth 64 = v)
    (c : Config isa)
    (hc : ReachablePF A fuel ⟨#[Thread.init ({
      exe := layout llscInc
      endPc := (layout llscInc).addrOf llscInc.length
      st := (d, Kraken.Layout.start Directive)
      showPc := showPc } : State)], mem⟩ c)
    (t' : Thread isa) (ht : c.threads = #[t'])
    (hend : t'.st.st.2 = (layout llscInc).addrOf llscInc.length) :
    t'.st.st.1.regs.X2.toBitVec = v ∧
      (c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)).setWidth 64 = v + 1 := by
  have hnone : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = none := by
    cases hl : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 with
    | none => rfl
    | some x =>
      have h0 := Mem.get?_isSome_of_loadBytes (Mem.loadBytes_isSome_of_loadInt hl) 0 (by decide)
      rw [hsplit _ ⟨_, 8, List.mem_singleton_self _, by simp⟩] at h0
      cases h0
  let g : BitVec 64 → BitVec 128 := fun _ => mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)
  have henv : envRel [(d.regs.X0.toBitVec, 8)] g mem := by
    intro a n ha
    rw [List.mem_singleton] at ha
    cases ha
    rfl
  have hev := Program.instrStepEnv_of_partialTripleEnv
    (llscInc_correctCounted d.regs.X0.toBitVec v).uncount (s := d) (g := g)
    ⟨0, rfl, hnone, h_slot⟩
  obtain ⟨g', hrel', hP⟩ := env_link_halt_safe _ (layout llscInc) (llscInc_layout_wf _) A fuel _
    showPc d _ mem g _ hm hsplit henv (fun x hx => hx.elim And.left fun ⟨_, h⟩ => h.elim)
    (not_instrStepEnv_of_end _) hev c hc t' ht hend
  obtain ⟨-, _, hx2, hslot⟩ := hP.resolve_right fun ⟨_, h⟩ => h
  refine ⟨hx2, ?_⟩
  have := hrel' _ 8 (List.mem_singleton_self _)
  rw [← hslot]
  exact this.symm

end MachineWP
