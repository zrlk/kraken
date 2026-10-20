import Kraken.AArch64.EnvCfg
import Kraken.AArch64.Parser
import Kraken.Promising.SeqLinkAArch64Prog
import Kraken.Promising.EnvWPAArch64

/-!
# `CASP` over the AArch64 environment wp, carried to the Promising machine

Pair compare-and-swap (`CASP` and its ordering variants) on a 16-byte
"versioned pointer": a pointer at `[x0]` and a version counter at `[x0, #8]`,
both shared (outside `dmem`), two 8-byte locations of `lastWrite [(a, 8),
(a + 8, 8)]`. `AllEnv` reads `CASP` as the Promising machine performs it
(`SharedEnv.CaspEnv`: one `rmw` per half, in either order; not one atomic
16-byte access, `Kraken/Promising/EnvWP.md`, "Pair effects"); in `lastWrite`
that is one read of both halves and, on a match of both, both writes
(`casp_lastWrite_spec`, which `vcgen` uses there). Every theorem reaches the
Promising machine through `env_link_halt`, with no access-discipline premises.

* `vpBump` (loop-free): `ldp` both halves, then `caspal` expecting the
  halves just read and replacing them by `x1` and the version plus one. In `lastWrite` nothing
  changes the halves in between, so the `caspal` succeeds
  (`vpBump_correctEnv`, one `vcgen` call; `vpBump_promising`).
* `vpUpdate`, the retry loop: `ldp`, then `caspal` with the pointer `x1` and
  the version plus one, comparing the old halves `caspal` returns with the
  expected ones and retrying on a mismatch. Total correctness by
  `MachineWP.cfgEnv` with a real variant (`1` at `retry` while `x2:x3` is
  stale, `0` otherwise: a failed `caspal` refreshes `x2:x3`), as `casInc`
  (`EnvLSELoops.lean`): `vpUpdate_correctEnv`, `vpUpdate_terminates`,
  `vpUpdate_promising`.
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

/-- The two halves of the versioned pointer: two 8-byte locations. -/
abbrev vpL (a : BitVec 64) : SharedLayout := [(a, 8), (a + 8, 8)]

/-- The two-slot layout is well formed: the slots are adjacent, not overlapping. -/
theorem vpL_wf (a : BitVec 64) : SharedLayout.WF (vpL a) where
  pos _ _ h := by
    simp only [vpL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  le16 _ _ h := by
    simp only [vpL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  disj _ _ _ _ k ha hb h1 h2 := by
    simp only [vpL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ha hb
    rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | exact ⟨rfl, rfl⟩ | (exfalso; bv_omega)

/-- A slot of `L` that `hsplit` keeps out of `dmem` does not load from it. -/
private theorem loadInt_none_of_mem {d : MachineData} {L : SharedLayout} {a : BitVec 64} {n : Nat}
    (hn : 0 < n) (ha : (a, n) ∈ L) (hsplit : ∀ k, SharedLayout.Covers L k → d.dmem.get? k = none) :
    Mem.loadInt d.dmem a n = none := by
  cases hl : Mem.loadInt d.dmem a n with
  | none => rfl
  | some x =>
    have h0 := Mem.get?_isSome_of_loadBytes (Mem.loadBytes_isSome_of_loadInt hl) 0 hn
    rw [hsplit _ ⟨_, n, ha, by simpa using hn⟩] at h0
    cases h0

/-- The environment state reading `a` as the pointer's and every other address
as the version's final value in `mem` is related to `mem`. -/
private theorem envRel_vp (a : BitVec 64) (mem : Memory) :
    envRel (vpL a) (fun k => if k = a then mem.finalVal (sharedLoc a 8) else mem.finalVal (sharedLoc (a + 8) 8))
      mem := by
  intro b m hb
  simp only [vpL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hb
  rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp
  · simp

/-- The version's address is not the pointer's. -/
@[simp] private theorem add8_ne (a : BitVec 64) : (a + 8#64 = a) ↔ False := by
  constructor
  · intro h; bv_omega
  · exact False.elim

/-! ## Loop-free: one `caspal` after an `ldp` -/

/-- Read the versioned pointer at `[x0]` (`ldp`), then replace it by `x1` with
the version plus one (`caspal`). -/
def vpBump : Program := parseAArch64("
    ldp x2, x3, [x0]
    add x5, x3, #1
    mov x4, x1
    caspal x2, x3, x4, x5, [x0]
")

section vpBump

variable [layout : _root_.Layout]

local instance vpBump.env : CodeEnv := ⟨layout vpBump⟩

/-- `vpBump` in `lastWrite`: `x2:x3` receive the old pointer and version
`p:v`, and the halves become `x1:(v + 1)` (`ldp_shared_spec`, then
`casp_lastWrite_spec`). -/
theorem vpBump_correctEnv (a p v n : BitVec 64) :
    TripleEnv (SharedEnv.lastWrite (vpL a))
      (fun s g => s.regs.X0.toBitVec = a ∧ s.regs.X1.toBitVec = n ∧ Mem.loadInt s.dmem a 8 = none ∧
        Mem.loadInt s.dmem (a + 8) 8 = none ∧ (g a).setWidth 64 = p ∧ (g (a + 8)).setWidth 64 = v)
      vpBump
      (fun s g => s.regs.X2.toBitVec = p ∧ s.regs.X3.toBitVec = v ∧
        (g a).setWidth 64 = n ∧ (g (a + 8)).setWidth 64 = v + 1)
      (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold vpBump
  vcgen [ldp_shared_spec]
  all_goals simp_all [SharedEnv.lastWrite, SharedEnv.caspLW, SharedEnv.upd, MemWidth.bytesv]

variable [Executable.ValidLayout (layout vpBump)]

/-- **`vpBump` on the Promising machine.** A promise-free one-thread run from
`d`, both halves at `[x0]` shared (no bytes in `dmem`, the message-free memory
`mem` holding `p:v`): when the thread has reached the end of the text, `x2:x3`
is `p:v` and the halves' last writes are `x1:(v + 1)`. `vpBump_correctEnv`
through `env_link_halt`. -/
theorem vpBump_promising (A : Arch) (fuel : Nat) (showPc : Int64 → String) (d : MachineData)
    (p v : BitVec 64) (mem : Memory) (hm : mem.msgs = #[])
    (hsplit : ∀ k, SharedLayout.Covers (vpL d.regs.X0.toBitVec) k → d.dmem.get? k = none)
    (h_ptr : (mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)).setWidth 64 = p)
    (h_ver : (mem.finalVal (sharedLoc (d.regs.X0.toBitVec + 8) 8)).setWidth 64 = v)
    (c : Config isa)
    (hc : ReachablePF A fuel ⟨#[Thread.init ({
      exe := layout vpBump
      endPc := (layout vpBump).addrOf vpBump.length
      st := (d, Kraken.Layout.start Directive)
      showPc := showPc } : State)], mem⟩ c)
    (t' : Thread isa) (ht : c.threads = #[t'])
    (hend : t'.st.st.2 = (layout vpBump).addrOf vpBump.length) :
    t'.st.st.1.regs.X2.toBitVec = p ∧ t'.st.st.1.regs.X3.toBitVec = v ∧
      (c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)).setWidth 64 = d.regs.X1.toBitVec ∧
      (c.mem.finalVal (sharedLoc (d.regs.X0.toBitVec + 8) 8)).setWidth 64 = v + 1 := by
  have hn₁ := loadInt_none_of_mem (L := vpL d.regs.X0.toBitVec) (a := d.regs.X0.toBitVec) (n := 8)
    (by decide) (by simp) hsplit
  have hn₂ := loadInt_none_of_mem (L := vpL d.regs.X0.toBitVec) (a := d.regs.X0.toBitVec + 8) (n := 8) (by decide)
    (by simp) hsplit
  have henv := envRel_vp d.regs.X0.toBitVec mem
  have hev := Program.instrStepEnv_of_tripleEnv
    (vpBump_correctEnv d.regs.X0.toBitVec p v d.regs.X1.toBitVec) (s := d)
    (g := fun k => if k = d.regs.X0.toBitVec then mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)
      else mem.finalVal (sharedLoc (d.regs.X0.toBitVec + 8) 8))
    ⟨rfl, rfl, hn₁, hn₂, by simp [h_ptr], by simpa using h_ver⟩
  obtain ⟨g', hrel', hP⟩ := env_link_halt _ (layout vpBump) (vpL_wf _) A fuel _ showPc d _ mem _ _ hm
    hsplit henv (fun x hx => hx.elim And.left False.elim) (step1W_stop_of_end _) hev c hc t' ht hend
  obtain ⟨-, hx2, hx3, hp, hv⟩ := hP.resolve_right id
  have h1 := hrel' d.regs.X0.toBitVec 8 (by simp)
  have h2 := hrel' (d.regs.X0.toBitVec + 8) 8 (by simp)
  exact ⟨hx2, hx3, by rw [← hp]; exact h1.symm, by rw [← hv]; exact h2.symm⟩

end vpBump

/-! ## The `caspal` retry loop -/

/-- Read the versioned pointer at `[x0]`, then try to replace it by `x1` with
the version plus one; `caspal` returns the halves it found in `x2:x3`, which
are compared (`eor`/`orr`) with the expected ones saved in `x6:x7`, retrying on
a mismatch (with the halves just returned as the new expectation). -/
def vpUpdate : Program := parseAArch64("
start:
    ldp x2, x3, [x0]
retry:
    mov x6, x2
    mov x7, x3
    add x5, x3, #1
    mov x4, x1
    caspal x2, x3, x4, x5, [x0]
    eor x8, x2, x6
    eor x9, x3, x7
    orr x8, x8, x9
    cbnz x8, retry
")

section vpUpdate

variable [layout : _root_.Layout] [Executable.ValidLayout (layout vpUpdate)]

local instance vpUpdate.env : CodeEnv := ⟨layout vpUpdate⟩

/-- The loop's table: at both labels the halves are shared and hold `p:v`, and
`x0`/`x1` are the address and the new pointer; `x2:x3` is unconstrained at
`retry`. -/
private abbrev vpUpdate_table (a n p v : BitVec 64) :
    Label → MachineData → (SharedEnv.lastWrite (vpL a)).State → Prop :=
  fun l s g => (l = "start" ∨ l = "retry") ∧
    s.regs.X0.toBitVec = a ∧ s.regs.X1.toBitVec = n ∧ Mem.loadInt s.dmem a 8 = none ∧
    Mem.loadInt s.dmem (a + 8) 8 = none ∧ (g a).setWidth 64 = p ∧ (g (a + 8)).setWidth 64 = v

/-- The variant: `1` at `retry` while `x2:x3` is stale, `0` otherwise. -/
private abbrev vpUpdate_var (a p v : BitVec 64) :
    Label → MachineData → (SharedEnv.lastWrite (vpL a)).State → Nat :=
  fun l s _ => if l = "retry" ∧ (s.regs.X2.toBitVec ≠ p ∨ s.regs.X3.toBitVec ≠ v) then 1 else 0

/-- From the shared halves at `a = x0` holding `p:v`, the loop ends with `p:v`
in `x2:x3` and `x1:(v + 1)` in the halves: `cfgEnv` with the variant
`vpUpdate_var`, one `vcgen` call per block. -/
theorem vpUpdate_correctEnv (a n p v : BitVec 64) :
    TripleEnv (SharedEnv.lastWrite (vpL a))
      (fun s g => s.regs.X0.toBitVec = a ∧ s.regs.X1.toBitVec = n ∧ Mem.loadInt s.dmem a 8 = none ∧
        Mem.loadInt s.dmem (a + 8) 8 = none ∧ (g a).setWidth 64 = p ∧ (g (a + 8)).setWidth 64 = v)
      vpUpdate
      (fun s g => s.regs.X2.toBitVec = p ∧ s.regs.X3.toBitVec = v ∧
        (g a).setWidth 64 = n ∧ (g (a + 8)).setWidth 64 = v + 1)
      (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv (vpUpdate_table a n p v) (vpUpdate_var a p v)
    (hP := by funext s g; simp [vpUpdate_table])
  cfg_cases_env [vpUpdate]
  all_goals intro m
  all_goals vcgen [ldp_shared_spec]
  all_goals obtain ⟨_, rfl⟩ := ‹_ ∧ _ = m›
  all_goals simp_all [SharedEnv.lastWrite, SharedEnv.caspLW_apply, SharedEnv.upd, MemWidth.bytesv]
  all_goals (repeat' split) <;> simp_all
  exact Table.ofLabelsEnv_at ⟨.inr rfl, by
    simp only [SharedEnv.caspLW_apply]; split <;> simp_all [MemWidth.bytesv]⟩

/-- **Termination at the machine.** From the start address, every run of
`vpUpdate` in `lastWrite` reaches the end of the text, with `p:v` in `x2:x3`
and `x1:(v + 1)` as the halves' values. -/
theorem vpUpdate_terminates (d : MachineData) (g : (SharedEnv.lastWrite (vpL d.regs.X0.toBitVec)).State)
    (p v : BitVec 64) (hn₁ : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = none)
    (hn₂ : Mem.loadInt d.dmem (d.regs.X0.toBitVec + 8) 8 = none)
    (h_ptr : (g d.regs.X0.toBitVec).setWidth 64 = p) (h_ver : (g (d.regs.X0.toBitVec + 8)).setWidth 64 = v) :
    Eventually ((layout vpUpdate).instrStepEnv (SharedEnv.lastWrite (vpL d.regs.X0.toBitVec)))
      (fun x => x.1.2 = (layout vpUpdate).addrOf vpUpdate.length ∧
        x.1.1.regs.X2.toBitVec = p ∧ x.1.1.regs.X3.toBitVec = v ∧
        (x.2 d.regs.X0.toBitVec).setWidth 64 = d.regs.X1.toBitVec ∧
        (x.2 (d.regs.X0.toBitVec + 8)).setWidth 64 = v + 1)
      ((d, Kraken.Layout.start Directive), g) :=
  eventually_weaken _ _ _ _ (fun _ h => h.resolve_right id)
    (Program.instrStepEnv_of_tripleEnv (vpUpdate_correctEnv d.regs.X0.toBitVec d.regs.X1.toBitVec p v)
      ⟨rfl, rfl, hn₁, hn₂, h_ptr, h_ver⟩)

/-- **The `caspal` retry loop on the Promising machine.** A promise-free
one-thread run of `vpUpdate` from `d`, both halves at `[x0]` shared (no bytes
in `dmem`, the message-free memory `mem` holding `p:v`): when the thread has
reached the end of the text, `x2:x3` is `p:v` and the halves' last writes are
`x1:(v + 1)`. `vpUpdate_correctEnv` through `env_link_halt`. -/
theorem vpUpdate_promising (A : Arch) (fuel : Nat) (showPc : Int64 → String) (d : MachineData)
    (p v : BitVec 64) (mem : Memory) (hm : mem.msgs = #[])
    (hsplit : ∀ k, SharedLayout.Covers (vpL d.regs.X0.toBitVec) k → d.dmem.get? k = none)
    (h_ptr : (mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)).setWidth 64 = p)
    (h_ver : (mem.finalVal (sharedLoc (d.regs.X0.toBitVec + 8) 8)).setWidth 64 = v)
    (c : Config isa)
    (hc : ReachablePF A fuel ⟨#[Thread.init ({
      exe := layout vpUpdate
      endPc := (layout vpUpdate).addrOf vpUpdate.length
      st := (d, Kraken.Layout.start Directive)
      showPc := showPc } : State)], mem⟩ c)
    (t' : Thread isa) (ht : c.threads = #[t'])
    (hend : t'.st.st.2 = (layout vpUpdate).addrOf vpUpdate.length) :
    t'.st.st.1.regs.X2.toBitVec = p ∧ t'.st.st.1.regs.X3.toBitVec = v ∧
      (c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)).setWidth 64 = d.regs.X1.toBitVec ∧
      (c.mem.finalVal (sharedLoc (d.regs.X0.toBitVec + 8) 8)).setWidth 64 = v + 1 := by
  have hn₁ := loadInt_none_of_mem (L := vpL d.regs.X0.toBitVec) (a := d.regs.X0.toBitVec) (n := 8)
    (by decide) (by simp) hsplit
  have hn₂ := loadInt_none_of_mem (L := vpL d.regs.X0.toBitVec) (a := d.regs.X0.toBitVec + 8) (n := 8)
    (by decide) (by simp) hsplit
  have henv := envRel_vp d.regs.X0.toBitVec mem
  have hev := Program.instrStepEnv_of_tripleEnv
    (vpUpdate_correctEnv d.regs.X0.toBitVec d.regs.X1.toBitVec p v) (s := d)
    (g := fun k => if k = d.regs.X0.toBitVec then mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)
      else mem.finalVal (sharedLoc (d.regs.X0.toBitVec + 8) 8))
    ⟨rfl, rfl, hn₁, hn₂, by simp [h_ptr], by simpa using h_ver⟩
  obtain ⟨g', hrel', hP⟩ := env_link_halt _ (layout vpUpdate) (vpL_wf _) A fuel _ showPc d _ mem _ _ hm
    hsplit henv (fun x hx => hx.elim And.left False.elim) (step1W_stop_of_end _) hev c hc t' ht hend
  obtain ⟨-, hx2, hx3, hp, hv⟩ := hP.resolve_right id
  have h1 := hrel' d.regs.X0.toBitVec 8 (by simp)
  have h2 := hrel' (d.regs.X0.toBitVec + 8) 8 (by simp)
  exact ⟨hx2, hx3, by rw [← hp]; exact h1.symm, by rw [← hv]; exact h2.symm⟩

end vpUpdate

end MachineWP
