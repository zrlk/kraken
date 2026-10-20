/-
**The x64 `ticketlock2.kl` worker
verbatim, by `vcgen`**, in the protocol environment `tk2Env`
(`EnvG/TicketX2Env.lean`).

The worker of `Kraken/Examples/LockFree/X64/ticketlock2.kl` as written, with
the absolute operands `(next)`, `(owner)`, `(counter)` (`tk2WorkerV`), run in
its image `tk2ImageV`: the code followed by the `.kl` runner's data trailer
(`tk2DataV`, the same symbols in the same order as `ticketlock3.kl`'s).

- `inc32_abs_shared_spec`: the `vcgen` rule of `incl (sym)` on a shared
  location (a plain 4-byte load, then a plain 4-byte store of the low word
  plus one; `LRX64VCGen.inc32_shared_spec` at `(sym)`).
- **`tk2WorkerV_envG`**: the worker's run in the counted
  `(tk2Env x o c).within (tkS x o c)`, three-label table (`worker`: phase
  `0`; `spin`: phase `1` with the ticket in `%eax`; `done`: phase `6`).
-/
import Kraken.Promising.SLR.EnvG.TicketX2Final
import Kraken.Promising.SLR.EnvG.TicketXPublic

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.TicketX2

open Kraken.Promising.SLR.EnvG.TicketX2 (tk2Env TkSt lo inc tk2Env_ok_load tk2Env_ok_store tk2Env_ok_rmw
  tk2Env_step_load tk2Env_step_store tk2Env_step_rmw)
open Kraken.Promising.X64.EnvG.TicketX (tkS FrameTk)

/-! ## The `incl (sym)` rule -/

section AbsInc

open Lean.Order

/-- **`incl (sym)` on a location outside `dmem`**, any environment: a plain
4-byte load, then a plain 4-byte store of the old low word plus one at the
env state after the load; the tail runs with every flag value
(`inc32_shared` at `(sym)`). -/
theorem inc32_abs_shared [CodeEnv] (env : SharedEnv) (l : Label) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop} :
    TripleEnv env
      (fun s g =>
        let a := absAddr l
        Mem.loadInt s.dmem a 4 = none ∧ env.ok (.load .plain false a 4) g ∧
          ∀ v g', env.step (.load .plain false a 4) g v g' →
            env.ok (.store .plain false a 4 ((v.setWidth 32 + 1).setWidth 128)) g' ∧
            ∀ ok g'', env.step (.store .plain false a 4 ((v.setWidth 32 + 1).setWidth 128)) g' ok g'' →
              ∀ st : StatusFlags, cenv.wpEnv env p Q E { s with status := st } g'')
      (Directive.instr (.regular .W64 .W32 (.inc (.mem ⟨none, none, .label l⟩))) :: p)
      Q E := by
  intro s g ⟨hnone, hok, hk⟩ pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  rw [show cenv.after pc (Directive.instr (.regular .W64 .W32 (.inc (.mem ⟨none, none, .label l⟩))) :: p)
      = cenv.after (pc + .ofNat z) p by simp only [Executable.after, hseg]]
  refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.set,
    MachineData.load, MachineData.store, Effects.AllEnv]
  simp only [AddrExpr.zeroExtend_interp_abs_label, Width.bytes, hnone, Effects.AllEnv]
  exact ⟨hok, fun v g' hs => ⟨(hk v g' hs).1, fun ok g'' hs' => (hk v g' hs).2 ok g'' hs' _ _ hpl'⟩⟩

/-- `inc32_abs_shared` as a `vcgen` rule (not global:
`vcgen [inc32_abs_shared_spec]`). -/
theorem inc32_abs_shared_spec [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} {p : Program} (l : Label) :
    ⦃ fun s g =>
        let a := absAddr l
        (Mem.loadInt s.dmem a 4 = none) ⊓ env.ok (.load .plain false a 4) g ⊓
          (∀ v g', env.step (.load .plain false a 4) g v g' →
            env.ok (.store .plain false a 4 ((v.setWidth 32 + 1).setWidth 128)) g' ⊓
            ∀ ok g'', env.step (.store .plain false a 4 ((v.setWidth 32 + 1).setWidth 128)) g' ok g'' →
              ∀ st : StatusFlags, WP.wp (⟨p⟩ : EnvProgram env) Q E { s with status := st } g'') ⦄
      (⟨Directive.instr (.regular .W64 .W32 (.inc (.mem ⟨none, none, .label l⟩))) :: p⟩ :
        EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1, h.1.2, h.2⟩)
    (inc32_abs_shared env l)

end AbsInc

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program and its image -/

/-- **The x64 ticket lock worker of `ticketlock2.kl`, verbatim** (its `code`
block): the release is an unlocked `incl (owner)`. -/
def tk2WorkerV : Program := parse("
worker:
  movl $1,%eax
  lock xaddl %eax,(next)
spin:
  movl (owner),%ecx
  cmpl %eax,%ecx
  jne spin
  movl (counter),%edx
  addl $1,%edx
  movl %edx,(counter)
  incl (owner)
  jmp done
done:
")

/-- The `.kl` runner's data trailer of `ticketlock2.kl`: each symbol a label
behind a padding cell, in the order of first mention (`next`, `owner`,
`counter`). -/
def tk2DataV : Program :=
  [.byteArray (.mk #[]), .label "next", .byteArray (.mk #[]), .label "owner", .byteArray (.mk #[]),
    .label "counter"]

/-- The worker's image: the code, then the data trailer. -/
def tk2ImageV : Program := tk2WorkerV ++ tk2DataV

/-- info: 13 -/
#guard_msgs in
#eval tk2WorkerV.length

/-- The release parses as `incl` of the absolute operand `(owner)`. -/
example : tk2WorkerV[10]? =
    some (.instr (.regular .W64 .W32 (.inc (.mem ⟨none, none, .label "owner"⟩)))) := by decide

theorem tk2ImageV_wf : Program.WF tk2ImageV := by decide

/-- The worker's blocks are placed in its image. -/
theorem tk2WorkerV_sub : Program.subBlocksOfE tk2WorkerV tk2ImageV = true := by decide

/-! ## The symbols -/

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tk2ImageV)]

local instance tk2ImageV.env : CodeEnv := ⟨layout tk2ImageV⟩

/-- A symbol's address in the image: where `(sym)` points. -/
abbrev symTk2 (x : Label) : BitVec 64 := ((_root_.Executable.labels (layout tk2ImageV)).label x).toBitVec

/-- The entry (`worker`) or exit (`done`) label's address. -/
abbrev labTk2 (x : Label) : Int64 := (_root_.Executable.labels (layout tk2ImageV)).label x

theorem tk2WorkerV_placedIn : Program.PlacedIn tk2WorkerV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := tk2ImageV) tk2ImageV_wf rfl (by decide))
    tk2WorkerV_sub

omit [Executable.ValidLayout (layout tk2ImageV)] in
theorem tk2WorkerV_last : ∀ l blk, Program.blockAt tk2WorkerV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labTk2 "done" :=
  Program.after_last_of (by decide)

/-! ## The run -/

/-- The worker's environment: the protocol `tk2Env` on the three words. -/
abbrev ETk2 (x o c : BitVec 64) : SharedEnv := (tk2Env x o c).within (tkS x o c)

/-- The worker's table: phase `0` at `worker`, phase `1` with the ticket in
`%eax` at `spin`, phase `6` at `done`; the frame everywhere. -/
abbrev tk2TableV (x o c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (ETk2 x o c)).State → Prop :=
  fun lb s σ => FrameTk x o c s ∧
    ((lb = "worker" ∧ σ.1.k = 0) ∨
      (lb = "spin" ∧ σ.1.k = 1 ∧ σ.1.t = (s.regs.get64 .rax).setWidth 32) ∨
      (lb = "done" ∧ σ.1.k = 6))

set_option hygiene false in
/-- The spin's exit (`jne` not taken): the owner read is the ticket, so the
load moved the protocol to phase `2`. -/
local macro "spin_exit" : tactic => `(tactic| (
  rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
  · simp [hdo] at hm
  have heq : lo v = BitVec.setWidth 32 s₀.regs.rax.toBitVec := by
    unfold lo
    simp [CondCode.interp, StatusFlags.from_result, Reg64s.set64] at hz
    bv_omega
  have h1 : σ1.1.k = 2 := by
    have h : σ1.1 = g₀.1.onLoad v := hst.1
    simp [h, TkSt.onLoad, hT.1, hT.2, heq]))

set_option hygiene false in
/-- The counter's load: phase `3`, the low word read. -/
local macro "ctr_load" : tactic => `(tactic| (
  rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst2, rfl⟩
  · simp [hdc] at hm
  have h2 : σ2.1.k = 3 ∧ σ2.1.e = lo u := by
    have h : σ2.1 = σ1.1.onLoad u := hst2.1
    simp [h, TkSt.onLoad, h1]))

set_option hygiene false in
/-- The counter's store: phase `4`, `dmem` unchanged. -/
local macro "ctr_store" : tactic => `(tactic| (
  rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, b, hst3⟩
  · simp [hdc] at hm
  have h3 : σ3.1.k = 4 := by
    have h : σ3.1 = { σ2.1 with k := σ2.1.k + 1 } := hst3.1
    simp [h, h2.1]))

set_option hygiene false in
/-- The release's load: phase `5`, the low word read. -/
local macro "own_load" : tactic => `(tactic| (
  have h4 : σ4.1.k = 5 ∧ σ4.1.u = lo v4 := by
    have h : σ4.1 = σ3.1.onLoad v4 := hld4.1
    simp [h, TkSt.onLoad, h3]))

/-- **The verbatim `ticketlock2` worker in its protocol environment**
(counted, partial): from phase `0` at the entry label, every run that
reaches the exit label is in phase `6`. -/
theorem tk2WorkerV_envG (x o c : BitVec 64) (hx : symTk2 "next" = x) (ho : symTk2 "owner" = o)
    (hc : symTk2 "counter" = c) :
    ∀ s g, FrameTk x o c s ∧ g.1.k = 0 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (ETk2 x o c)))
        (fun y => (y.1.2 = labTk2 "done" ∧ y.2.1.k = 6) ∨ False) ((s, labTk2 "worker"), g) := by
  subst hx ho hc
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at
    (env := SharedEnv.counted (ETk2 (symTk2 "next") (symTk2 "owner") (symTk2 "counter")))
    (Q := fun _ σ => σ.1.k = 6) (E := fun _ _ _ => False)
    (tk2TableV (symTk2 "next") (symTk2 "owner") (symTk2 "counter")) ?_ rfl
    (by decide) tk2WorkerV_placedIn tk2WorkerV_last s g ⟨hsg.1, .inl ⟨rfl, hsg.2⟩⟩
  have : (SharedEnv.counted (ETk2 (symTk2 "next") (symTk2 "owner") (symTk2 "counter"))).Skips := inferInstance
  cfg_cases_env [tk2WorkerV]
  all_goals intro s₀ g₀
  all_goals vcgen [inc32_abs_shared_spec]
  all_goals obtain ⟨⟨⟨hdx, hdo, hdc⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [Reg64s.get64] at *
  · -- the frame before the ticket RMW
    exact hdx
  · -- the ticket RMW: in phase `0`, writing the low word plus one
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_rmw]
    refine ⟨⟨hT, rfl, rfl, fun old => ?_⟩, by simp⟩
    simp [rmwOp128, Reg64s.set64]
  · -- after the ticket RMW: `spin`, phase `1`, the ticket in `%eax`
    rename_i g₀ old σ1 hst _
    have h1 : σ1.1 = { g₀.1 with k := 1, t := lo old } := hst.1
    refine ⟨⟨hdx, hdo, hdc⟩, .inr (.inl ⟨trivial, ?_⟩)⟩
    rw [h1]
    simp [Reg64s.set64]
  · -- the spin's load: phase `1`, `owner`
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_load]
    exact ⟨⟨rfl, rfl, rfl, .inl ⟨.inl hT.1, rfl⟩⟩, by simp⟩
  · -- the spin's back edge: another value keeps phase `1`
    rename_i s₀ g₀ w σ1 hld hz _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hdo] at hm
    have hne : lo v ≠ BitVec.setWidth 32 s₀.regs.rax.toBitVec := by
      intro h; unfold lo at h
      simp [CondCode.interp, StatusFlags.from_result, Reg64s.set64] at hz
      bv_omega
    have h1 : σ1.1 = g₀.1 := by
      have h : σ1.1 = g₀.1.onLoad v := hst.1
      simp [h, TkSt.onLoad, hT.1, hT.2, hne]
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨hdx, hdo, hdc⟩, .inr (.inl ⟨rfl, ?_⟩)⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    · rw [h1]; simpa [Reg64s.set64] using hT
    · subst hg
      have := hst.2
      simp only [SharedEnv.tick_load] at *; omega
  · -- the counter's load: phase `2`, `counter`
    rename_i s₀ g₀ w σ1 hld hz _ _
    spin_exit
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_load]
    exact ⟨⟨rfl, rfl, rfl, .inr ⟨h1, rfl⟩⟩, by simp⟩
  · -- the counter's store: phase `3`, the low word read plus one
    rename_i s₀ g₀ w σ1 hld hz w2 σ2 hld2 _ _
    spin_exit
    ctr_load
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_store]
    refine ⟨⟨rfl, rfl, rfl, .inl ⟨h2.1, rfl, ?_⟩⟩, by simp⟩
    rw [h2.2]
    simp [Reg64s.set64, BitVec.add_comm]
  · -- the release's frame: `dmem` unchanged by the counter's store
    rename_i s₀ g₀ w σ1 hld hz w2 σ2 hld2 m σ3 hst3 _
    spin_exit
    ctr_load
    ctr_store
    exact hdo
  · -- the release's load: phase `4`, `owner`
    rename_i s₀ g₀ w σ1 hld hz w2 σ2 hld2 m σ3 hst3 _
    spin_exit
    ctr_load
    ctr_store
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_load]
    exact ⟨⟨rfl, rfl, rfl, .inl ⟨.inr h3, rfl⟩⟩, by simp⟩
  · -- the release's store: phase `5`, the low word read plus one
    rename_i s₀ g₀ w σ1 hld hz w2 σ2 hld2 m σ3 hst3 v4 σ4 hld4 _
    spin_exit
    ctr_load
    ctr_store
    own_load
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_store]
    exact ⟨⟨rfl, rfl, rfl, .inr ⟨h4.1, rfl, by rw [h4.2]⟩⟩, by simp⟩
  · -- `done`, phase `6`
    rename_i s₀ g₀ w σ1 hld hz w2 σ2 hld2 m σ3 hst3 v4 σ4 hld4 b5 σ5 hst5 st _
    spin_exit
    ctr_load
    ctr_store
    own_load
    have h5 : σ5.1.k = 6 := by
      have h : σ5.1 = { σ4.1 with k := σ4.1.k + 1 } := hst5.1
      simp [h, h4.1]
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨hdx, hdo, hdc⟩, .inr (.inr ⟨rfl, h5⟩)⟩, .inl (by decide)⟩
  · exact hT

end Kraken.Promising.X64.EnvG.TicketX2

#print axioms Kraken.Promising.X64.EnvG.TicketX2.inc32_abs_shared_spec
#print axioms Kraken.Promising.X64.EnvG.TicketX2.tk2WorkerV_envG
