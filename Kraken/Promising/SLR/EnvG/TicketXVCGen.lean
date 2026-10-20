/-
**Part 1: the x64 ticket lock worker
verbatim, by `vcgen`**: the worker of
`Kraken/Examples/LockFree/X64/ticketlock3.kl` as written, with the absolute
operands `(next)`, `(owner)`, `(counter)` (`tk3WorkerV`), run in its image
`tk3ImageV`: the code followed by the `.kl` runner's data trailer
(`tk3DataV`: per symbol, in the order of first mention, a padding
`.byteArray` and the symbol's label; `Kraken.Litmus.X64.prepareProgram`).

- `lock_xadd32_abs_shared_specX`: the `vcgen` rule of `lock xaddl %r32,(sym)`
  (one `rmw .acqRel` of 4 bytes adding the low word of `r`; `r` gets the old
  word, zero-extended), as `MachineWP.xchg32_abs_shared_spec`.
- `tk3WorkerV_envG`: the worker's run in the counted
  `EnvGTDRX Arch.tso tid (tkPlan P) (disp P hL.xo) S` (`S` the three words),
  three-label table (`worker`: `Start`; `spin`: `Spin` at the ticket in
  `%eax`; `done`: `QEnd`), the VCs of `EnvG/TicketXVC.lean` restated at an
  address given by an equation (`*_at`).
- `tk3WorkerV_dispPure`: the worker's run in the counted all-release
  purity-and-phase environment `(dispPureX Arch.tso False ⟨x, 4⟩ (N + 1)).within S`
  (`worker` before the hand-out, `spin`/`done` after).
-/
import Kraken.Promising.SLR.EnvG.TicketXVC
import Kraken.Promising.SLR.EnvG.TicketXPure
import Kraken.Promising.SLR.EnvG.TicketRX64Link
import Kraken.Promising.SLR.EnvG.X64SpinAbsVCGen

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.TicketLock
open Kraken.X64.Parser

/-! ## The `cmpl %rb32, %ra32` rule -/

section Cmp32

open MachineWP

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} {p : Program}

/-- **`cmpl %rb32, %ra32`**: the flags of the 32-bit difference `ra - rb`; no
register changes (`MachineWP.cmp32_reg_imm_spec` with a register source, as
`MachineWP.cmp_reg_reg_spec` at 32 bits). `MachineWP.cmp32_reg_reg_spec`
(`Kraken/MachineWP.lean`, `@[spec]`). -/
theorem MachineWP.cmp32_reg_reg_specX (asz : Width) (ra rb : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 ra).setWidth 32
        let b := (s.regs.get64 rb).setWidth 32
        let v := a - b
        WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned - b.unsigned,
                  af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                  of := v.signed != a.signed - b.signed } } ⦄
      (Directive.instr (.regular asz .W32
          (.cmp (.reg (.low ra .W32)) (.regOrMem (.reg (.low rb .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  MachineWP.cmp32_reg_reg_spec asz ra rb

end Cmp32

/-! ## The `lock xaddl %r32,(sym)` rule -/

section AbsXadd

open Lean.Order

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

/-- **`lock xaddl %r32, (sym)` on a shared location**: one `rmw .acqRel` of
4 bytes adding the low word of `r`; `r` gets the old word, zero-extended, and
the flags of the addition (`MachineWP.lock_xadd_shared_spec` at 32 bits and
`(sym)`). `MachineWP.lock_xadd32_abs_shared_spec`
(`Kraken/EnvVCGenAbs.lean`, `@[spec]`). -/
theorem MachineWP.lock_xadd32_abs_shared_specX (l : Label) (r : Reg64) :
    ⦃ fun s g =>
        let a := absAddr l
        let src := (s.regs.get64 r).setWidth 32
        let op := rmwOp128 .W32 (fun x => some (x + src))
        (Mem.loadInt s.dmem a 4 = none) ⊓ env.ok (.rmw .acqRel a 4 op) g ⊓
          (∀ v g', env.step (.rmw .acqRel a 4 op) g v g' →
            let old := v.setWidth 32
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with
              regs := s.regs.set64 r (old.setWidth 64),
              status := LockBinOp.add.status old src (old + src) false } g') ⦄
      (⟨Directive.instr (.regular .W64 .W32
          (.xadd true (.mem ⟨none, none, .label l⟩) (.low r .W32))) :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  MachineWP.lock_xadd32_abs_shared_spec l r

end AbsXadd

namespace Kraken.Promising.X64.EnvG.TicketX

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program and its image -/

/-- **The x64 ticket lock worker of `ticketlock3.kl`, verbatim** (its `code`
block). -/
def tk3WorkerV : Program := parse("
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
  addl $1,%ecx
  movl %ecx,(owner)
  jmp done
done:
")

/-- The `.kl` runner's data trailer of `ticketlock3.kl`: each symbol a label
behind a padding cell, in the order of first mention (`next`, `owner`,
`counter`). -/
def tk3DataV : Program :=
  [.byteArray (.mk #[]), .label "next", .byteArray (.mk #[]), .label "owner", .byteArray (.mk #[]),
    .label "counter"]

/-- The worker's image: the code, then the data trailer. -/
def tk3ImageV : Program := tk3WorkerV ++ tk3DataV

/-- info: 14 -/
#guard_msgs in
#eval tk3WorkerV.length

theorem tk3ImageV_wf : Program.WF tk3ImageV := by decide

/-- The worker's blocks are placed in its image. -/
theorem tk3WorkerV_sub : Program.subBlocksOfE tk3WorkerV tk3ImageV = true := by decide

/-! ## The symbols -/

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tk3ImageV)]

local instance tk3ImageV.env : CodeEnv := ⟨layout tk3ImageV⟩

/-- A symbol's address in the image: where `(sym)` points. -/
abbrev symTk (x : Label) : BitVec 64 := ((_root_.Executable.labels (layout tk3ImageV)).label x).toBitVec

/-- The entry (`worker`) or exit (`done`) label's address. -/
abbrev labTk (x : Label) : Int64 := (_root_.Executable.labels (layout tk3ImageV)).label x

theorem tk3WorkerV_placedIn : Program.PlacedIn tk3WorkerV :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := tk3ImageV) tk3ImageV_wf rfl (by decide))
    tk3WorkerV_sub

omit [Executable.ValidLayout (layout tk3ImageV)] in
theorem tk3WorkerV_last : ∀ l blk, Program.blockAt tk3WorkerV l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labTk "done" :=
  Program.after_last_of (by decide)

/-! ## The layout -/

/-- The shared layout: the three 4-byte words. -/
abbrev tkS (x o c : BitVec 64) : SharedEnv.Layout := [(x, 4), (o, 4), (c, 4)]

/-- The worker's frame: no word in `dmem`. -/
abbrev FrameTk (x o c : BitVec 64) (s : MachineData) : Prop :=
  Mem.loadInt s.dmem x 4 = none ∧ Mem.loadInt s.dmem o 4 = none ∧ Mem.loadInt s.dmem c 4 = none

/-- The worker's environment: `EnvGTDRX` under `Arch.tso` on the three
words. -/
noncomputable abbrev ETk (N : Nat) (x o c : BitVec 64) (hL : Locs (tkSysX N x o c)) (tid : Nat) : SharedEnv :=
  EnvGTDRX Arch.tso tid (tkPlan (tkSysX N x o c)) (disp (tkSysX N x o c) hL.xo) (tkS x o c)

/-- The worker's table: `Start` at `worker`, `Spin` at the ticket in `%eax`
at `spin`, `QEnd` at `done`. -/
abbrev tk3TableV (N : Nat) (x o c : BitVec 64) (hL : Locs (tkSysX N x o c)) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (ETk N x o c hL tid)).State → Prop :=
  fun lb s σ => FrameTk x o c s ∧
    ((lb = "worker" ∧ Start (tkSysX N x o c) tid σ.1) ∨
      (lb = "spin" ∧ Spin (tkSysX N x o c) tid ((s.regs.get64 .rax).setWidth 32).toNat σ.1) ∨
      (lb = "done" ∧ QEnd (tkSysX N x o c) tid σ.1))

/-- **The verbatim x64 ticket lock worker on `EnvGTDRX`** (counted,
partial): from `Start` at the entry label, every run that reaches the exit
label is in `QEnd`. -/
theorem tk3WorkerV_envG (N : Nat) (x o c : BitVec 64) (hx : symTk "next" = x) (ho : symTk "owner" = o)
    (hc : symTk "counter" = c) (hL : Locs (tkSysX N x o c)) (tid : Nat) :
    ∀ s g, FrameTk x o c s ∧ Start (tkSysX N x o c) tid g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (ETk N x o c hL tid)))
        (fun y => (y.1.2 = labTk "done" ∧ QEnd (tkSysX N x o c) tid y.2.1) ∨ False) ((s, labTk "worker"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (ETk N x o c hL tid))
    (Q := fun _ σ => QEnd (tkSysX N x o c) tid σ.1)
    (E := fun _ _ _ => False) (tk3TableV N x o c hL tid) ?_ rfl
    (by decide) tk3WorkerV_placedIn tk3WorkerV_last s g (by simpa [tk3TableV] using hsg)
  cfg_cases_env [tk3WorkerV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hdx, hdo, hdc⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMonoX_le_within, TicketLock.fenceMono_le_envGTDR,
    Reg64s.get64] at *
  · -- the frame before the ticket RMW
    exact hdx
  · -- the ticket RMW is permitted
    rename_i hf _
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_rmw]
    exact ⟨(vcX_xadd hL _ (hT.fence hf.1) (fun v => by simp [rmwOp128, Reg64s.set64])).1, by simp⟩
  · -- after the ticket RMW: `spin` at the ticket
    rename_i σ0 old σ1 hst hf _
    have hS := (vcX_xadd hL _ (hT.fence hf.1) (fun v => by simp [rmwOp128, Reg64s.set64])).2 old σ1.1 hst.1
    have hlt : old.toNat < 2 ^ 32 := by have := hS.2.1; have := hL.n32; omega
    refine ⟨⟨hdx, hdo, hdc⟩, .inr (.inl ⟨trivial, ?_⟩)⟩
    simp only [Reg64s.set64, BitVec.toNat_setWidth]
    simp only [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (show old.toNat < 2 ^ 64 by omega)]; exact hS
  · -- the spin's load is permitted
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_load]
    exact ⟨fun h => hL.xo h.symm, by simp⟩
  · -- the spin's back edge: another value keeps `Spin`
    rename_i s₀ g₀ x σ1 hld σ2 hz σ3 hf1 hf2 _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hdo] at hm
    have hne : lo v ≠ (BitVec.setWidth 32 s₀.regs.rax.toBitVec).toNat := by
      intro h; unfold lo at h
      simp [CondCode.interp, StatusFlags.from_result, Reg64s.set64] at hz
      bv_omega
    have h := ((vcX_spin hL _ hT v σ1.1 hst.1).1 hne).fence hf1.1 |>.fence hf2.1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨hdx, hdo, hdc⟩, .inr (.inl ⟨rfl, by simpa [Reg64s.set64] using h⟩)⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have := hst.2; have := hf1.2; have := hf2.2
    simp only [SharedEnv.tick_load] at *; omega
  · -- the counter's load is permitted
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_load]
    exact ⟨fun h => hL.xc h.symm, by simp⟩
  · -- the counter's store is permitted
    rename_i s₀ g₀ x σ1 hld σ2 hz σ3 w σ4 hld2 σ5 hdm hf1 hf2 hf3 _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hdo] at hm
    have heq : lo v = (BitVec.setWidth 32 s₀.regs.rax.toBitVec).toNat := by
      unfold lo
      simp [CondCode.interp, StatusFlags.from_result, Reg64s.set64] at hz
      bv_omega
    have hG := ((vcX_spin hL _ hT v σ1.1 hst.1).2 heq).fence hf1.1 |>.fence hf2.1
    have ht : (BitVec.setWidth 32 s₀.regs.rax.toBitVec).toNat + 1 < 2 ^ 32 := by
      have := hG.2.1; have := hL.n32; simp only at *; omega
    have h1 : (Int64.toBitVec 1).toNat = 1 := rfl
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst2, rfl⟩
    · simp [hdc] at hm
    have hR := (vcX_ldc hL _ hG u σ4.1 hst2.1).fence hf3.1
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_store]
    exact ⟨(vcX_stc hL _ hR (by intro hu; simp only [Reg64s.set64]; bv_omega)).1, by simp⟩
  · -- the release is permitted
    rename_i s₀ g₀ x σ1 hld σ2 hz σ3 w σ4 hld2 σ5 dm σ6 hst3 σ7 hdm hf1 hf2 hf3 hf4 _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hdo] at hm
    have heq : lo v = (BitVec.setWidth 32 s₀.regs.rax.toBitVec).toNat := by
      unfold lo
      simp [CondCode.interp, StatusFlags.from_result, Reg64s.set64] at hz
      bv_omega
    have hG := ((vcX_spin hL _ hT v σ1.1 hst.1).2 heq).fence hf1.1 |>.fence hf2.1
    have ht : (BitVec.setWidth 32 s₀.regs.rax.toBitVec).toNat + 1 < 2 ^ 32 := by
      have := hG.2.1; have := hL.n32; simp only at *; omega
    have h1 : (Int64.toBitVec 1).toNat = 1 := rfl
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst2, rfl⟩
    · simp [hdc] at hm
    have hR := (vcX_ldc hL _ hG u σ4.1 hst2.1).fence hf3.1
    rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, b, hst3⟩
    · simp [hdc] at hm
    have hS := (vcX_stc hL _ hR (by intro hu; simp only [Reg64s.set64]; bv_omega)).2 b σ6.1 hst3.1
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_store]
    exact ⟨(vcX_rel hL _ (hS.fence hf4.1) (by unfold lo at heq ⊢; simp only [Reg64s.set64]; bv_omega)).1, by simp⟩
  · -- after the release: `done`
    rename_i s₀ g₀ x σ1 hld σ2 hz σ3 w σ4 hld2 σ5 dm σ6 hst3 σ7 dm2 σ8 hst4 σ9 hf1 hf2 hf3 hf4 hf5 _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hdo] at hm
    have heq : lo v = (BitVec.setWidth 32 s₀.regs.rax.toBitVec).toNat := by
      unfold lo
      simp [CondCode.interp, StatusFlags.from_result, Reg64s.set64] at hz
      bv_omega
    have hG := ((vcX_spin hL _ hT v σ1.1 hst.1).2 heq).fence hf1.1 |>.fence hf2.1
    have ht : (BitVec.setWidth 32 s₀.regs.rax.toBitVec).toNat + 1 < 2 ^ 32 := by
      have := hG.2.1; have := hL.n32; simp only at *; omega
    have h1 : (Int64.toBitVec 1).toNat = 1 := rfl
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst2, rfl⟩
    · simp [hdc] at hm
    have hR := (vcX_ldc hL _ hG u σ4.1 hst2.1).fence hf3.1
    rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, b, hst3⟩
    · simp [hdc] at hm
    have hS := (vcX_stc hL _ hR (by intro hu; simp only [Reg64s.set64]; bv_omega)).2 b σ6.1 hst3.1
    rcases hst4 with ⟨hm, -, -⟩ | ⟨-, rfl, b', hst4⟩
    · simp [hdo] at hm
    have hQ := ((vcX_rel hL _ (hS.fence hf4.1) (by unfold lo at heq ⊢; simp only [Reg64s.set64]; bv_omega)).2 b' σ8.1
      hst4.1).fence hf5.1
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨hdx, hdo, hdc⟩, .inr (.inr ⟨rfl, hQ⟩)⟩, .inl (by decide)⟩
  · exact hT

/-! ## Purity and the dispenser phases -/

/-- The worker's purity-and-phase environment: all-release `dispPureX` on
the three words, bound `N + 1`. -/
abbrev EPureTk (N : Nat) (x o c : BitVec 64) : SharedEnv :=
  (dispPureX Arch.tso (fun _ _ => False) ⟨x, 4⟩ (N + 1)).within (tkS x o c)

/-- The phase table: the frame everywhere, before the hand-out at `worker`,
after it at `spin` and `done`. -/
abbrev tk3PureTableV (N : Nat) (x o c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (EPureTk N x o c)).State → Prop :=
  fun lb s σ => FrameTk x o c s ∧ ((lb = "worker" ∧ σ.1 = false) ∨ ((lb = "spin" ∨ lb = "done") ∧ σ.1 = true))

/-- **The verbatim x64 ticket lock worker in the all-release
purity-and-phase environment** (counted, partial): the `lock xaddl` writes
`old + 1` to `next` and moves to the second phase; every store is a release
(`Arch.tso`) away from `next`. -/
theorem tk3WorkerV_dispPure (N : Nat) (x o c : BitVec 64) (hx : symTk "next" = x) (ho : symTk "owner" = o)
    (hc : symTk "counter" = c) (hN : N + 1 < 2 ^ 32) (hxo : x ≠ o) (hxc : x ≠ c) :
    ∀ s g, FrameTk x o c s ∧ g.1 = false →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EPureTk N x o c)))
        (fun y => (y.1.2 = labTk "done" ∧ y.2.1 = true) ∨ False) ((s, labTk "worker"), g) := by
  subst hx ho hc
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at
    (env := SharedEnv.counted (EPureTk N (symTk "next") (symTk "owner") (symTk "counter")))
    (Q := fun _ σ => σ.1 = true) (E := fun _ _ _ => False)
    (tk3PureTableV N (symTk "next") (symTk "owner") (symTk "counter")) ?_ rfl
    (by decide) tk3WorkerV_placedIn tk3WorkerV_last s g ⟨hsg.1, .inl ⟨rfl, hsg.2⟩⟩
  have : (SharedEnv.counted (EPureTk N (symTk "next") (symTk "owner") (symTk "counter"))).Skips := inferInstance
  cfg_cases_env [tk3WorkerV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hdx, hdo, hdc⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  · exact hdx
  · -- the ticket RMW: a release on `next`, before the hand-out, writing `old + 1`
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_rmw]
    refine ⟨⟨fun h => (h rfl).elim, fun _ => ⟨hT, fun old new hop hlt => ?_⟩⟩, by simp⟩
    have h1 : (Int64.toBitVec 1).toNat = 1 := rfl
    simp only [rmwOp128, Option.map_some, Option.some.injEq] at hop
    subst hop
    have hw : Width.W32.bits = 32 := rfl
    simp only [Reg64s.get64, Reg64s.set64, BitVec.toNat_setWidth, BitVec.toNat_add, h1, hw]
    omega
  · -- after the hand-out: `spin`, in the second phase
    rename_i old σ1 hst _
    have h : σ1.1 = true := by
      have h := hst.1
      simp [rmwOp128] at h
      exact h.trans (Bool.or_true _)
    exact ⟨⟨hdx, hdo, hdc⟩, .inr ⟨.inl rfl, h⟩⟩
  · simp only [SharedEnv.counted_ok, SharedEnv.within_ok_load]
    exact ⟨trivial, by simp⟩
  · -- the spin's back edge
    rename_i s₀ g₀ x σ1 hld hz _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hdo] at hm
    have h : σ1.1 = g₀.1 := hst.1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨hdx, hdo, hdc⟩, .inr ⟨.inl rfl, h.trans hT⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have := hst.2
    simp only [SharedEnv.tick_load] at *; omega
  · simp only [SharedEnv.counted_ok, SharedEnv.within_ok_load]
    exact ⟨trivial, by simp⟩
  · -- the counter's store: a release away from `next`
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_store]
    exact ⟨⟨fun h => (h rfl).elim, fun h => hxc (congrArg Loc.addr h).symm⟩, by simp⟩
  · -- the release: away from `next`
    simp only [SharedEnv.counted_ok, SharedEnv.within_ok_store]
    exact ⟨⟨fun h => (h rfl).elim, fun h => hxo (congrArg Loc.addr h).symm⟩, by simp⟩
  · -- `done`, in the second phase
    rename_i s₀ g₀ x σ1 hld hz w σ2 hld2 dm σ3 hst3 dm2 σ4 hst4 _
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hdo] at hm
    rcases hld2 with ⟨u, hm, -, -⟩ | ⟨-, u, hst2, rfl⟩
    · simp [hdc] at hm
    rcases hst3 with ⟨hm, -, -⟩ | ⟨-, rfl, b, hst3⟩
    · simp [hdc] at hm
    rcases hst4 with ⟨hm, -, -⟩ | ⟨-, rfl, b', hst4⟩
    · simp [hdo] at hm
    have h1 : σ1.1 = g₀.1 := hst.1
    have h2 : σ2.1 = σ1.1 := hst2.1
    have h3 : σ3.1 = σ2.1 := hst3.1
    have h4 : σ4.1 = σ3.1 := hst4.1
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨hdx, hdo, hdc⟩, .inr ⟨.inr rfl, by rw [h4, h3, h2, h1]; exact hT⟩⟩,
      .inl (by decide)⟩
  · exact hT

end Kraken.Promising.X64.EnvG.TicketX
