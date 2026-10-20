/-
**`msqueue1.kl` (AArch64) never faults at the runner's declarations**
`msqueue1_envG_runner_faultFree` and its
concrete instance `msqueue1_envG_runner_faultFree_concrete`, program-level
`Config.FaultFree` from the runner's start states under any architecture
(promises included).

The enqueuer loads `[X3 + 8]` at a `tail` it read; the dequeuer loads
`[X3 + 8]` at a `head` it read and `[X5]` at a `next` it read. Both threads
get **value specifications** (`MemValsA64.ValSpecA`) over `inv S G` at the
layout `msqSA h t d n1 n2` (`head`, `tail`, the null node's link `8`, and
each node's data word and link), with

- `L` (`MsqValLA`): the 8-byte words `head`, `tail`, `8` and every node's
  link;
- `V` (`MsqValVA`): `0` or a node `d`, `n1`, `n2` (low 64 bits).

Every write of an 8-byte `L` word is a `casal` of the thread's own node or
of a value it read, so `MemVals L V` holds throughout and every dereference
is at a node or at `0`. As in the x64 proof (`MemValsMsQueue`), the null
node's link is in the layout: a value invariant cannot exclude `head = 0` or
`tail = 0`, so the proof covers loads at `0 + 8`; it is an undeclared 8-byte
footprint that overlaps no declaration of the runner (no fault). The initial
memory must hold `V` values at `L` (`decide` at the runner's
`msq1InitMemD`).

The runs (`enq_val_at`, `deq_val_at`) are the MS queue proof's purity scripts
(`MsQueueRelPure.lean`) in the counted `inv S G`, register tables only, run
in the whole image (`msq1Image`) from the entry labels to the exit labels,
as the purity specifications of `A64WholeMsQueue1` are. `msqueue1` has one
enqueued node; its theorem is the three-node invariant at `n2 = n1`.

Phase-1 limit: single-access trees (`msq1Image_dirs`).
-/
import Kraken.Promising.SLR.EnvG.MemValsA64
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue1Runner

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.MsQueue

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The value invariant -/

/-- A node: `d`, `n1` or `n2`. -/
def MsqNodeA (d n1 n2 x : BitVec 64) : Prop := x = d ∨ x = n1 ∨ x = n2

/-- The locations of the value invariant: `head`, `tail`, the null node's
link and every node's link. -/
def MsqValLA (h t d n1 n2 : BitVec 64) : Loc → Prop := fun l =>
  l = ⟨h, 8⟩ ∨ l = ⟨t, 8⟩ ∨ l = ⟨8, 8⟩ ∨ l = ⟨d + 8, 8⟩ ∨ l = ⟨n1 + 8, 8⟩ ∨ l = ⟨n2 + 8, 8⟩

/-- The values of the value invariant: `0` or a node. -/
def MsqValVA (d n1 n2 : BitVec 64) : Val → Prop := fun v => v.setWidth 64 = 0 ∨ MsqNodeA d n1 n2 (v.setWidth 64)

/-- The value condition. -/
abbrev msqGA (h t d n1 n2 : BitVec 64) : Loc → Val → Prop := fun l v =>
  MsqValLA h t d n1 n2 l → MsqValVA d n1 n2 v

/-- The threads' layout: `head`, `tail`, the null node's link, then each
node's data word and link. -/
abbrev msqSA (h t d n1 n2 : BitVec 64) : SharedEnv.Layout :=
  [(h, 8), (t, 8), (8, 8), (d, 4), (d + 8, 8), (n1, 4), (n1 + 8, 8), (n2, 4), (n2 + 8, 8)]

/-- The threads' environment. -/
abbrev msqEnvA (h t d n1 n2 : BitVec 64) : SharedEnv := SharedEnv.inv (msqSA h t d n1 n2) (msqGA h t d n1 n2)

/-- A 64-bit compare-and-swap writing a `V`-value writes a `V`-value
(`MemValsA64.rmwOpBits_cas_val`). -/
theorem msqValA_cas {d n1 n2 c y : BitVec 64} (hy : y = 0 ∨ MsqNodeA d n1 n2 y) :
    ∀ old v, rmwOpBits 64 (fun old => if old = c then some y else none) old = some v → MsqValVA d n1 n2 v :=
  rmwOpBits_cas_val (P := fun x => x = 0 ∨ MsqNodeA d n1 n2 x) hy

/-- A node's or the null node's link is an `L` word. -/
theorem msqValLA_link {h t d n1 n2 : BitVec 64} {v : Val} (hv : MsqValVA d n1 n2 v) :
    MsqValLA h t d n1 n2 ⟨v.setWidth 64 + 8, 8⟩ := by
  rcases hv with h0 | h0 | h0 | h0 <;> simp [MsqValLA, h0]

/-! ## The runs -/

section EnqAt

variable [CodeEnv]

/-- The enqueuer's value table: `x1 = t`, `x12` a node, `dmem` maps no 8- or
4-byte word; `x2` a node after `enq1`. -/
abbrev enqValTable (h t d n1 n2 : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (msqEnvA h t d n1 n2)).State → Prop :=
  fun lb s _ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    s.regs.X1.toBitVec = t ∧ MsqNodeA d n1 n2 s.regs.X12.toBitVec ∧
    (lb = "enq1" ∨ ((lb = "enq1_loop" ∨ lb = "enq1_end" ∨ lb = "pdone") ∧ MsqNodeA d n1 n2 s.regs.X2.toBitVec) ∨
      (lb = "enq1_fix" ∧ MsqNodeA d n1 n2 s.regs.X2.toBitVec ∧
        (s.regs.X4.toBitVec = 0 ∨ MsqNodeA d n1 n2 s.regs.X4.toBitVec)))

/-- **The enqueuer in the value environment**, in any ambient code in which
`enqProg` is `PlacedIn`, from `enq1` to the end address `endA` of its last
block. -/
theorem enq_val_at (h t d n1 n2 : BitVec 64) (hpl : Program.PlacedIn enqProg) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt enqProg l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (enqValTable h t d n1 n2) "enq1" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (msqEnvA h t d n1 n2)))
        (fun x => (x.1.2 = endA ∧ True) ∨ False) ((s, (_root_.Executable.labels cenv).label "enq1"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (msqEnvA h t d n1 n2)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (enqValTable h t d n1 n2) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [enqProg]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hd8, hd4, hx1, hx12, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals try (simp_all [SharedEnv.inv, Reg64s.setXReg, MsqValLA, MsqValVA, MsqNodeA]; done)
  -- forward jumps
  all_goals try (refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx1],
    by simpa using hx12, ?_⟩, .inl (by decide)⟩; simp (config := { decide := true }) [hT]; done)
  case vc7 =>
    rename_i s σ0 v3 σ1 v4 σ2 hnz hld1 hld2 _
    have hv3 : MsqValVA d n1 n2 v3 := by simpa [hx1, MsqValLA] using hld1.1
    have hv4 : MsqValVA d n1 n2 v4 := by
      have h2 := hld2.1
      simp [SharedEnv.inv, Reg64s.setXReg] at h2
      exact h2 (msqValLA_link hv3)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx1],
      by simpa using hx12, ?_⟩, .inl (by decide)⟩
    simpa [MsqValVA] using ⟨hT, hv4⟩
  case vc10 =>
    rename_i s σ0 v3 σ1 v4 σ2 hz hld1 hld2 _
    have hv3 : MsqValVA d n1 n2 v3 := by simpa [hx1, MsqValLA] using hld1.1
    simp only [MsqValVA, MsqNodeA] at hv3
    rcases hv3 with h0 | h0 | h0 | h0 <;> simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, h0] <;>
      exact fun old _ => msqValA_cas (.inr hT) old
  case vc11 =>
    rename_i s σ0 v3 σ1 v4 σ2 hz old σ3 hnz hld1 hld2 hcas _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx1], by simpa using hx12,
      ?_⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · simp (config := { decide := true }) [hT]
    · subst hg
      have h1 := hld1.2; have h2 := hld2.2; have h3 := hcas.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2 h3
      omega
  case vc14 =>
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx1]
    exact fun old _ => msqValA_cas (.inr hT) old
  case vc3 =>
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx1]
    exact fun old _ => msqValA_cas hT.2 old
  case vc4 =>
    rename_i s σ0 old σ1 hcas _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx1], by simpa using hx12,
      ?_⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · simp (config := { decide := true }) [hT.1]
    · subst hg
      have h3 := hcas.2
      simp only [SharedEnv.tick_rmw] at h3
      omega
  all_goals done

end EnqAt

section DeqAt

variable [CodeEnv]

/-- The dequeuer's value table: `x0 = h`, `x1 = t`, `dmem` maps no 8- or
4-byte word; `x5` a `V` value at `deq1a_ne`. -/
abbrev deqValTable (h t d n1 n2 : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (msqEnvA h t d n1 n2)).State → Prop :=
  fun lb s _ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    s.regs.X0.toBitVec = h ∧ s.regs.X1.toBitVec = t ∧
    (lb = "deq1a" ∨ (lb = "deq1a_ne" ∧ (s.regs.X5.toBitVec = 0 ∨ MsqNodeA d n1 n2 s.regs.X5.toBitVec)) ∨
      lb = "ddone1")

/-- **The dequeuer in the value environment**, in any ambient code in which
`deqProg` is `PlacedIn`, from `deq1a` to the end address `endA` of its last
block. -/
theorem deq_val_at (h t d n1 n2 : BitVec 64) (hpl : Program.PlacedIn deqProg) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt deqProg l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (deqValTable h t d n1 n2) "deq1a" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (msqEnvA h t d n1 n2)))
        (fun x => (x.1.2 = endA ∧ True) ∨ False) ((s, (_root_.Executable.labels cenv).label "deq1a"), g) := by
  refine cfgEnv_partial_rank_at (env := SharedEnv.counted (msqEnvA h t d n1 n2)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (deqValTable h t d n1 n2) deqRank ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env_rank [deqProg]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hd8, hd4, hx0, hx1, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals try (simp_all [SharedEnv.inv, Reg64s.setXReg, MsqValLA, MsqValVA, MsqNodeA]; done)
  -- jumps down the rank
  all_goals try (refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx0],
    by simp [hx1], ?_⟩, .inl (by decide)⟩; simp (config := { decide := true }); done)
  case vc10 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hld1 hld2 hld3 _
    have hv3 : MsqValVA d n1 n2 v3 := by simpa [hx0, MsqValLA] using hld1.1
    have hv5 : MsqValVA d n1 n2 v5 := by
      have h3 := hld3.1
      simp [SharedEnv.inv, Reg64s.setXReg] at h3
      exact h3 (msqValLA_link hv3)
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx0], by simp [hx1], ?_⟩,
      .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    · simpa [MsqValVA] using hv5
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2
    simp only [SharedEnv.tick_load] at h1 h2 h3
    omega
  case vc11 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hz hld1 hld2 hld3 _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx0], by simp [hx1], by simp⟩,
      .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2
    simp only [SharedEnv.tick_load] at h1 h2 h3
    omega
  case vc14 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hnz hld1 hld2 hld3 _
    have hv3 : MsqValVA d n1 n2 v3 := by simpa [hx0, MsqValLA] using hld1.1
    have hv5 : MsqValVA d n1 n2 v5 := by
      have h3 := hld3.1
      simp [SharedEnv.inv, Reg64s.setXReg] at h3
      exact h3 (msqValLA_link hv3)
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx1]
    exact fun old _ => msqValA_cas hv5 old
  case vc15 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hnz old σ4 hld1 hld2 hld3 hcas _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx0], by simp [hx1], by simp⟩,
      .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2; have h4 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2 h3 h4
    omega
  case vc6 =>
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx0]
    exact fun old _ => msqValA_cas hT old
  all_goals done

end DeqAt

/-! ## Specifications in the whole image

`ValSpecA.ofImageA` and `holdsD_ofImageA` (same names, this namespace) moved
to `EnvG/MemValsA64.lean`. -/

/-- The initial memory satisfies the value invariant when every `L` word
starts at a `V` value (no messages yet). -/
theorem memValsA_msq_init {h t d n1 n2 : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hi : ∀ l, MsqValLA h t d n1 n2 l → MsqValVA d n1 n2 ((Config.init states initMem).mem.initVal l)) :
    MemVals (MsqValLA h t d n1 n2) (MsqValVA d n1 n2) (Config.init states initMem).mem :=
  ⟨hi, fun ts w hw _ => by simp [Memory.get?, Config.init] at hw⟩

/-! ## `msqueue1.kl` -/

open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

section Msq1

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq1Image)]

/-- The image's static facts at a value condition `G` and layout `S`, ending
at `endPc`. -/
abbrev msq1SpecA (G : Loc → Val → Prop) (S : SharedEnv.Layout) (endPc : Int64) : ValSpecA G :=
  ValSpecA.ofImageA G S (layout msq1Image) endPc msq1Image_noPairs msq1Image_rmwLive msq1Image_noFault
    (phase1TreeF_of_dirs (dirsPhase1F_layout msq1Image_dirs))

/-- The enqueuer (thread `0`, to `pdone`) and the dequeuer (to `ddone1`). -/
def msq1ValSpecA (h t d n1 : BitVec 64) : Nat → ValSpecA (msqGA h t d n1 n1)
  | 0 => msq1SpecA _ (msqSA h t d n1 n1) (labQ1 "pdone")
  | _ + 1 => msq1SpecA _ (msqSA h t d n1 n1) (labQ1 "ddone1")

/-- The enqueuer's start state holds its specification. -/
theorem msq1_enq_holdsD {h t d n1 : BitVec 64} {ds : Decls} {s : isa.State}
    (hS : WithDeclsD ds (StartEQ1 t n1) s) : (msq1ValSpecA h t d n1 0).HoldsD ds s := by
  obtain ⟨hds, hS⟩ := hS
  refine holdsD_ofImageA (hph := phase1TreeF_of_dirs (dirsPhase1F_layout msq1Image_dirs)) hS.exe hds hS.endPc ?_
  rw [show s.st = (s.st.1, labQ1 "enq1") from Prod.ext rfl (hS.pc.trans labQ1_enq)]
  letI : CodeEnv := ⟨layout msq1Image⟩
  exact enq_val_at h t d n1 n1 (Program.PlacedIn.of_placedE msq1Image_placed (by decide))
    (Program.last_of_check (lx := "pdone") (by decide)) _ ((), 0)
    ⟨hS.d8, hS.d4, hS.x1, .inr (.inl hS.x12), .inl rfl⟩

/-- The dequeuer's start state holds its specification. -/
theorem msq1_deq_holdsD {h t d n1 : BitVec 64} {ds : Decls} {s : isa.State}
    (hS : WithDeclsD ds (StartDQ1 h t) s) : (msq1ValSpecA h t d n1 1).HoldsD ds s := by
  obtain ⟨hds, hS⟩ := hS
  refine holdsD_ofImageA (hph := phase1TreeF_of_dirs (dirsPhase1F_layout msq1Image_dirs)) hS.exe hds hS.endPc ?_
  rw [show s.st = (s.st.1, labQ1 "deq1a") from Prod.ext rfl (hS.pc.trans labQ1_deq1)]
  letI : CodeEnv := ⟨layout msq1Image⟩
  exact deq_val_at h t d n1 n1 (Program.PlacedIn.of_placedE msq1Image_placed (by decide))
    (Program.last_of_check (lx := "ddone1") (by decide)) _ ((), 0) ⟨hS.d8, hS.d4, hS.x0, hS.x1, .inl rfl⟩

end Msq1

/-- **No reachable configuration of the verbatim `msqueue1.kl` threads with
the runner's declarations has a faulting step** (one layout `l` for both),
for strict sized `ds` agreeing on `msqSA h t d n1 n1`, and an initial memory
with a `V` value (`0`, `d` or `n1`) at every `L` word. -/
theorem msqueue1_envG_runner_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l msq1Image)] {ds : Decls} (hsz : ds.StrictSized) (h t d n1 : BitVec 64)
    (hag : ds.AgreesOnA (msqSA h t d n1 n1)) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : WithDeclsD ds (StartEQ1 (layout := l) t n1) s0) (h1 : WithDeclsD ds (StartDQ1 (layout := l) h t) s1)
    (hi : ∀ lc, MsqValLA h t d n1 n1 lc → MsqValVA d n1 n1 ((Config.init [s0, s1] initMem).mem.initVal lc)) :
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  a64_faultFree_of_valSpecs (fun _ _ => Iff.rfl) (msq1ValSpecA (layout := l) h t d n1) (fun _ => ds)
    (fun _ => hsz) (fun | 0 => hag | _ + 1 => hag) (memValsA_msq_init hi)
    (init_threads_of2 (msq1_enq_holdsD h0) (msq1_deq_holdsD h1))

set_option maxRecDepth 8192 in
/-- **`msqueue1.kl` never faults**, from the runner's exact configuration
(`[enqDQ1, deqDQ1]` with the runner's declarations, initial memory
`msq1InitMemD`), under any architecture. -/
theorem msqueue1_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [enqDQ1, deqDQ1] msq1InitMemD) :=
  msqueue1_envG_runner_faultFree wLayoutQ1 msq1DeclsD_sized 0x1000 0x1200 0x1100 0x1300 (by decls_agrees_on_a)
    (withDeclsD_of rfl enqWQ1_start) (withDeclsD_of rfl deqWQ1_start)
    (fun lc hl => by
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Config.init, MsqValVA, MsqNodeA] <;> decide)

end Kraken.Promising.SLR.EnvG.MsQueue

#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue1_envG_runner_faultFree
#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue1_envG_runner_faultFree_concrete
