/-
**The x64 Michael–Scott queue with a
bump-allocating enqueuer, whole program, through the x64 kit**
(`KitX.lower_promising_x64`). ISA: x64 (`isa`);
`Arch.tso`; machine: the executable Promising machine (`Reachable`).

Thread `0` runs `msqAX` (`main_e`: two `alloc`, two data-word stores, two
`enq`) on its layout `l0`; thread `1` runs the x64 MS queue pilot's dequeuer, `MsqXR.deqT` on
`msqXR` at its own layout `l1`, **unchanged** (`mainD_specXR`,
`msqXR_pureD`). The protocol is the x64 MS queue pilot's (`MQX`, `planE`/`planD`, `erase_init`,
the final reading of `msqXR_promising`, unchanged) at `pAX h t s base`: the
nodes are `n1 = base` and `n2 = base + 16`, the two allocations from the
enqueuer's arena (`r14 = base` at start, limit `r15`).

**What is proved, and what is not.** The conclusion is the x64 MS queue pilot's predicate
`MsQueue2FinalX base (base + 16)`: the dequeuer returns the **node
identities** in FIFO order (`r12 = base`, `r13 = base + 16`). The x64 MS queue pilot's x64
protocol has no data word, so nothing is concluded about the payload
`[n + 8]` (the stores `[n1 + 8] := 1`, `[n2 + 8] := 2` are proved
*admitted*, pure messages off the queue words, not *read back*).

**Node layout versus WeakCore.** WeakCore's `node` is `τ × Ptr?` (payload at
offset `0`, link at offset `8`; the allocating MS queue pilot's AArch64 layout). Here, as in the x64 MS queue pilot's
protocol, the link is at offset `0` and the payload at offset `8`; the node
is 16 bytes either way.

Start hypotheses only: the threads' start states (`StartA`: `rbx = &tail`,
`r14 = base` with room for two nodes below `r15`, the link at `done`, `dmem`
empty; `MsqXR.StartD`), the queue's initial words with the **pre-zeroed
arena's links** (`InitV`: `head = tail = s`, `[s] = [base] = [base + 16] = 0`;
the data words are arbitrary; the emitter rule of `Lower/MsqAllocXProg.lean`)
and the layout facts `ArenaLocs` (`head`, `tail`, `s` and the arena's words
distinct, both nodes non-null).
-/
import Kraken.Promising.Lower.MsqAllocXMain
import Kraken.Promising.Lower.MsqXRConcrete

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.MsqAllocX

open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16 split_sAll)
open Kraken.Promising.Lower.KitX (LowerThreadX lower_promising_x64)
open Kraken.Promising.Lower.PilotXR (D8)
open Kraken.Promising.Lower.MsqXR (deqT StartD msqXR)

/-! ## The protocol's parameters at the arena -/

/-- **The parameters**: `head` at `h`, `tail` at `t`, the sentinel `s`, the
two allocated nodes `n1 = base`, `n2 = base + 16`; untracked swings. -/
abbrev pAX (h t s base : BitVec 64) : Params := ⟨h, t, s, base, base + 16, false⟩

/-- **The layout facts**: `head`, `tail`, the sentinel and the arena's four
words (`[base]`, `[base + 8]`, `[base + 16]`, `[base + 24]`) distinct, the
nodes non-null. -/
structure ArenaLocs (h t s base : BitVec 64) : Prop where
  ht : h ≠ t
  hs : h ≠ s
  ts : t ≠ s
  h0 : h ≠ base
  h8 : h ≠ base + 8
  h16 : h ≠ base + 16
  h24 : h ≠ base + 16 + 8
  t0 : t ≠ base
  t8 : t ≠ base + 8
  t16 : t ≠ base + 16
  t24 : t ≠ base + 16 + 8
  s0 : s ≠ base
  s8 : s ≠ base + 8
  s16 : s ≠ base + 16
  s24 : s ≠ base + 16 + 8
  nz1 : base ≠ 0
  nz2 : base + 16 ≠ 0

namespace ArenaLocs

variable {h t s base : BitVec 64} (hA : ArenaLocs h t s base)
include hA

/-- The x64 MS queue pilot's `QLocs` at `pAX`. -/
theorem qLocs : QLocs (pAX h t s base) :=
  ⟨hA.ht, hA.hs, hA.h0, hA.h16, hA.ts, hA.t0, hA.t16, hA.s0, hA.s16, by bv_omega, hA.nz1, hA.nz2⟩

/-- A data word `[n + 8]` (`n` a node) is not a queue word. -/
theorem data_not_isW {n : BitVec 64} (hn : n = base ∨ n = base + 16) : ¬ (pAX h t s base).IsW ⟨n + 8, 8⟩ := by
  rintro (e | e | e | e | e) <;>
    simp only [Params.head, Params.tail, Params.ls, Params.l1, Params.l2, Loc.mk.injEq, and_true] at e <;>
    rcases hn with rfl | rfl
  all_goals first
    | exact hA.h8 e.symm | exact hA.h24 e.symm | exact hA.t8 e.symm | exact hA.t24 e.symm
    | exact hA.s8 e.symm | exact hA.s24 e.symm | (revert e; bv_omega)

end ArenaLocs

/-! ## The enqueuer as a lowered x64 thread -/

section Thread

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msqAX)]

set_option maxRecDepth 20000 in
/-- The label `done` is the end of the text. -/
theorem labA_done : labA "done" = (layout msqAX).addrOf msqAX.length := by
  have hm : msqAX[49]? = some (Directive.label "done") := by decide
  have hd : labA "done" = (layout msqAX).addrOf 49 :=
    Program.label_addrOf_drop msqAX_wf.nodup (by decide) (by decide)
  have h49 : (layout msqAX).2[49]? = some (Directive.label "done", Kraken.Layout.size Directive 49) := by
    simp [Layout.apply_snd, Layout.frag, hm]
  rw [show msqAX.length = 49 + 1 by decide, Executable.addrOf_succ _ h49,
    Executable.ValidLayout.label_size 49 "done" _ h49, hd]
  simp

/-- **No instruction steps at `done`.** -/
theorem msqAX_stuck (env : SharedEnv) : ∀ x R, x.1.2 = labA "done" → ¬ (layout msqAX).instrStepEnv env x R := by
  rw [labA_done]
  exact not_instrStepEnv_of_end_labels env 1

omit [Executable.ValidLayout (layout msqAX)] in
/-- **`hB` of the enqueuer**: its token, whole (the x64 MS queue pilot's `hB_E`, at `labA`). -/
theorem hB_EA (P : Params) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    (∃ n, (fun x : MachineState × (EStateX × Nat) => x.1.2 = labA "done" ∧ ComE P x.2.1) (t.st.st, (σ, n))) →
      t.prom = [] → EnvRel 0 (planE P) σ c t r g cl → cl → MQX P c r g := by
  rintro c t r g cl σ ⟨_, -, hcom⟩ hp hrel -
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr hcom.2.2
  · rw [hp] at hts; cases hts

/-- **The allocating enqueuer as a lowered x64 thread** (thread `0`). -/
noncomputable def enqTA (P : Params) (hL : QLocs P) (hn2 : P.n2 = P.n1 + 16) (hd1 : ¬ P.IsW ⟨P.n1 + 8, 8⟩)
    (hd2 : ¬ P.IsW ⟨P.n2 + 8, 8⟩) : LowerThreadX 0 sAll (MQX P) where
  e := layout msqAX
  valid := inferInstance
  pl := planE P
  hpl := planE_valid P
  shape := msqAX_phase1FX
  entry := labA "main_e"
  endPc := labA "done"
  stuck := msqAX_stuck
  Q x := x.1.2 = labA "done" ∧ ComE P x.2.1
  Q_end _ h := h.1
  hB := hB_EA P
  PreR := MainAPreR (labA "done")
  QR x := x.1.2 = labA "done"
  QR_end _ h := h
  pure := mainA_pureX _
  Pre := MainAPreX P (labA "done")
  main := mainA_specX P hL hn2 hd1 hd2 _

/-- **The enqueuer's start state**: the image, pc at `main_e`, end and link
at `done`, `rbx = &tail`, the bump pointer `r14 = n1` with room for **two**
nodes below `r15`, `dmem` empty. -/
structure StartA (P : Params) (s : isa.State) : Prop where
  exe : s.exe = layout msqAX
  decls : s.decls = {}
  pc : s.st.2 = labA "main_e"
  endPc : s.endPc = labA "done"
  r11 : s.st.1.regs.get64 .r11 = (labA "done").toBitVec
  rbx : s.st.1.regs.get64 .rbx = P.t
  r14 : s.st.1.regs.get64 .r14 = P.n1
  room1 : s.st.1.regs.get64 .r14 + 16 ≤ s.st.1.regs.get64 .r15
  room2 : P.n1 + 16 + 16 ≤ s.st.1.regs.get64 .r15
  dmem : ∀ k, s.st.1.dmem.get? k = none

end Thread

/-- **The threads**: the allocating enqueuer (`msqAX` at `l0`) and the x64 MS queue pilot's
dequeuer (`msqXR` at `l1`). -/
noncomputable def msqAT (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 msqAX)]
    [Executable.ValidLayout (l1 msqXR)] (h t s base : BitVec 64) (hA : ArenaLocs h t s base) :
    (tid : Nat) → tid < 2 → LowerThreadX tid sAll (MQX (pAX h t s base))
  | 0, _ => enqTA (layout := l0) _ hA.qLocs rfl (hA.data_not_isW (.inl rfl)) (hA.data_not_isW (.inr rfl))
  | 1, _ => deqT (layout := l1) _ hA.qLocs rfl
  | _ + 2, hh => absurd hh (by omega)

/-- **The x64 Michael–Scott queue with a bump-allocating enqueuer, on the
Promising model** (x64, `Arch.tso`, `isa`, executable machine): for all
layouts `l0` of `msqAX` and `l1` of `msqXR`, all addresses `h` of `head`, `t`
of `tail`, `s` of the sentinel and `base` of the enqueuer's arena (nodes at
`base` and `base + 16`: link `[n]`, payload `[n + 8]`, 8 bytes each) with the
layout facts `ArenaLocs`: if thread `0` starts `msqAX` with `rbx = &tail`,
`r14 = base` and room for two nodes below `r15` (`StartA`), thread `1` starts
the x64 MS queue pilot's `main_d` (`MsqXR.StartD`), and the initial memory has
`head = tail = s` and the links `[s]`, `[base]`, `[base + 16]` zero (`InitV`;
the arena is pre-zeroed, the payload words arbitrary), then every final
configuration reachable under `Arch.tso` has the dequeuer's `r12 = base`,
`r13 = base + 16` (`MsQueue2FinalX`: node-identity FIFO; nothing about the
payload). -/
theorem msqAllocX_promising {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 msqAX)]
    [Executable.ValidLayout (l1 msqXR)] {h t s base : BitVec 64} (hA : ArenaLocs h t s base)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartA (layout := l0) (pAX h t s base) s0)
    (h1 : StartD (layout := l1) (pAX h t s base) s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem (pAX h t s base))
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : MsQueue2FinalX base (base + 16) cfg := by
  have hL := hA.qLocs
  refine lower_promising_x64 (Φ := MsQueue2FinalX base (base + 16)) fuel sAll_le16 (erase_init hL _) rfl
    (msqAT l0 l1 h t s base hA) ?_ hc hf ?_
  · intro tid htid
    rcases tid with _ | _ | i
    · obtain ⟨he, hds, hpc, hend, h11, hbx, h14, hr1, hr2, hdm⟩ := h0
      exact ⟨⟨he, hds, hend, hpc, split_sAll hdm, 0, h11, hr1, (show s0.st.1.regs.get64 .r14 + 16 + 16 ≤ _ by rw [h14]; exact hr2), d8_of_dmem hdm⟩,
        0, h11, hbx, h14, hr1, hr2, d8_of_dmem hdm, e0_init _ _⟩
    · obtain ⟨he, hds, hpc, hend, h11, hbx, h14, hdm⟩ := h1
      exact ⟨⟨he, hds, hend, hpc, split_sAll hdm, 0, d8_of_dmem hdm, h11⟩, 0, h11, hbx, h14, d8_of_dmem hdm,
        comD_init _ _ hi⟩
    · simp only [List.length_cons, List.length_nil] at htid; omega
  intro rF' g' E' hle hsize hB
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw (pAX h t s base)).mono hle
  have fin : ∀ i, i < cfg.threads.size → MQX (pAX h t s base) cfg (rF' i) g' →
      1 ≤ ((rF' i).wr (pAX h t s base).tokH).q ∨ MsQueue2FinalX base (base + 16) cfg := by
    rintro i hi (⟨th, hth, hd, hiv, hacq⟩ | hq)
    · exact .inr ⟨th, hth, final_values E' hW hL hiv
        (fun x hx => TreiberCommon.total_acq_of_ge E' hi (hacq x hx)) hd⟩
    · exact .inl hq
  rcases fin 0 hi0 (hB 0 (Config.final_done hf hi0)) with hq0 | hfin
  · rcases fin 1 hi1 (hB 1 (Config.final_done hf hi1)) with hq1 | hfin
    · exact (tokH_pair_false E' hi0 hi1 (by decide) hq0 hq1).elim
    · exact hfin
  · exact hfin

/-! ## The concrete instance (`MsqAllocXProg`'s explorer configuration) -/

/-- The explorer's layout facts: `head` `0x1000`, `tail` `0x1008`, `s`
`0x2000`, the arena at `0x2100`. -/
theorem arenaLocsC : ArenaLocs 0x1000 0x1008 0x2000 0x2100 := by
  constructor <;> decide

section
attribute [local instance] maLayout

set_option maxRecDepth 20000

theorem threadA_start : StartA (pAX 0x1000 0x1008 0x2000 0x2100) threadA := by
  have hd : labA "done" = endMA := by rw [labA_done]; decide
  refine ⟨rfl, rfl, ?_, hd.symm, by rw [hd]; rfl, rfl, rfl, by decide, by decide, fun k => by simp [threadA]⟩
  rw [show labA "main_e" = (maLayout msqAX).addrOf 0 from
    Program.label_addrOf_drop msqAX_wf.nodup (by decide) (by decide)]
  decide

end

section
attribute [local instance] MsqXR.mxLayout

/-- The x64 MS queue pilot's concrete dequeuer start (`StartD` reads only `head` and `tail`). -/
theorem threadD_startA : StartD (pAX 0x1000 0x1008 0x2000 0x2100) MsqXR.threadD :=
  let ⟨a, b, c, d, e, f, g, h⟩ := MsqXR.Concrete.threadD_start; ⟨a, b, c, d, e, f, g, h⟩

end

theorem initMemA_initV :
    InitV (Config.init (I := isa) [threadA, MsqXR.threadD] initMemA).mem (pAX 0x1000 0x1008 0x2000 0x2100) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Params.head, Params.tail, Params.ls, Params.l1, Params.l2, Config.init_mem] <;> decide

/-- **Non-vacuity**: `msqAllocX_promising` at the explorer's configuration
(`msqAllocXRun0`): `head` `0x1000`, `tail` `0x1008` (both initially the
sentinel `0x2000`), the arena at `0x2100` (nodes `0x2100`, `0x2110`; links
`0`, payload words garbage `7`). No hypothesis beyond reachability and
finality. -/
theorem msqAllocX_concrete {fuel : Nat} {cfg : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [threadA, MsqXR.threadD] initMemA) cfg) (hf : cfg.final = true) :
    MsQueue2FinalX 0x2100 0x2110 cfg :=
  msqAllocX_promising maLayout MsqXR.mxLayout arenaLocsC threadA_start threadD_startA initMemA_initV hc hf

end Kraken.Promising.Lower.MsqAllocX

#print axioms Kraken.Promising.Lower.MsqAllocX.msqAllocX_promising
#print axioms Kraken.Promising.Lower.MsqAllocX.msqAllocX_concrete
