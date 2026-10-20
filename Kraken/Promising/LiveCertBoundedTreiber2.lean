/-
**Fuel-free termination of the `treiber2`
family on the semantic machine** (`TermBoundSemU`, `LiveCertBounded.lean`).
Additive: every name is new and sits beside the existing fixed-fuel
`…_term_sem` theorem it upgrades (`LiveTermTreiber2Thm.lean`,
`LiveTermTreiber2Nodes.lean`), whose statements are unchanged.

Each `…_certBounded…` theorem proves `CertBoundedFrom Arch.armv8 c0 F` for
the start configurations of the existing theorem, with the explicit bound

  **`F = certF n = 42 + 20 * (2 * n + 2)` (`= 82 + 40 * n`) for `n` threads**

(`n = 2` for the two-thread and concrete forms: `F = 162`), independent of
fuel (`LiveCertBoundedTreiber2P.lean`). Each `…_term_semU…` theorem then
says: **every `TraceSemU` from `c0` (each step may use its own certification
length) is final at one index `K`, under every schedule**. It is the existing
`…_term_sem` at fuel `F`, transferred by `CertBounded.termTransfer`; no
hypothesis is left open.

| worker | fuel-free statements |
|---|---|
| `treiber2DWorker` | `treiber2_term_semU_gen`, `treiber2_term_semU` (+ `_concrete`) |
| `treiber2ArmWorker` | `treiber2_arm_term_semU_all`, `treiber2_arm_term_semU` (+ `_concrete`) |
| `Reach.Treiber2Relaxed.code` | `treiber2_relaxed_term_semU_all`, `treiber2_relaxed_term_semU` |
| `treiber2NImage` | `treiber2_nodes_term_semU_all`, `treiber2_nodes_term_semU` (+ `_concrete`) |
-/
import Kraken.Promising.LiveCertBoundedTreiber2P
import Kraken.Promising.LiveTermTreiber2Thm
import Kraken.Promising.LiveTermTreiber2Nodes

namespace Kraken.Promising.Live.TermTreiber2

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live.CertBounded
open Kraken.Promising.Live.CertBoundedTreiber2P (certF certBounded_genP' InvU init_size)
open Kraken.Promising.SLR.EnvG.Treiber2 (treiber2DWorker StartWD wLayout2D wWorker0 wWorker1 wWorker0_start
  wWorker1_start)
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr)
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2Data (treiber2InitMem)

/-- **Bounded certification for the `treiber2.kl` workers**: from the start
configurations of `treiber2_term_sem_gen` with `n = |states|` threads, every
certification of a reachable thread (at any fuel) fits in
`certF n = 42 + 20 * (2 * n + 2)` instructions. -/
theorem treiber2_certBounded_gen (l : _root_.Layout) [Executable.ValidLayout (l treiber2DWorker)]
    (t : BitVec 64) {states : List isa.State} {initMem : List (Loc × Val)} (hs : ∀ s ∈ states, Start (layout := l) t s) :
    CertBoundedFrom Arch.armv8 (Config.init states initMem : Config isa) (certF states.length) := by
  have := certBounded_genP' (cells (layout := l)) (InvU.ofInv0 (inv_init (layout := l) (fuel := 0) (initMem := initMem) hs).toP)
  rwa [init_size] at this

/-- **The `treiber2.kl` workers terminate on the fuel-free semantic machine
under every schedule** (no fairness): any number of `treiber2DWorker`
threads; certification bound `certF |states|` (`treiber2_certBounded_gen`). -/
theorem treiber2_term_semU_gen (l : _root_.Layout) [Executable.ValidLayout (l treiber2DWorker)]
    (t : BitVec 64) {states : List isa.State} {initMem : List (Loc × Val)} (hs : ∀ s ∈ states, Start (layout := l) t s) :
    TermBoundSemU Arch.armv8 (Config.init states initMem : Config isa) :=
  termTransfer (treiber2_certBounded_gen l t hs) (treiber2_term_sem_gen (layout := l) t hs)

/-- **The two-thread Treiber stack `treiber2.kl` terminates on the fuel-free
semantic machine under every schedule**: the hypotheses of
`treiber2_term_sem`; certification bound `certF 2 = 162`. -/
theorem treiber2_term_semU (l : _root_.Layout) [Executable.ValidLayout (l treiber2DWorker)]
    (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (_hn : n0 ≠ n1) (_hn0 : n0 ≠ 0) (_hn1 : n1 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartWD (layout := l) t n0 1 s0) (h1 : StartWD (layout := l) t n1 2 s1)
    (_hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    TermBoundSemU Arch.armv8 (Config.init [s0, s1] initMem : Config isa) :=
  treiber2_term_semU_gen l t fun s hs => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨n0, 1, h0, ht0⟩
    · exact ⟨n1, 2, h1, ht1⟩

section
attribute [local instance] wLayout2D

/-- **`treiber2.kl` at the runner's layout and threads terminates on the
fuel-free semantic machine under every schedule** (the start configuration
of `treiber2_term_sem_concrete`; certification bound `162`). -/
theorem treiber2_term_semU_concrete :
    TermBoundSemU Arch.armv8 (Config.init [wWorker0, wWorker1] treiber2InitMem : Config isa) :=
  treiber2_term_semU wLayout2D topAddr n1Addr n2Addr (by decide) (by decide) (by decide) (by decide)
    (by decide) wWorker0_start wWorker1_start (by simp only [Config.init]; decide)

end

end Kraken.Promising.Live.TermTreiber2

namespace Kraken.Promising.Live.TermTreiber2Arm

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live.CertBounded
open Kraken.Promising.Live.CertBoundedTreiber2P (certF certBounded_genP' InvU init_size)
open Kraken.Promising.SLR.EnvG.Treiber2Arm (treiber2ArmWorker StartWA wLayoutA wWorkerA0 wWorkerA1 wWorkerA0_start
  wWorkerA1_start)
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr)
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2Data (treiber2InitMem)

/-- **Bounded certification for the `treiber2_arm.kl` workers**: bound
`certF |states|`, at any fuel. -/
theorem treiber2_arm_certBounded_all (l : _root_.Layout) [Executable.ValidLayout (l treiber2ArmWorker)]
    (t : BitVec 64) {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : ∀ s ∈ states, ∃ n d, StartWA (layout := l) t n d s ∧ t ≠ n + 8) :
    CertBoundedFrom Arch.armv8 (Config.init states initMem : Config isa) (certF states.length) := by
  have := certBounded_genP' (cells (layout := l)) (InvU.ofInv0 (inv_init (layout := l) (fuel := 0) (initMem := initMem) hs).toP)
  rwa [init_size] at this

/-- **The `treiber2_arm.kl` workers terminate on the fuel-free semantic
machine under every schedule** (any number of threads; certification bound
`certF |states|`). -/
theorem treiber2_arm_term_semU_all (l : _root_.Layout) [Executable.ValidLayout (l treiber2ArmWorker)]
    (t : BitVec 64) {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : ∀ s ∈ states, ∃ n d, StartWA (layout := l) t n d s ∧ t ≠ n + 8) :
    TermBoundSemU Arch.armv8 (Config.init states initMem : Config isa) :=
  termTransfer (treiber2_arm_certBounded_all l t hs) (treiber2_arm_term_sem_all l t hs)

/-- **`treiber2_arm.kl` terminates on the fuel-free semantic machine under
every schedule**: the hypotheses of `treiber2_arm_term_sem`; certification
bound `162`. -/
theorem treiber2_arm_term_semU (l : _root_.Layout) [Executable.ValidLayout (l treiber2ArmWorker)]
    (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (_hn : n0 ≠ n1) (_hn0 : n0 ≠ 0) (_hn1 : n1 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartWA (layout := l) t n0 1 s0) (h1 : StartWA (layout := l) t n1 2 s1)
    (_hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    TermBoundSemU Arch.armv8 (Config.init [s0, s1] initMem : Config isa) :=
  treiber2_arm_term_semU_all l t fun s hs => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨n0, 1, h0, ht0⟩
    · exact ⟨n1, 2, h1, ht1⟩

section
attribute [local instance] wLayoutA

/-- **`treiber2_arm.kl` at the runner's layout and threads terminates on the
fuel-free semantic machine under every schedule** (certification bound
`162`). -/
theorem treiber2_arm_term_semU_concrete :
    TermBoundSemU Arch.armv8 (Config.init [wWorkerA0, wWorkerA1] treiber2InitMem : Config isa) :=
  treiber2_arm_term_semU wLayoutA topAddr n1Addr n2Addr (by decide) (by decide) (by decide) (by decide)
    (by decide) wWorkerA0_start wWorkerA1_start (by simp only [Config.init]; decide)

end

end Kraken.Promising.Live.TermTreiber2Arm

namespace Kraken.Promising.Live.TermTreiber2Relaxed

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live.CertBounded
open Kraken.Promising.Live.CertBoundedTreiber2P (certF certBounded_genP' InvU init_size)
open Kraken.Promising.Reach.Treiber2Relaxed (StartWR)

/-- **Bounded certification for the `treiber2_relaxed.kl` workers**: bound
`certF |states|`, at any fuel. -/
theorem treiber2_relaxed_certBounded_all (l : _root_.Layout)
    [Executable.ValidLayout (l Reach.Treiber2Relaxed.code)] (t : BitVec 64) {states : List isa.State}
    {initMem : List (Loc × Val)} (hs : ∀ s ∈ states, ∃ n d, StartWR (layout := l) t n d s ∧ t ≠ n + 8) :
    CertBoundedFrom Arch.armv8 (Config.init states initMem : Config isa) (certF states.length) := by
  have := certBounded_genP' (cells (layout := l)) (InvU.ofInv0 (inv_init (layout := l) (fuel := 0) (initMem := initMem) hs).toP)
  rwa [init_size] at this

/-- **The `treiber2_relaxed.kl` workers terminate on the fuel-free semantic
machine under every schedule** (any number of threads; certification bound
`certF |states|`). -/
theorem treiber2_relaxed_term_semU_all (l : _root_.Layout)
    [Executable.ValidLayout (l Reach.Treiber2Relaxed.code)] (t : BitVec 64) {states : List isa.State}
    {initMem : List (Loc × Val)} (hs : ∀ s ∈ states, ∃ n d, StartWR (layout := l) t n d s ∧ t ≠ n + 8) :
    TermBoundSemU Arch.armv8 (Config.init states initMem : Config isa) :=
  termTransfer (treiber2_relaxed_certBounded_all l t hs) (treiber2_relaxed_term_sem_all l t hs)

/-- **`treiber2_relaxed.kl`'s two workers terminate on the fuel-free
semantic machine under every schedule** (the hypotheses of
`treiber2_relaxed_term_sem`; certification bound `162`). -/
theorem treiber2_relaxed_term_semU (l : _root_.Layout)
    [Executable.ValidLayout (l Reach.Treiber2Relaxed.code)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8)
    (ht1 : t ≠ n1 + 8) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartWR (layout := l) t n0 1 s0) (h1 : StartWR (layout := l) t n1 2 s1) :
    TermBoundSemU Arch.armv8 (Config.init [s0, s1] initMem : Config isa) :=
  treiber2_relaxed_term_semU_all l t fun s hs => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨n0, 1, h0, ht0⟩
    · exact ⟨n1, 2, h1, ht1⟩

end Kraken.Promising.Live.TermTreiber2Relaxed

namespace Kraken.Promising.Live.TermTreiber2Nodes

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live.CertBounded
open Kraken.Promising.Live.CertBoundedTreiber2P (certF certBounded_genP)
open Kraken.Promising.SLR.EnvG.Treiber2 (treiber2NImage StartWN)

/-- **Bounded certification for the `treiber2_nodes.kl` workers**: bound
`certF |states|`, at any fuel. -/
theorem treiber2_nodes_certBounded_all (l : _root_.Layout) [Executable.ValidLayout (l treiber2NImage)]
    (t : BitVec 64) {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : ∀ s ∈ states, ∃ n, StartWN (layout := l) t n s ∧ t ≠ n + 8) :
    CertBoundedFrom Arch.armv8 (Config.init states initMem : Config isa) (certF states.length) :=
  certBounded_genP (layout := l) cellsN fun s hs' =>
    let ⟨_, h, hn⟩ := hs s hs'
    start_of_startWN h hn

/-- **The `treiber2_nodes.kl` workers terminate on the fuel-free semantic
machine under every schedule** (any number of threads; certification bound
`certF |states|`). -/
theorem treiber2_nodes_term_semU_all (l : _root_.Layout) [Executable.ValidLayout (l treiber2NImage)]
    (t : BitVec 64) {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : ∀ s ∈ states, ∃ n, StartWN (layout := l) t n s ∧ t ≠ n + 8) :
    TermBoundSemU Arch.armv8 (Config.init states initMem : Config isa) :=
  termTransfer (treiber2_nodes_certBounded_all l t hs) (treiber2_nodes_term_sem_all l t hs)

/-- **The two-thread `treiber2_nodes.kl` terminates on the fuel-free
semantic machine under every schedule** (the hypotheses of
`treiber2_nodes_term_sem`; certification bound `162`). -/
theorem treiber2_nodes_term_semU (l : _root_.Layout) [Executable.ValidLayout (l treiber2NImage)]
    (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (_hn : n0 ≠ n1) (_hn0 : n0 ≠ 0) (_hn1 : n1 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartWN (layout := l) t n0 s0) (h1 : StartWN (layout := l) t n1 s1)
    (_hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    TermBoundSemU Arch.armv8 (Config.init [s0, s1] initMem : Config isa) :=
  treiber2_nodes_term_semU_all l t fun s hs => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨n0, h0, ht0⟩
    · exact ⟨n1, h1, ht1⟩

section
open Kraken.Promising.SLR.EnvG.Treiber2 (wLayout2N wNWorker0 wNWorker1 wNWorker0_start wNWorker1_start)
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr treiber2InitMem)
attribute [local instance] Kraken.Promising.SLR.EnvG.Treiber2.wLayout2N

/-- **`treiber2_nodes.kl` at the runner's layout and threads terminates on
the fuel-free semantic machine under every schedule** (certification bound
`162`). -/
theorem treiber2_nodes_term_semU_concrete :
    TermBoundSemU Arch.armv8 (Config.init [wNWorker0, wNWorker1] treiber2InitMem : Config isa) :=
  treiber2_nodes_term_semU wLayout2N topAddr n1Addr n2Addr (by decide) (by decide) (by decide) (by decide)
    (by decide) wNWorker0_start wNWorker1_start (by simp only [Config.init]; decide)

end

end Kraken.Promising.Live.TermTreiber2Nodes
