/-
**Combined runner theorems for AArch64: safety ∧ program-level fault
freedom**. Convenience theorems only.

For each AArch64 family with both a runner-exact safety theorem
(`*_runner`, the AArch64 declarations proofs pattern: the `.kl` runner's declarations, a
conclusion about every final configuration reachable under `Arch.armv8`)
and a program-level fault-freedom theorem (`*_runner_faultFree`, the AArch64
fault-freedom proofs and
the runner-exact fault-freedom proofs: `Config.FaultFree`, any architecture, promises included),
`*_runner_safe_faultFree` states both at once, at the union of the two
theorems' hypotheses:

  `(∀ cfg : Config isa, Reachable Arch.armv8 fuel init cfg → cfg.final = true → Φ cfg) ∧
    Config.FaultFree A fuel init`.

The proof is the pair of the two existing theorems. The `_concrete(N)`
companions are at the runner's own threads, declarations and initial
memory (no hypotheses beyond those of the existing runner concretes).

Families: `spinlock_cas`, `spinlock_swpl`, `ticketlock`, `ticketlock_al`,
`mp_relay3`, `mp_relay3_swpl`, `spsc_queue`, `treiber_pp`, `treiber2`,
`treiber2_nodes`, `treiber2_arm`, `msqueue1/2/3`. The fixed-`N` runner
corollaries (`*_concrete2/3`) get no combined twin; use `_concreteN`.
-/
import Kraken.Promising.SLR.EnvG.A64FaultFreeFixed
import Kraken.Promising.SLR.EnvG.MemValsA64TreiberPP
import Kraken.Promising.SLR.EnvG.MemValsA64Treiber2
import Kraken.Promising.SLR.EnvG.MemValsA64Treiber2Nodes
import Kraken.Promising.SLR.EnvG.MemValsA64Treiber2Arm
import Kraken.Promising.SLR.EnvG.MemValsA64MsQueue
import Kraken.Promising.SLR.EnvG.MemValsA64MsQueue23
import Kraken.Promising.SLR.EnvG.A64CasRunner
import Kraken.Promising.SLR.EnvG.A64SwplRunner
import Kraken.Promising.SLR.EnvG.A64TicketRunner
import Kraken.Promising.SLR.EnvG.A64WholeRelayRunner
import Kraken.Promising.SLR.EnvG.A64WholeRelaySwplRunner
import Kraken.Promising.SLR.EnvG.A64SpscWholeRunner
import Kraken.Promising.SLR.EnvG.A64WholeTreiberRunner
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2Runner
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2NodesRunner
import Kraken.Promising.SLR.EnvG.A64Treiber2ArmRunner
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue1Runner
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue2Runner
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue3Runner

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD)

/-! ## `spinlock_cas2/3.kl` -/

namespace Kraken.Promising.SLR.EnvG.CasSmoke

/-- **`spinlock_cas` workers with the runner's declarations: the counter
ends at `N`, and no step faults.** -/
theorem cas_counter_envG_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout casTtasWorker)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized)
    (N : Nat) (l c : BitVec 64) (hdisj : Decls.overlaps l 4 c 4 = false) (hN32 : N < 2 ^ 32)
    (hag : ds.AgreesOnA (casS l c)) {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, WithDeclsD ds (StartState l c) s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.armv8 fuel (Config.init states initMem) cfg → cfg.final = true →
      cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree A fuel (Config.init states initMem) :=
  ⟨fun _ hc hf => cas_counter_envG_runner hsz N l c hdisj hN32 hst hN hC0 hLk0 hc hf,
    cas_counter_envG_runner_faultFree hsz l c hag hst⟩

end Kraken.Promising.SLR.EnvG.CasSmoke

namespace Kraken.Promising.SLR.EnvG.ConcreteCas

/-- **`spinlock_cas2.kl` / `spinlock_cas3.kl`** from the runner's exact
configuration: safety and fault freedom. -/
theorem cas_counter_envG_runner_safe_faultFree_concreteN (N : Nat) (hN32 : N < 2 ^ 32) {A : Arch}
    {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.armv8 fuel (Config.init (List.replicate N casWorkerD0) casInitMem) c →
      c.final = true → c.mem.finalVal ⟨counterAddr, 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree (I := isa) A fuel (Config.init (List.replicate N casWorkerD0) casInitMem) :=
  ⟨fun _ hc hf => cas_counter_envG_runner_concreteN N hN32 hc hf,
    cas_counter_envG_runner_faultFree_concreteN N⟩

end Kraken.Promising.SLR.EnvG.ConcreteCas

/-! ## `spinlock_swpl2/3.kl` -/

namespace Kraken.Promising.SLR.EnvG.SwplLock

open Kraken.Promising.SLR.EnvG.CasSmoke (casS)

/-- **`spinlock_swpl` workers with the runner's declarations: the counter
ends at `N`, and no step faults.** -/
theorem swpl_counter_envG_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout swplWorker)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized)
    (N : Nat) (l c : BitVec 64) (hdisj : Decls.overlaps l 4 c 4 = false) (hN32 : N < 2 ^ 32)
    (hag : ds.AgreesOnA (casS l c)) {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, WithDeclsD ds (StartState l c) s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.armv8 fuel (Config.init states initMem) cfg → cfg.final = true →
      cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree A fuel (Config.init states initMem) :=
  ⟨fun _ hc hf => swpl_counter_envG_runner hsz N l c hdisj hN32 hst hN hC0 hLk0 hc hf,
    swpl_counter_envG_runner_faultFree hsz l c hag hst⟩

end Kraken.Promising.SLR.EnvG.SwplLock

namespace Kraken.Promising.SLR.EnvG.ConcreteSwpl

/-- **`spinlock_swpl2.kl` / `spinlock_swpl3.kl`** from the runner's exact
configuration: safety and fault freedom. -/
theorem swpl_counter_envG_runner_safe_faultFree_concreteN (N : Nat) (hN32 : N < 2 ^ 32) {A : Arch}
    {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.armv8 fuel (Config.init (List.replicate N swplWorkerD0) swplInitMem) c →
      c.final = true → c.mem.finalVal ⟨counterAddr, 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree (I := isa) A fuel (Config.init (List.replicate N swplWorkerD0) swplInitMem) :=
  ⟨fun _ hc hf => swpl_counter_envG_runner_concreteN N hN32 hc hf,
    swpl_counter_envG_runner_faultFree_concreteN N⟩

end Kraken.Promising.SLR.EnvG.ConcreteSwpl

/-! ## `ticketlock{2,3}.kl` and `ticketlock_al{2,3}.kl` -/

namespace Kraken.Promising.SLR.EnvG.TicketLock

/-- **`ldadda` ticket-lock workers with the runner's declarations: the
counter ends at `N`, and no step faults.** -/
theorem ticket_counter_envG_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout tkWorker)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized)
    (N : Nat) (x o c : BitVec 64) (hxo : Decls.overlaps x 4 o 4 = false) (hxc : Decls.overlaps x 4 c 4 = false)
    (hoc : Decls.overlaps o 4 c 4 = false) (hN32 : N + 1 < 2 ^ 32) (hag : ds.AgreesOnA (tkS x o c))
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, WithDeclsD ds (StartState x o c) s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.armv8 fuel (Config.init states initMem) cfg → cfg.final = true →
      cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree A fuel (Config.init states initMem) :=
  ⟨fun _ hc hf => ticket_counter_envG_runner hsz N x o c hxo hxc hoc hN32 hst hN hX0 hO0 hC0 hc hf,
    ticket_counter_envG_runner_faultFree hsz x o c hag hst⟩

/-- **`ldaddal` ticket-lock workers with the runner's declarations: the
counter ends at `N`, and no step faults.** -/
theorem ticket_al_counter_envG_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout tkWorkerAl)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized)
    (N : Nat) (x o c : BitVec 64) (hxo : Decls.overlaps x 4 o 4 = false) (hxc : Decls.overlaps x 4 c 4 = false)
    (hoc : Decls.overlaps o 4 c 4 = false) (hN32 : N + 1 < 2 ^ 32) (hag : ds.AgreesOnA (tkS x o c))
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, WithDeclsD ds (StartStateAl x o c) s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.armv8 fuel (Config.init states initMem) cfg → cfg.final = true →
      cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree A fuel (Config.init states initMem) :=
  ⟨fun _ hc hf => ticket_al_counter_envG_runner hsz N x o c hxo hxc hoc hN32 hst hN hX0 hO0 hC0 hc hf,
    ticket_al_counter_envG_runner_faultFree hsz x o c hag hst⟩

end Kraken.Promising.SLR.EnvG.TicketLock

namespace Kraken.Promising.SLR.EnvG.ConcreteTicketD

open Kraken.Promising.SLR.EnvG.ConcreteTicketAl (counterAddr tkAlInitMem)

/-- **`ticketlock2.kl` / `ticketlock3.kl`** from the runner's exact
configuration: safety and fault freedom. -/
theorem ticket_counter_envG_runner_safe_faultFree_concreteN (N : Nat) (hN32 : N + 1 < 2 ^ 32) {A : Arch}
    {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.armv8 fuel (Config.init (List.replicate N tkWorkerD0) tkAlInitMem) c →
      c.final = true → c.mem.finalVal ⟨counterAddr, 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree (I := isa) A fuel (Config.init (List.replicate N tkWorkerD0) tkAlInitMem) :=
  ⟨fun _ hc hf => ticket_counter_envG_runner_concreteN N hN32 hc hf,
    ticket_counter_envG_runner_faultFree_concreteN N⟩

end Kraken.Promising.SLR.EnvG.ConcreteTicketD

namespace Kraken.Promising.SLR.EnvG.ConcreteTicketAl

/-- **`ticketlock_al2.kl` / `ticketlock_al3.kl`** from the runner's exact
configuration: safety and fault freedom. -/
theorem ticket_al_counter_envG_runner_safe_faultFree_concreteN (N : Nat) (hN32 : N + 1 < 2 ^ 32) {A : Arch}
    {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.armv8 fuel (Config.init (List.replicate N tkAlWorkerD0) tkAlInitMem) c →
      c.final = true → c.mem.finalVal ⟨counterAddr, 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree (I := isa) A fuel (Config.init (List.replicate N tkAlWorkerD0) tkAlInitMem) :=
  ⟨fun _ hc hf => ticket_al_counter_envG_runner_concreteN N hN32 hc hf,
    ConcreteTicketD.ticket_al_counter_envG_runner_faultFree_concreteN N⟩

end Kraken.Promising.SLR.EnvG.ConcreteTicketAl

/-! ## `mp_relay3.kl` and `mp_relay3_swpl.kl` -/

namespace Kraken.Promising.SLR.EnvG.Relay

/-- **`mp_relay3.kl` with the runner's declarations: the reader sees `43`
and `d` ends at `43`, and no step faults.** -/
theorem mp_relay3_envG_runner_safe_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l relay3Img)] {ds : Decls} (hsz : ds.StrictSized) (f1 f2 d : BitVec 64)
    (hL : RelayLocs f1 f2 d) (hag : ds.AgreesOnA (relayS f1 f2 d)) {sW sY sR : isa.State}
    {initMem : List (Loc × Val)} (hW : WithDeclsD ds (StartW3 (layout := l) f1 d) sW)
    (hY : WithDeclsD ds (StartY3 (layout := l) f1 f2 d) sY) (hR : WithDeclsD ds (StartD3 (layout := l) f2 d) sR)
    (hF1 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f1, 4⟩ = 0)
    (hF2 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f2, 4⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.armv8 fuel (Config.init [sW, sY, sR] initMem) cfg → cfg.final = true →
      (∃ t, cfg.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
        cfg.mem.finalVal ⟨d, 4⟩ = 43#128) ∧
    Config.FaultFree A fuel (Config.init [sW, sY, sR] initMem) :=
  ⟨fun _ hc hf => mp_relay3_envG_runner l hsz f1 f2 d hL hW hY hR hF1 hF2 hc hf,
    mp_relay3_envG_runner_faultFree (layout := l) hsz f1 f2 d hag hW hY hR⟩

/-- **`mp_relay3.kl`** from the runner's exact configuration: safety and
fault freedom. -/
theorem mp_relay3_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.armv8 fuel (Config.init [writerDY0, relayDY1, readerDY2] relay3InitMem) c →
      c.final = true →
      (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
        c.mem.finalVal ⟨dAddrY, 4⟩ = 43#128) ∧
    Config.FaultFree (I := isa) A fuel (Config.init [writerDY0, relayDY1, readerDY2] relay3InitMem) :=
  ⟨fun _ hc hf => mp_relay3_envG_runner_concrete hc hf, mp_relay3_envG_runner_faultFree_concrete⟩

/-- **`mp_relay3_swpl.kl` with the runner's declarations: the reader sees
`43` and `d` ends at `43`, and no step faults.** -/
theorem mp_relay3_swpl_envG_runner_safe_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l relaySwpl3Img)] {ds : Decls} (hsz : ds.StrictSized) (f1 f2 d : BitVec 64)
    (hL : RelayLocs f1 f2 d) (hag : ds.AgreesOnA (relayS f1 f2 d)) {sW sY sR : isa.State}
    {initMem : List (Loc × Val)} (hW : WithDeclsD ds (StartWS3 (layout := l) f1 d) sW)
    (hY : WithDeclsD ds (StartYS3 (layout := l) f1 f2 d) sY) (hR : WithDeclsD ds (StartDS3 (layout := l) f2 d) sR)
    (hF1 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f1, 4⟩ = 0)
    (hF2 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f2, 4⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.armv8 fuel (Config.init [sW, sY, sR] initMem) cfg → cfg.final = true →
      (∃ t, cfg.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
        cfg.mem.finalVal ⟨d, 4⟩ = 43#128) ∧
    Config.FaultFree A fuel (Config.init [sW, sY, sR] initMem) :=
  ⟨fun _ hc hf => mp_relay3_swpl_envG_runner l hsz f1 f2 d hL hW hY hR hF1 hF2 hc hf,
    mp_relay3_swpl_envG_runner_faultFree (layout := l) hsz f1 f2 d hag hW hY hR⟩

/-- **`mp_relay3_swpl.kl`** from the runner's exact configuration: safety
and fault freedom. -/
theorem mp_relay3_swpl_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.armv8 fuel (Config.init [writerDS0, relayDS1, readerDS2] relaySwpl3InitMem) c →
      c.final = true →
      (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
        c.mem.finalVal ⟨0x1000, 4⟩ = 43#128) ∧
    Config.FaultFree (I := isa) A fuel (Config.init [writerDS0, relayDS1, readerDS2] relaySwpl3InitMem) :=
  ⟨fun _ hc hf => mp_relay3_swpl_envG_runner_concrete hc hf, mp_relay3_swpl_envG_runner_faultFree_concrete⟩

end Kraken.Promising.SLR.EnvG.Relay

/-! ## `spsc_queue.kl` -/

namespace Kraken.Promising.SLR.EnvG.SpscA

/-- **`spsc_queue.kl` with the runner's declarations: the consumer reads
`1, 2, 3`, and no step faults.** -/
theorem a64_spsc_envG_runner_safe_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l spscImageA)] {ds : Decls} (hsz : ds.StrictSized) (b h t : BitVec 64)
    (hL : SpscLocs ⟨b, h, t⟩) (hag : ds.AgreesOnA (spscS ⟨b, h, t⟩)) {sP sC : isa.State}
    {initMem : List (Loc × Val)} (hP : WithDeclsD ds (StartPW (layout := l) ⟨b, h, t⟩) sP)
    (hC : WithDeclsD ds (StartCW (layout := l) ⟨b, h, t⟩) sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨h, 8⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.armv8 fuel (Config.init [sP, sC] initMem) cfg → cfg.final = true →
      ∃ th, cfg.threads[1]? = some th ∧ BitVec.setWidth 32 th.st.st.1.regs.X10.toBitVec = 1 ∧
        BitVec.setWidth 32 th.st.st.1.regs.X11.toBitVec = 2 ∧ BitVec.setWidth 32 th.st.st.1.regs.X12.toBitVec = 3) ∧
    Config.FaultFree A fuel (Config.init [sP, sC] initMem) :=
  ⟨fun _ hc hf => a64_spsc_envG_runner l hsz b h t hL hP hC hT0 hH0 hc hf,
    a64_spsc_envG_runner_faultFree (layout := l) hsz _ hag hP hC⟩

/-- **`spsc_queue.kl`** from the runner's exact configuration: safety and
fault freedom. -/
theorem a64_spsc_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.armv8 fuel (Config.init [spscProdWD0, spscConsWD1] spscInitMemD) c →
      c.final = true →
      ∃ th, c.threads[1]? = some th ∧ BitVec.setWidth 32 th.st.st.1.regs.X10.toBitVec = 1 ∧
        BitVec.setWidth 32 th.st.st.1.regs.X11.toBitVec = 2 ∧ BitVec.setWidth 32 th.st.st.1.regs.X12.toBitVec = 3) ∧
    Config.FaultFree (I := isa) A fuel (Config.init [spscProdWD0, spscConsWD1] spscInitMemD) :=
  ⟨fun _ hc hf => a64_spsc_envG_runner_concrete hc hf, a64_spsc_envG_runner_faultFree_concrete⟩

end Kraken.Promising.SLR.EnvG.SpscA

/-! ## `treiber_pp.kl` -/

namespace Kraken.Promising.SLR.EnvG.Treiber

/-- **`treiber_pp.kl` with the runner's declarations: the popper gets the
pushed node and its data, and no step faults.** `hdnQ` and `hN0` are the
fault-freedom side's (`treiber_pp_envG_runner_faultFree`). -/
theorem treiber_pp_envG_runner_safe_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l treiberImageA)] {ds : Decls} (hsz : ds.StrictSized) (t n : BitVec 64)
    (htn : t ≠ n + 8) (hag : ds.AgreesOnA (treiberSA t n)) {sP sQ : isa.State} {initMem : List (Loc × Val)}
    (hP : StartPushWD (layout := l) ds t n sP) (hQ : StartPopWD (layout := l) ds t sQ)
    (hdnQ : Mem.loadInt sQ.st.1.dmem (n + 8) 8 = none)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨n + 8, 8⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.armv8 fuel (Config.init [sP, sQ] initMem) cfg → cfg.final = true →
      ∃ th, cfg.threads[1]? = some th ∧ th.st.st.1.regs.X10.toBitVec = n ∧ th.st.st.1.regs.X11.toBitVec = 1) ∧
    Config.FaultFree A fuel (Config.init [sP, sQ] initMem) :=
  ⟨fun _ hc hf => treiber_pp_envG_runner l hsz t n htn hP hQ hT0 hc hf,
    treiber_pp_envG_runner_faultFree (layout := l) hsz t n hag hP hQ hdnQ hT0 hN0⟩

open Kraken.Promising.SLR.EnvG.ConcreteTreiber in
/-- **`treiber_pp.kl`** from the runner's exact configuration: safety and
fault freedom. -/
theorem treiber_pp_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.armv8 fuel (Config.init [pusherWD0, popperWD1] treiberInitMem) c →
      c.final = true →
      ∃ th, c.threads[1]? = some th ∧ th.st.st.1.regs.X10.toBitVec = n1Addr ∧ th.st.st.1.regs.X11.toBitVec = 1) ∧
    Config.FaultFree (I := isa) A fuel (Config.init [pusherWD0, popperWD1] treiberInitMem) :=
  ⟨fun _ hc hf => treiber_pp_envG_runner_concrete hc hf, treiber_pp_envG_runner_faultFree_concrete⟩

end Kraken.Promising.SLR.EnvG.Treiber

/-! ## `treiber2.kl` and `treiber2_nodes.kl` -/

namespace Kraken.Promising.SLR.EnvG.Treiber2

open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr)

/-- **`treiber2.kl` with the runner's declarations: each worker pops one of
the two nodes with its data, and no step faults.** `hN0`, `hN1` are the
fault-freedom side's. -/
theorem treiber2_envG_runner_safe_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l treiber2DWorker)] {ds : Decls} (hsz : ds.StrictSized) (t n0 n1 : BitVec 64)
    (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0)
    (hag : ds.AgreesOnA (treiber2SA t n0 n1)) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : WithDeclsD ds (StartWD (layout := l) t n0 1) s0) (h1 : WithDeclsD ds (StartWD (layout := l) t n1 2) s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init [s0, s1] initMem).mem.initVal ⟨n0 + 8, 8⟩ = 0)
    (hN1 : (Config.init [s0, s1] initMem).mem.initVal ⟨n1 + 8, 8⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg → cfg.final = true →
      Treiber2DFinal n0 n1 cfg) ∧
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  ⟨fun _ hc hf => treiber2_envG_runner l hsz t n0 n1 ht0 ht1 hn hn0 hn1 h0 h1 hT0 hc hf,
    treiber2_envG_runner_faultFree l hsz t n0 n1 hag h0 h1 hT0 hN0 hN1⟩

/-- **`treiber2.kl`** from the runner's exact configuration: safety and
fault freedom. -/
theorem treiber2_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.armv8 fuel (Config.init [wWorkerD0, wWorkerD1] treiber2InitMemD) c →
      c.final = true → Treiber2DFinal n1Addr n2Addr c) ∧
    Config.FaultFree (I := isa) A fuel (Config.init [wWorkerD0, wWorkerD1] treiber2InitMemD) :=
  ⟨fun _ hc hf => treiber2_envG_runner_concrete hc hf, treiber2_envG_runner_faultFree_concrete⟩

/-- **`treiber2_nodes.kl` with the runner's declarations: each worker pops
one of the two nodes, and no step faults.** `hN0`, `hN1` are the
fault-freedom side's. -/
theorem treiber2_nodes_envG_runner_safe_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l treiber2NImage)] {ds : Decls} (hsz : ds.StrictSized) (t n0 n1 : BitVec 64)
    (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0)
    (hag : ds.AgreesOnA (treiber2NSA t n0 n1)) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : WithDeclsD ds (StartWN (layout := l) t n0) s0) (h1 : WithDeclsD ds (StartWN (layout := l) t n1) s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init [s0, s1] initMem).mem.initVal ⟨n0 + 8, 8⟩ = 0)
    (hN1 : (Config.init [s0, s1] initMem).mem.initVal ⟨n1 + 8, 8⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg → cfg.final = true →
      Treiber2Final n0 n1 cfg) ∧
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  ⟨fun _ hc hf => treiber2_nodes_envG_runner l hsz t n0 n1 ht0 ht1 hn hn0 hn1 h0 h1 hT0 hc hf,
    treiber2_nodes_envG_runner_faultFree l hsz t n0 n1 hag h0 h1 hT0 hN0 hN1⟩

/-- **`treiber2_nodes.kl`** from the runner's exact configuration: safety
and fault freedom. -/
theorem treiber2_nodes_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.armv8 fuel (Config.init [wNWorkerD0, wNWorkerD1] treiber2NInitMemD) c →
      c.final = true → Treiber2Final n1Addr n2Addr c) ∧
    Config.FaultFree (I := isa) A fuel (Config.init [wNWorkerD0, wNWorkerD1] treiber2NInitMemD) :=
  ⟨fun _ hc hf => treiber2_nodes_envG_runner_concrete hc hf, treiber2_nodes_envG_runner_faultFree_concrete⟩

end Kraken.Promising.SLR.EnvG.Treiber2

/-! ## `treiber2_arm.kl` -/

namespace Kraken.Promising.SLR.EnvG.Treiber2Arm

open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr)
open Kraken.Promising.SLR.EnvG.Treiber2 (Treiber2DFinal treiber2SA treiber2InitMemD)

/-- **`treiber2_arm.kl` with the runner's declarations: each worker pops
one of the two nodes with its data, and no step faults.** `hN0`, `hN1` are
the fault-freedom side's. -/
theorem treiber2_arm_envG_runner_safe_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l treiber2ArmWorker)] {ds : Decls} (hsz : ds.StrictSized) (t n0 n1 : BitVec 64)
    (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0)
    (hag : ds.AgreesOnA (treiber2SA t n0 n1)) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : WithDeclsD ds (StartWA (layout := l) t n0 1) s0) (h1 : WithDeclsD ds (StartWA (layout := l) t n1 2) s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init [s0, s1] initMem).mem.initVal ⟨n0 + 8, 8⟩ = 0)
    (hN1 : (Config.init [s0, s1] initMem).mem.initVal ⟨n1 + 8, 8⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg → cfg.final = true →
      Treiber2DFinal n0 n1 cfg) ∧
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  ⟨fun _ hc hf => treiber2_arm_envG_runner l hsz t n0 n1 ht0 ht1 hn hn0 hn1 h0 h1 hT0 hc hf,
    treiber2_arm_envG_runner_faultFree l hsz t n0 n1 hag h0 h1 hT0 hN0 hN1⟩

/-- **`treiber2_arm.kl`** from the runner's exact configuration: safety and
fault freedom. -/
theorem treiber2_arm_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.armv8 fuel (Config.init [wWorkerDA0, wWorkerDA1] treiber2InitMemD) c →
      c.final = true → Treiber2DFinal n1Addr n2Addr c) ∧
    Config.FaultFree (I := isa) A fuel (Config.init [wWorkerDA0, wWorkerDA1] treiber2InitMemD) :=
  ⟨fun _ hc hf => treiber2_arm_envG_runner_concrete hc hf, treiber2_arm_envG_runner_faultFree_concrete⟩

end Kraken.Promising.SLR.EnvG.Treiber2Arm

/-! ## `msqueue1/2/3.kl` -/

namespace Kraken.Promising.SLR.EnvG.MsQueue

/-- **`msqueue1.kl` with the runner's declarations: the dequeuer gets `1`,
and no step faults.** `hag`, `hv` are the fault-freedom side's. -/
theorem msqueue1_envG_runner_safe_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l msq1Image)] {ds : Decls} (hsz : ds.StrictSized) (h t d n1 : BitVec 64)
    (hht : h ≠ t) (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (htd : t ≠ d + 8) (htn : t ≠ n1 + 8) (hdn : d ≠ n1)
    (hag : ds.AgreesOnA (msqSA h t d n1 n1)) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : WithDeclsD ds (StartEQ1 (layout := l) t n1) s0) (h1 : WithDeclsD ds (StartDQ1 (layout := l) h t) s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem ⟨h, t, d, n1⟩)
    (hv : ∀ lc, MsqValLA h t d n1 n1 lc → MsqValVA d n1 n1 ((Config.init [s0, s1] initMem).mem.initVal lc)) :
    (∀ cfg : Config isa, Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg → cfg.final = true →
      ∃ th1, cfg.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1) ∧
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  ⟨fun _ hc hf => msqueue1_envG_runner l hsz h t d n1 hht hhd hhn htd htn hdn h0 h1 hi hc hf,
    msqueue1_envG_runner_faultFree l hsz h t d n1 hag h0 h1 hv⟩

/-- **`msqueue1.kl`** from the runner's exact configuration: safety and
fault freedom. -/
theorem msqueue1_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.armv8 fuel (Config.init [enqDQ1, deqDQ1] msq1InitMemD) c → c.final = true →
      ∃ th1, c.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1) ∧
    Config.FaultFree (I := isa) A fuel (Config.init [enqDQ1, deqDQ1] msq1InitMemD) :=
  ⟨fun _ hc hf => msqueue1_envG_runner_concrete hc hf, msqueue1_envG_runner_faultFree_concrete⟩

/-- **`msqueue2.kl` with the runner's declarations: the dequeuer gets `1`
then `2`, and no step faults.** `hag`, `hv` are the fault-freedom side's. -/
theorem msqueue2_envG_runner_safe_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l msq2Image)] {ds : Decls} (hsz : ds.StrictSized) (h t d n1 n2 : BitVec 64)
    (hht : h ≠ t) (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8) (htd : t ≠ d + 8)
    (htn : t ≠ n1 + 8) (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2) (hn1 : n1 ≠ 0)
    (hn2 : n2 ≠ 0) (hag : ds.AgreesOnA (msqSA h t d n1 n2)) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : WithDeclsD ds (StartEQ2 (layout := l) t n1 n2) s0) (h1 : WithDeclsD ds (StartDQ2 (layout := l) h t) s1)
    (hi : InitV2 (Config.init [s0, s1] initMem).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    (hv : ∀ lc, MsqValLA h t d n1 n2 lc → MsqValVA d n1 n2 ((Config.init [s0, s1] initMem).mem.initVal lc)) :
    (∀ cfg : Config isa, Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg → cfg.final = true →
      ∃ th1, cfg.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1 ∧
        th1.st.st.1.regs.X11.toBitVec = 2) ∧
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  ⟨fun _ hc hf => msqueue2_envG_runner l hsz h t d n1 n2 hht hhd hhn hhn2 htd htn htn2 hdn hdn2 hn12 hn1 hn2
      h0 h1 hi hc hf,
    msqueue2_envG_runner_faultFree l hsz h t d n1 n2 hag h0 h1 hv⟩

/-- **`msqueue2.kl`** from the runner's exact configuration: safety and
fault freedom. -/
theorem msqueue2_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.armv8 fuel (Config.init [enqDQ2, deqDQ2] msq2InitMemD) c → c.final = true →
      ∃ th1, c.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1 ∧
        th1.st.st.1.regs.X11.toBitVec = 2) ∧
    Config.FaultFree (I := isa) A fuel (Config.init [enqDQ2, deqDQ2] msq2InitMemD) :=
  ⟨fun _ hc hf => msqueue2_envG_runner_concrete hc hf, msqueue2_envG_runner_faultFree_concrete⟩

/-- **`msqueue3.kl` with the runner's declarations: the two dequeuers get
`1` and `2` in some order, and no step faults.** `hag`, `hv` are the
fault-freedom side's. -/
theorem msqueue3_envG_runner_safe_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l msq3Image)] {ds : Decls} (hsz : ds.StrictSized) (h t d n1 n2 : BitVec 64)
    (hht : h ≠ t) (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8) (htd : t ≠ d + 8)
    (htn : t ≠ n1 + 8) (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2) (hn1 : n1 ≠ 0)
    (hn2 : n2 ≠ 0) (hag : ds.AgreesOnA (msqSA h t d n1 n2)) {s0 s1 s2 : isa.State}
    {initMem : List (Loc × Val)} (h0 : WithDeclsD ds (StartEQ3 (layout := l) t n1 n2) s0)
    (h1 : WithDeclsD ds (StartDQ3 (layout := l) "deq1" "ddone1" h t) s1)
    (h2 : WithDeclsD ds (StartDQ3 (layout := l) "deq2" "ddone2" h t) s2)
    (hi : InitV2 (Config.init [s0, s1, s2] initMem).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    (hv : ∀ lc, MsqValLA h t d n1 n2 lc → MsqValVA d n1 n2 ((Config.init [s0, s1, s2] initMem).mem.initVal lc)) :
    (∀ cfg : Config isa, Reachable Arch.armv8 fuel (Config.init [s0, s1, s2] initMem) cfg → cfg.final = true →
      ∃ th1 th2, cfg.threads[1]? = some th1 ∧ cfg.threads[2]? = some th2 ∧
        ((th1.st.st.1.regs.X10.toBitVec = 1 ∧ th2.st.st.1.regs.X10.toBitVec = 2) ∨
          (th1.st.st.1.regs.X10.toBitVec = 2 ∧ th2.st.st.1.regs.X10.toBitVec = 1))) ∧
    Config.FaultFree A fuel (Config.init [s0, s1, s2] initMem) :=
  ⟨fun _ hc hf => msqueue3_envG_runner l hsz h t d n1 n2 hht hhd hhn hhn2 htd htn htn2 hdn hdn2 hn12 hn1 hn2
      h0 h1 h2 hi hc hf,
    msqueue3_envG_runner_faultFree l hsz h t d n1 n2 hag h0 h1 h2 hv⟩

/-- **`msqueue3.kl`** from the runner's exact configuration: safety and
fault freedom. -/
theorem msqueue3_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.armv8 fuel (Config.init [enqDQ3, deqADQ3, deqBDQ3] msq3InitMemD) c →
      c.final = true →
      ∃ th1 th2, c.threads[1]? = some th1 ∧ c.threads[2]? = some th2 ∧
        ((th1.st.st.1.regs.X10.toBitVec = 1 ∧ th2.st.st.1.regs.X10.toBitVec = 2) ∨
          (th1.st.st.1.regs.X10.toBitVec = 2 ∧ th2.st.st.1.regs.X10.toBitVec = 1))) ∧
    Config.FaultFree (I := isa) A fuel (Config.init [enqDQ3, deqADQ3, deqBDQ3] msq3InitMemD) :=
  ⟨fun _ hc hf => msqueue3_envG_runner_concrete hc hf, msqueue3_envG_runner_faultFree_concrete⟩

end Kraken.Promising.SLR.EnvG.MsQueue
