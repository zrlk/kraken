/-
**Combined runner theorems for x64: safety ∧ program-level fault freedom**
. Convenience theorems only.

For each x64 family with both a runner-exact safety theorem (`*_runner`:
the `.kl` runner's declarations, a conclusion about every final
configuration reachable under `Arch.tso`) and a program-level fault-freedom
theorem (`*_runner_faultFree`: `Config.FaultFree`, any
architecture, promises included), `*_runner_safe_faultFree` states both at
once, at the union of the two theorems' hypotheses:

  `(∀ cfg, Reachable Arch.tso fuel init cfg → cfg.final = true → Φ cfg) ∧
    Config.FaultFree A fuel init`.

The proof is the pair of the two existing theorems. The `_concrete(N)`
companions are at the runner's own threads, declarations and initial
memory.

Families: `spinlock`, `spinlock_cmpxchg`, `dekker_mfence`, `ticketlock3`,
`mp_relay3_xchg`, `mp_incl`, `spsc_queue`, `treiber_pp`, `treiber2`,
`msqueue2/3`. `treiber_aba_tagged`'s combined theorem is in
`RunnerSafeFFX64ABA.lean`. The fixed-`N` runner corollaries
(`*_concrete2/3`) get no combined twin; use `_concreteN`.
-/
import Kraken.Promising.SLR.EnvG.X64FaultFreeFixed
import Kraken.Promising.SLR.EnvG.MemValsTreiberPP
import Kraken.Promising.SLR.EnvG.MemValsTreiber2
import Kraken.Promising.SLR.EnvG.MemValsMsQueue
import Kraken.Promising.SLR.EnvG.MemValsX64Spsc
import Kraken.Promising.SLR.EnvG.X64SpinAbsRunner
import Kraken.Promising.SLR.EnvG.X64CmpxAbsRunner
import Kraken.Promising.SLR.EnvG.DekkerAbsRunner
import Kraken.Promising.SLR.EnvG.TicketXRunner
import Kraken.Promising.SLR.EnvG.X64RelayAbsRunner
import Kraken.Promising.SLR.EnvG.X64MpInclAbsRunner

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## `spinlock2/3.kl` -/

namespace Kraken.Promising.X64.EnvG.SpinAbs

/-- **x64 spinlock workers with the runner's declarations: the counter ends
at `N`, and no step faults.** -/
theorem x64_spin_counter_envG_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout spinImageV)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized) (N : Nat)
    (hdisj : Decls.overlaps (symV "lock") 4 (symV "counter") 4 = false) (hN32 : N < 2 ^ 32)
    (hag : ds.AgreesOn [(symV "lock", 4), (symV "counter", 4)]) {states : List isa.State}
    {initMem : List (Loc × Val)} (hst : ∀ s ∈ states, StartStateVD ds s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨symV "counter", 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨symV "lock", 4⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.tso fuel (Config.init states initMem) cfg → cfg.final = true →
      cfg.mem.finalVal ⟨symV "counter", 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree A fuel (Config.init states initMem) :=
  ⟨fun _ hc hf => x64_spin_counter_envG_runner hsz N hdisj hN32 hst hN hC0 hLk0 hc hf,
    x64_spin_counter_envG_runner_faultFree hsz hag hst⟩

/-- **`spinlock2.kl` / `spinlock3.kl`** from the runner's exact
configuration: safety and fault freedom. -/
theorem Concrete.x64_spin_counter_envG_runner_safe_faultFree_concreteN (N : Nat) (hN32 : N < 2 ^ 32)
    {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.tso fuel (Config.init (List.replicate N Concrete.spinWorkerD0)
        Concrete.spinInitMemV) c →
      c.final = true → c.mem.finalVal ⟨0x1000100, 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree (I := isa) A fuel
      (Config.init (List.replicate N Concrete.spinWorkerD0) Concrete.spinInitMemV) :=
  ⟨fun _ hc hf => Concrete.x64_spin_counter_envG_runner_concreteN N hN32 hc hf,
    Concrete.x64_spin_counter_envG_runner_faultFree_concreteN N⟩

end Kraken.Promising.X64.EnvG.SpinAbs

/-! ## `spinlock_cmpxchg2/3.kl` -/

namespace Kraken.Promising.X64.EnvG.CmpxAbs

/-- **x64 `cmpxchg` spinlock workers with the runner's declarations: the
counter ends at `N`, and no step faults.** -/
theorem x64_cmpx_counter_envG_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout cmpxImageV)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized) (N : Nat)
    (hdisj : Decls.overlaps (symC "lock") 4 (symC "counter") 4 = false) (hN32 : N < 2 ^ 32)
    (hag : ds.AgreesOn [(symC "lock", 4), (symC "counter", 4)]) {states : List isa.State}
    {initMem : List (Loc × Val)} (hst : ∀ s ∈ states, StartStateCVD ds s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨symC "counter", 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨symC "lock", 4⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.tso fuel (Config.init states initMem) cfg → cfg.final = true →
      cfg.mem.finalVal ⟨symC "counter", 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree A fuel (Config.init states initMem) :=
  ⟨fun _ hc hf => x64_cmpx_counter_envG_runner hsz N hdisj hN32 hst hN hC0 hLk0 hc hf,
    x64_cmpx_counter_envG_runner_faultFree hsz hag hst⟩

/-- **`spinlock_cmpxchg2.kl` / `spinlock_cmpxchg3.kl`** from the runner's
exact configuration: safety and fault freedom. -/
theorem Concrete.x64_cmpx_counter_envG_runner_safe_faultFree_concreteN (N : Nat) (hN32 : N < 2 ^ 32)
    {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.tso fuel (Config.init (List.replicate N Concrete.cmpxWorkerD0)
        Concrete.cmpxInitMemV) c →
      c.final = true → c.mem.finalVal ⟨0x1000100, 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree (I := isa) A fuel
      (Config.init (List.replicate N Concrete.cmpxWorkerD0) Concrete.cmpxInitMemV) :=
  ⟨fun _ hc hf => Concrete.x64_cmpx_counter_envG_runner_concreteN N hN32 hc hf,
    Concrete.x64_cmpx_counter_envG_runner_faultFree_concreteN N⟩

end Kraken.Promising.X64.EnvG.CmpxAbs

/-! ## `dekker_mfence.kl` -/

namespace Kraken.Promising.X64.EnvG.DekkerAbs

open Kraken.Promising.X64.EnvG.Dekker (Locs)

/-- **`dekker_mfence.kl` with the runner's declarations: the two threads
are never both in the critical section with the counter at `1`, and no step
faults.** -/
theorem x64_dekker_public_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout dkImageV)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hL : Locs (symD "flag0") (symD "flag1") (symD "counter"))
    (hag : ds.AgreesOn [(symD "flag0", 4), (symD "flag1", 4), (symD "counter", 4)]) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)}
    (h0 : StartDVD ds (symD "flag0") (symD "flag1") s0) (h1 : StartDVD ds (symD "flag1") (symD "flag0") s1)
    (hF0 : (Config.init [s0, s1] initMem).mem.initVal ⟨symD "flag0", 4⟩ = 0)
    (hF1 : (Config.init [s0, s1] initMem).mem.initVal ⟨symD "flag1", 4⟩ = 0)
    (hC : (Config.init [s0, s1] initMem).mem.initVal ⟨symD "counter", 4⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg → cfg.final = true →
      ¬ ((∃ t, cfg.threads[0]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
        (∃ t, cfg.threads[1]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
        cfg.mem.finalVal ⟨symD "counter", 4⟩ = 1)) ∧
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  ⟨fun _ hc hf => x64_dekker_public_runner hsz hL h0 h1 hF0 hF1 hC hc hf,
    x64_dekker_public_runner_faultFree hsz hag h0 h1⟩

/-- **`dekker_mfence.kl`** from the runner's exact configuration: safety
and fault freedom. -/
theorem Concrete.x64_dekker_public_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.tso fuel (Config.init [Concrete.dk0D, Concrete.dk1D] Concrete.dkInitMemV) c →
      c.final = true →
      ¬ ((∃ t, c.threads[0]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
        (∃ t, c.threads[1]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
        c.mem.finalVal ⟨0x1000200, 4⟩ = 1)) ∧
    Config.FaultFree (I := isa) A fuel (Config.init [Concrete.dk0D, Concrete.dk1D] Concrete.dkInitMemV) :=
  ⟨fun _ hc hf => Concrete.x64_dekker_public_runner_concrete hc hf,
    Concrete.x64_dekker_public_runner_faultFree_concrete⟩

end Kraken.Promising.X64.EnvG.DekkerAbs

/-! ## `ticketlock3.kl` -/

namespace Kraken.Promising.X64.EnvG.TicketX

/-- **x64 ticket-lock workers with the runner's declarations: the counter
ends at `N`, and no step faults.** The fault-freedom side's `hxo'`/`hxc'`
(address inequalities) follow from the runner side's non-overlap
hypotheses but are kept as stated there. -/
theorem ticket3_counter_envG_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout tk3ImageV)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized) (N : Nat)
    (hxo : Decls.overlaps (symTk "next") 4 (symTk "owner") 4 = false)
    (hxc : Decls.overlaps (symTk "next") 4 (symTk "counter") 4 = false)
    (hoc : Decls.overlaps (symTk "owner") 4 (symTk "counter") 4 = false) (hN32 : N + 1 < 2 ^ 32)
    (hxo' : symTk "next" ≠ symTk "owner") (hxc' : symTk "next" ≠ symTk "counter")
    (hag : ds.AgreesOn [(symTk "next", 4), (symTk "owner", 4), (symTk "counter", 4)])
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateTk ds s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨symTk "next", 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨symTk "owner", 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨symTk "counter", 4⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.tso fuel (Config.init states initMem) cfg → cfg.final = true →
      cfg.mem.finalVal ⟨symTk "counter", 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree A fuel (Config.init states initMem) :=
  ⟨fun _ hc hf => ticket3_counter_envG_runner hsz N hxo hxc hoc hN32 hst hN hX0 hO0 hC0 hc hf,
    ticket3_counter_envG_runner_faultFree hsz N hN32 hxo' hxc' hag hst⟩

/-- **`ticketlock3.kl`** (any `N`) from the runner's exact configuration:
safety and fault freedom. -/
theorem Concrete.ticket3_counter_envG_runner_safe_faultFree_concreteN (N : Nat) (hN32 : N + 1 < 2 ^ 32)
    {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.tso fuel (Config.init (List.replicate N Concrete.tk3WorkerD0)
        Concrete.tk3InitMemV) c →
      c.final = true → c.mem.finalVal ⟨0x1000200, 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree (I := isa) A fuel
      (Config.init (List.replicate N Concrete.tk3WorkerD0) Concrete.tk3InitMemV) :=
  ⟨fun _ hc hf => Concrete.ticket3_counter_envG_runner_concreteN N hN32 hc hf,
    Concrete.ticket3_counter_envG_runner_faultFree_concreteN N hN32⟩

end Kraken.Promising.X64.EnvG.TicketX

/-! ## `mp_relay3_xchg.kl` -/

namespace Kraken.Promising.X64.EnvG.RelayAbs

open Kraken.Promising.X64.EnvG.RelayX

/-- **`mp_relay3_xchg.kl` with the runner's declarations: the reader sees
`43` and `d` ends at `43`, and no step faults.** -/
theorem mp_relay3_xchg_envG_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout relayImageV)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hL : RelayLocs (symY "f1") (symY "f2") (symY "d"))
    (hag : ds.AgreesOn [(symY "f1", 4), (symY "d", 4), (symY "f2", 4)])
    {sW sY sR : isa.State} {initMem : List (Loc × Val)} (hW : StartWVD ds sW) (hY : StartYVD ds sY)
    (hR : StartRVD ds sR)
    (hF1 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨symY "f1", 4⟩ = 0)
    (hF2 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨symY "f2", 4⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.tso fuel (Config.init [sW, sY, sR] initMem) cfg → cfg.final = true →
      (∃ t, cfg.threads[2]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
        cfg.mem.finalVal ⟨symY "d", 4⟩ = 43#128) ∧
    Config.FaultFree A fuel (Config.init [sW, sY, sR] initMem) :=
  ⟨fun _ hc hf => mp_relay3_xchg_envG_runner hsz hL hW hY hR hF1 hF2 hc hf,
    mp_relay3_xchg_envG_runner_faultFree hsz hag hW hY hR⟩

/-- **`mp_relay3_xchg.kl`** from the runner's exact configuration: safety
and fault freedom. -/
theorem Concrete.mp_relay3_xchg_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.tso fuel
        (Config.init [Concrete.relayW0D, Concrete.relayY1D, Concrete.relayR2D] Concrete.relayInitMemV) c →
      c.final = true →
      (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
        c.mem.finalVal ⟨0x1000000, 4⟩ = 43#128) ∧
    Config.FaultFree (I := isa) A fuel
      (Config.init [Concrete.relayW0D, Concrete.relayY1D, Concrete.relayR2D] Concrete.relayInitMemV) :=
  ⟨fun _ hc hf => Concrete.mp_relay3_xchg_envG_runner_concrete hc hf,
    Concrete.mp_relay3_xchg_envG_runner_faultFree_concrete⟩

end Kraken.Promising.X64.EnvG.RelayAbs

/-! ## `mp_incl.kl` -/

namespace Kraken.Promising.X64.EnvG.MpInclAbs

/-- **`mp_incl.kl` with the runner's declarations: the reader sees `42`,
`d = 42` and `f = 1` at the end, and no step faults.** -/
theorem x64_mp_incl_envGV_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout mpInclImageV)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hfd : symM "f" ≠ symM "d") (hag : ds.AgreesOn [(symM "f", 4), (symM "d", 4)]) {sW sR : isa.State}
    {initMem : List (Loc × Val)} (hW : StartWMD ds sW) (hR : StartRMD ds sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨symM "f", 4⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.tso fuel (Config.init [sW, sR] initMem) cfg → cfg.final = true →
      (∃ t, cfg.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
        cfg.mem.finalVal ⟨symM "d", 4⟩ = 42#128 ∧ cfg.mem.finalVal ⟨symM "f", 4⟩ = 1#128) ∧
    Config.FaultFree A fuel (Config.init [sW, sR] initMem) :=
  ⟨fun _ hc hf => x64_mp_incl_envGV_runner hsz hfd hW hR hF0 hc hf,
    x64_mp_incl_envGV_runner_faultFree hsz hag hW hR⟩

/-- **`mp_incl.kl`** from the runner's exact configuration: safety and
fault freedom. -/
theorem Concrete.x64_mp_incl_envGV_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.tso fuel
        (Config.init [Concrete.mpInclW0D, Concrete.mpInclR1D] Concrete.mpInclInitMemV) c →
      c.final = true →
      (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
        c.mem.finalVal ⟨0x1000000, 4⟩ = 42#128 ∧ c.mem.finalVal ⟨0x1000100, 4⟩ = 1#128) ∧
    Config.FaultFree (I := isa) A fuel
      (Config.init [Concrete.mpInclW0D, Concrete.mpInclR1D] Concrete.mpInclInitMemV) :=
  ⟨fun _ hc hf => Concrete.x64_mp_incl_envGV_runner_concrete hc hf,
    Concrete.x64_mp_incl_envGV_runner_faultFree_concrete⟩

end Kraken.Promising.X64.EnvG.MpInclAbs

/-! ## `spsc_queue.kl` -/

namespace Kraken.Promising.X64.EnvG.SpscAbs

open Kraken.Promising.X64.EnvG.SpscX

/-- **x64 `spsc_queue.kl` with the runner's declarations: the consumer
reads `1, 2, 3`, and no step faults.** -/
theorem x64_spsc_envG_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout spscImageV)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hL : SpscLocs spscP) (hag : ds.AgreesOn (spscS spscP)) {sP sC : isa.State} {initMem : List (Loc × Val)}
    (hP : StartPVD ds sP) (hC : StartCVD ds sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "tail", 4⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "head", 4⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.tso fuel (Config.init [sP, sC] initMem) cfg → cfg.final = true →
      ∃ th, cfg.threads[1]? = some th ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r12) = 1 ∧
        BitVec.setWidth 32 (th.st.st.1.regs.get64 .r13) = 2 ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r14) = 3) ∧
    Config.FaultFree A fuel (Config.init [sP, sC] initMem) :=
  ⟨fun _ hc hf => x64_spsc_envG_runner hsz hL hP hC hT0 hH0 hc hf,
    x64_spsc_envG_runner_faultFree hsz hL hag hP hC hT0 hH0⟩

/-- **x64 `spsc_queue.kl`** from the runner's exact configuration: safety
and fault freedom. -/
theorem Concrete.x64_spsc_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.tso fuel (Config.init [Concrete.spscP0D, Concrete.spscC1D]
        Concrete.spscInitMemV) c →
      c.final = true →
      ∃ th, c.threads[1]? = some th ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r12) = 1 ∧
        BitVec.setWidth 32 (th.st.st.1.regs.get64 .r13) = 2 ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r14) = 3) ∧
    Config.FaultFree (I := isa) A fuel (Config.init [Concrete.spscP0D, Concrete.spscC1D] Concrete.spscInitMemV) :=
  ⟨fun _ hc hf => Concrete.x64_spsc_envG_runner_concrete hc hf, Concrete.x64_spsc_envG_runner_faultFree_concrete⟩

end Kraken.Promising.X64.EnvG.SpscAbs

/-! ## `treiber_pp.kl` -/

namespace Kraken.Promising.X64.EnvG.TreiberAbs

open Kraken.Promising.X64.EnvG.TreiberX

/-- **x64 `treiber_pp.kl` with the runner's declarations: the popper gets
the pushed node and its data, and no step faults.** `hag`, `hN0` are the
fault-freedom side's. -/
theorem x64_treiber_pp_envG_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout treiberImageV)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (htn : symT "top" ≠ symT "n1" + 8) (hag : ds.AgreesOn (pushS (symT "top") (symT "n1")))
    {sP sQ : isa.State} {initMem : List (Loc × Val)} (hP : StartPushVD ds sP) (hQ : StartPopVD ds sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨symT "top", 8⟩ = 0)
    (hN0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨symT "n1" + 8, 8⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.tso fuel (Config.init [sP, sQ] initMem) cfg → cfg.final = true →
      ∃ th, cfg.threads[1]? = some th ∧ th.st.st.1.regs.get64 .r10 = symT "n1" ∧
        BitVec.setWidth 32 (th.st.st.1.regs.get64 .r11) = 1) ∧
    Config.FaultFree A fuel (Config.init [sP, sQ] initMem) :=
  ⟨fun _ hc hf => x64_treiber_pp_envG_runner hsz htn hP hQ hT0 hc hf,
    x64_treiber_pp_envG_runner_faultFree hsz hag hP hQ hT0 hN0⟩

/-- **x64 `treiber_pp.kl`** from the runner's exact configuration: safety
and fault freedom. -/
theorem Concrete.x64_treiber_pp_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.tso fuel (Config.init [Concrete.treiberP0D, Concrete.treiberP1D]
        Concrete.treiberInitMemV) c →
      c.final = true →
      ∃ th, c.threads[1]? = some th ∧ th.st.st.1.regs.get64 .r10 = 0x1000100 ∧
        BitVec.setWidth 32 (th.st.st.1.regs.get64 .r11) = 1) ∧
    Config.FaultFree (I := isa) A fuel
      (Config.init [Concrete.treiberP0D, Concrete.treiberP1D] Concrete.treiberInitMemV) :=
  ⟨fun _ hc hf => Concrete.x64_treiber_pp_envG_runner_concrete hc hf,
    Concrete.x64_treiber_pp_envG_runner_faultFree_concrete⟩

end Kraken.Promising.X64.EnvG.TreiberAbs

/-! ## `treiber2.kl` -/

namespace Kraken.Promising.X64.EnvG.Treiber2X

/-- **x64 `treiber2.kl` with the runner's declarations: each worker pops
one of the two nodes, and no step faults.** `hag`, `hN1`, `hN2` are the
fault-freedom side's. -/
theorem x64_treiber2_envG_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout treiber2ImageV)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (h1 : symT2 "top" ≠ symT2 "n1") (h2 : symT2 "top" ≠ symT2 "n2") (hn : symT2 "n1" ≠ symT2 "n2")
    (hn1 : symT2 "n1" ≠ 0) (hn2 : symT2 "n2" ≠ 0)
    (hag : ds.AgreesOn (treiber2S (symT2 "top") (symT2 "n1") (symT2 "n2"))) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartWVD ds (symT2 "n1") s0) (h1' : StartWVD ds (symT2 "n2") s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨symT2 "top", 8⟩ = 0)
    (hN1 : (Config.init [s0, s1] initMem).mem.initVal ⟨symT2 "n1", 8⟩ = 0)
    (hN2 : (Config.init [s0, s1] initMem).mem.initVal ⟨symT2 "n2", 8⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg → cfg.final = true →
      ∃ th0 th1, cfg.threads[0]? = some th0 ∧ cfg.threads[1]? = some th1 ∧
        ((th0.st.st.1.regs.get64 .r12 = symT2 "n1" ∧ th1.st.st.1.regs.get64 .r12 = symT2 "n2") ∨
          (th0.st.st.1.regs.get64 .r12 = symT2 "n2" ∧ th1.st.st.1.regs.get64 .r12 = symT2 "n1"))) ∧
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  ⟨fun _ hc hf => x64_treiber2_envG_runner hsz h1 h2 hn hn1 hn2 h0 h1' hT0 hc hf,
    x64_treiber2_envG_runner_faultFree hsz hag h0 h1' hT0 hN1 hN2⟩

/-- **x64 `treiber2.kl`** from the runner's exact configuration: safety and
fault freedom. -/
theorem Concrete.x64_treiber2_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.tso fuel (Config.init [Concrete.treiber2P0D, Concrete.treiber2P1D]
        Concrete.treiber2InitMemV) c →
      c.final = true →
      ∃ th0 th1, c.threads[0]? = some th0 ∧ c.threads[1]? = some th1 ∧
        ((th0.st.st.1.regs.get64 .r12 = 0x1000100 ∧ th1.st.st.1.regs.get64 .r12 = 0x1000200) ∨
          (th0.st.st.1.regs.get64 .r12 = 0x1000200 ∧ th1.st.st.1.regs.get64 .r12 = 0x1000100))) ∧
    Config.FaultFree (I := isa) A fuel
      (Config.init [Concrete.treiber2P0D, Concrete.treiber2P1D] Concrete.treiber2InitMemV) :=
  ⟨fun _ hc hf => Concrete.x64_treiber2_envG_runner_concrete hc hf,
    Concrete.x64_treiber2_envG_runner_faultFree_concrete⟩

end Kraken.Promising.X64.EnvG.Treiber2X

/-! ## `msqueue2.kl` and `msqueue3.kl` -/

namespace Kraken.Promising.X64.EnvG.MsQueueX

/-- **x64 `msqueue2.kl` with the runner's declarations: the dequeuer gets
`n1` then `n2`, and no step faults.** `hag`, `hinit` are the fault-freedom
side's. -/
theorem x64_msqueue2_envG_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout msq2ImageV)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hht : symV "head" ≠ symV "tail")
    (hhs : symV "head" ≠ symV "s") (hh1 : symV "head" ≠ symV "n1") (hh2 : symV "head" ≠ symV "n2")
    (hts : symV "tail" ≠ symV "s") (ht1 : symV "tail" ≠ symV "n1") (ht2 : symV "tail" ≠ symV "n2")
    (hs1 : symV "s" ≠ symV "n1") (hs2 : symV "s" ≠ symV "n2") (h12 : symV "n1" ≠ symV "n2")
    (hn1 : symV "n1" ≠ 0) (hn2 : symV "n2" ≠ 0)
    (hag : ds.AgreesOn (msqS (symV "head") (symV "tail") (symV "s") (symV "n1") (symV "n2")))
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEVD ds s0) (h1 : StartDVD ds s1) (hi : InitV (Config.init [s0, s1] initMem).mem paramsV)
    (hinit : ∀ l, MsqValL (symV "head") (symV "tail") (symV "s") (symV "n1") (symV "n2") l →
      MsqValV (symV "s") (symV "n1") (symV "n2") ((Config.init [s0, s1] initMem).mem.initVal l)) :
    (∀ cfg : Config isa, Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg → cfg.final = true →
      ∃ th1, cfg.threads[1]? = some th1 ∧ th1.st.st.1.regs.get64 .r12 = symV "n1" ∧
        th1.st.st.1.regs.get64 .r13 = symV "n2") ∧
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  ⟨fun _ hc hf => x64_msqueue2_envG_runner hsz hht hhs hh1 hh2 hts ht1 ht2 hs1 hs2 h12 hn1 hn2 h0 h1 hi hc hf,
    x64_msqueue2_envG_runner_faultFree hsz hag h0 h1 hinit⟩

/-- **x64 `msqueue2.kl`** from the runner's exact configuration: safety
and fault freedom. -/
theorem Concrete.x64_msqueue2_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.tso fuel (Config.init [Concrete.msq2P0D, Concrete.msq2P1D]
        Concrete.msq2InitMemV) c →
      c.final = true →
      ∃ th1, c.threads[1]? = some th1 ∧ th1.st.st.1.regs.get64 .r12 = 0x1000100 ∧
        th1.st.st.1.regs.get64 .r13 = 0x1000200) ∧
    Config.FaultFree (I := isa) A fuel (Config.init [Concrete.msq2P0D, Concrete.msq2P1D] Concrete.msq2InitMemV) :=
  ⟨fun _ hc hf => Concrete.x64_msqueue2_envG_runner_concrete hc hf,
    Concrete.x64_msqueue2_envG_runner_faultFree_concrete⟩

end Kraken.Promising.X64.EnvG.MsQueueX

namespace Kraken.Promising.X64.EnvG.MsQueue3X

open Kraken.Promising.X64.EnvG.MsQueueX (msqS MsqValL MsqValV InitV x64_msqueue3_envG_runner_faultFree)

/-- **x64 `msqueue3.kl` with the runner's declarations: the two dequeuers
get the two nodes, and no step faults.** `hag`, `hinit` are the
fault-freedom side's. -/
theorem x64_msqueue3_envG_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout msq3ImageV)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hht : symV3 "head" ≠ symV3 "tail")
    (hhs : symV3 "head" ≠ symV3 "s") (hh1 : symV3 "head" ≠ symV3 "n1") (hh2 : symV3 "head" ≠ symV3 "n2")
    (hts : symV3 "tail" ≠ symV3 "s") (ht1 : symV3 "tail" ≠ symV3 "n1") (ht2 : symV3 "tail" ≠ symV3 "n2")
    (hs1 : symV3 "s" ≠ symV3 "n1") (hs2 : symV3 "s" ≠ symV3 "n2") (h12 : symV3 "n1" ≠ symV3 "n2")
    (hn1 : symV3 "n1" ≠ 0) (hn2 : symV3 "n2" ≠ 0)
    (hag : ds.AgreesOn (msqS (symV3 "head") (symV3 "tail") (symV3 "s") (symV3 "n1") (symV3 "n2")))
    {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEV3D ds s0) (h1 : StartDV3D ds s1) (h2 : StartDV3D ds s2)
    (hi : InitV (Config.init [s0, s1, s2] initMem).mem params3V)
    (hinit : ∀ l, MsqValL (symV3 "head") (symV3 "tail") (symV3 "s") (symV3 "n1") (symV3 "n2") l →
      MsqValV (symV3 "s") (symV3 "n1") (symV3 "n2") ((Config.init [s0, s1, s2] initMem).mem.initVal l)) :
    (∀ cfg : Config isa, Reachable Arch.tso fuel (Config.init [s0, s1, s2] initMem) cfg → cfg.final = true →
      MsQueue3FinalX (symV3 "n1") (symV3 "n2") cfg) ∧
    Config.FaultFree A fuel (Config.init [s0, s1, s2] initMem) :=
  ⟨fun _ hc hf => x64_msqueue3_envG_runner hsz hht hhs hh1 hh2 hts ht1 ht2 hs1 hs2 h12 hn1 hn2 h0 h1 h2 hi hc hf,
    x64_msqueue3_envG_runner_faultFree hsz hag h0 h1 h2 hinit⟩

/-- **x64 `msqueue3.kl`** from the runner's exact configuration: safety
and fault freedom. -/
theorem Concrete.x64_msqueue3_envG_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.tso fuel
        (Config.init [Concrete.msq3P0D, Concrete.msq3PDD, Concrete.msq3PDD] Concrete.msq3InitMemV) c →
      c.final = true → MsQueue3FinalX 0x1000100 0x1000200 c) ∧
    Config.FaultFree (I := isa) A fuel
      (Config.init [Concrete.msq3P0D, Concrete.msq3PDD, Concrete.msq3PDD] Concrete.msq3InitMemV) :=
  ⟨fun _ hc hf => Concrete.x64_msqueue3_envG_runner_concrete hc hf,
    Concrete.x64_msqueue3_envG_runner_faultFree_concrete⟩

end Kraken.Promising.X64.EnvG.MsQueue3X
