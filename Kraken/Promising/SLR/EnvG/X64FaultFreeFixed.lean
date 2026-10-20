/-
**Program-level fault freedom at the runner's declarations for the
fixed-layout x64 programs**:
`spinlock2/3.kl`, `spinlock_cmpxchg2/3.kl`, `dekker_mfence.kl`,
`ticketlock3.kl`, `mp_relay3_xchg.kl`, `mp_incl.kl`.

The no-fault-at-declarations proofs' `*_runner_noFault` theorems
(`X64NoFaultDLocks`, `X64NoFaultDMp`,
`X64NoFaultDMpIncl`) are rule-level: each thread rule's `wp` hypotheses
exclude a fault. The `*_runner_faultFree` theorems here are
**program-level**: no configuration reachable from the runner's start
states (under any architecture, promises included) has a faulting step
(`Config.FaultFree`). They need no SLR: the all-release purity
specifications the `*_runner` theorems already use (`spinNoNTSpecV`, …,
`tk3DispSpec`) sit at the programs' fixed layouts, hold at every reachable
thread state (`MemValsX64`, the value invariant at `L = ∅`), and their trees
are fault-free at declarations agreeing on the layout (`noFault_QX64MD_rootD`
/ `noFault_QX64MD_rootSameD` at the purity environment). The `_concrete`
instances are at the runner's own threads, declarations and initial memory.

`spsc_queue.kl` and `treiber_pp.kl` are not here: their purity
specifications use the layout `sAll` (`MemValsTreiberPP` covers
`treiber_pp.kl` with a value specification).

Phase-1 limit: single-access trees (or same-location, for `mp_incl.kl`'s
`incl`).
-/
import Kraken.Promising.SLR.EnvG.MemValsX64
import Kraken.Promising.SLR.EnvG.X64NoFaultDLocks
import Kraken.Promising.SLR.EnvG.X64NoFaultDMpIncl

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

variable {A : Arch} {Q : Loc → Val → Prop}

/-- **The tree of a thread where a purity specification holds is
fault-free**, for trees that repeat their root's location
(`noFault_relPureSpecQXD` at `noFault_QX64MD_rootSameD`). -/
theorem noFault_relPureSpecQXD_same (sp : RelPureSpecQX A Q) {ds : Decls} (hag : ds.AgreesOn sp.S)
    (hnf : DirsNoFaultCode sp.e)
    (hsame : ∀ st : State, st.exe = sp.e → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootSameD)
    {st : State} (h : sp.HoldsD ds st) (tree : EvTree State) (hex : isa.exec st = some tree) : tree.NoFault :=
  haveI := sp.valid
  noFault_QX64MD_rootSameD hag (relPureQ_fenceTotal A Q) (MaskOf.refl _) sp.le16 hnf sp.post_end hsame st () tree
    ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩ hex

/-- `ds` agrees on every sublayout of a layout it agrees on. -/
theorem Decls.agreesOn_sub {ds : Decls} {S S' : SharedEnv.Layout} (h : ds.AgreesOn S) (hs : ∀ p ∈ S', p ∈ S) :
    ds.AgreesOn S' :=
  fun p hp => h p (hs p hp)

end Kraken.Promising.X64.EnvG

/-! ## `spinlock2/3.kl` -/

namespace Kraken.Promising.X64.EnvG.SpinAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Spin Kraken.Promising.X64.EnvG.SpinLink
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spinImageV)]

/-- **No reachable configuration of verbatim spinlock workers with the
runner's declarations has a faulting step**, for `ds` agreeing on `lock` and
`counter`. -/
theorem x64_spin_counter_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hag : ds.AgreesOn [(symV "lock", 4), (symV "counter", 4)]) {states : List isa.State}
    {initMem : List (Loc × Val)} (hst : ∀ s ∈ states, StartStateVD ds s) :
    Config.FaultFree A fuel (Config.init states initMem) :=
  x64_faultFree_of_relPureSpecsQXD (fun _ => spinNoNTSpecV) (fun _ => ds) (fun _ => hsz) (fun _ => hag)
    (fun _ => spinImageV_noFaultCode) (fun _ => rootOnlyD_of_phase1TreeRX spinImageV_phase1)
    (init_threads_of fun _ s hs => spinNoNTSpecV_holdsD (hst s (List.mem_of_getElem? hs)))

end Kraken.Promising.X64.EnvG.SpinAbs

namespace Kraken.Promising.X64.EnvG.SpinAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR
open Kraken.Promising.X64.EnvG.SpinAbs Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG

section
attribute [local instance] spinLayoutV

/-- **`spinlock2.kl` (`N = 2`) and `spinlock3.kl` (`N = 3`) never fault**,
from the runner's exact configuration (`N` workers `spinWorkerD0`, initial
memory `spinInitMemV`). -/
theorem x64_spin_counter_envG_runner_faultFree_concreteN (N : Nat) {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init (List.replicate N spinWorkerD0) spinInitMemV) :=
  x64_spin_counter_envG_runner_faultFree spinDeclsD_sized (by rw [symV_lock, symV_counter]; decls_agrees_on)
    fun s hs => (List.eq_of_mem_replicate hs) ▸ spinWorkerD0_start

end

end Kraken.Promising.X64.EnvG.SpinAbs.Concrete

/-! ## `spinlock_cmpxchg2/3.kl` -/

namespace Kraken.Promising.X64.EnvG.CmpxAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Spin Kraken.Promising.X64.EnvG.SpinLink
open Kraken.Promising.X64.EnvG.CmpxPublic
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin

variable [layout : _root_.Layout] [Executable.ValidLayout (layout cmpxImageV)]

/-- **No reachable configuration of verbatim `lock cmpxchg` spinlock workers
with the runner's declarations has a faulting step.** -/
theorem x64_cmpx_counter_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hag : ds.AgreesOn [(symC "lock", 4), (symC "counter", 4)]) {states : List isa.State}
    {initMem : List (Loc × Val)} (hst : ∀ s ∈ states, StartStateCVD ds s) :
    Config.FaultFree A fuel (Config.init states initMem) :=
  x64_faultFree_of_relPureSpecsQXD (fun _ => cmpxNoNTSpecV) (fun _ => ds) (fun _ => hsz) (fun _ => hag)
    (fun _ => cmpxImageV_noFaultCode) (fun _ => rootOnlyD_of_phase1TreeFX cmpxImageV_phase1)
    (init_threads_of fun _ s hs => cmpxNoNTSpecV_holdsD (hst s (List.mem_of_getElem? hs)))

end Kraken.Promising.X64.EnvG.CmpxAbs

namespace Kraken.Promising.X64.EnvG.CmpxAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR
open Kraken.Promising.X64.EnvG.CmpxAbs Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG

section
attribute [local instance] cmpxLayoutV

/-- **`spinlock_cmpxchg2.kl` (`N = 2`) and `spinlock_cmpxchg3.kl` (`N = 3`)
never fault**, from the runner's exact configuration. -/
theorem x64_cmpx_counter_envG_runner_faultFree_concreteN (N : Nat) {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init (List.replicate N cmpxWorkerD0) cmpxInitMemV) :=
  x64_cmpx_counter_envG_runner_faultFree cmpxDeclsD_sized (by rw [symC_lock, symC_counter]; decls_agrees_on)
    fun s hs => (List.eq_of_mem_replicate hs) ▸ cmpxWorkerD0_start

end

end Kraken.Promising.X64.EnvG.CmpxAbs.Concrete

/-! ## `dekker_mfence.kl` -/

namespace Kraken.Promising.X64.EnvG.DekkerAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvG.Dekker
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Dekker

variable [layout : _root_.Layout] [Executable.ValidLayout (layout dkImageV)]

/-- **No reachable configuration of the two verbatim Dekker threads with the
runner's declarations has a faulting step**, for `ds` agreeing on both flags
and the counter. -/
theorem x64_dekker_public_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hag : ds.AgreesOn [(symD "flag0", 4), (symD "flag1", 4), (symD "counter", 4)]) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartDVD ds (symD "flag0") (symD "flag1") s0)
    (h1 : StartDVD ds (symD "flag1") (symD "flag0") s1) :
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) := by
  have hag' : ∀ tid, ds.AgreesOn (dkNoNTSpecsV tid).S := fun tid => by
    cases tid with
    | zero => exact hag
    | succ =>
      refine Decls.agreesOn_sub hag fun p hp => ?_
      simp only [dkNoNTSpecsV, dkNoNTSpecV, dkS, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      rcases hp with rfl | rfl | rfl <;> simp
  exact x64_faultFree_of_relPureSpecsQXD dkNoNTSpecsV (fun _ => ds) (fun _ => hsz) hag'
    (fun tid => by cases tid <;> exact dkImageV_noFaultCode)
    (fun tid => by cases tid <;> exact rootOnlyD_of_phase1TreeX dkImageV_phase1)
    (init_threads_of (dkNoNTSpecsV_initD h0 h1))

end Kraken.Promising.X64.EnvG.DekkerAbs

namespace Kraken.Promising.X64.EnvG.DekkerAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR
open Kraken.Promising.X64.EnvG.DekkerAbs Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvG.Dekker
open Kraken.Promising.X64.EnvG.Dekker

section
attribute [local instance] dkLayoutV

/-- **`dekker_mfence.kl` never faults**, from the runner's exact
configuration (`[dk0D, dk1D]`, `dkInitMemV`). -/
theorem x64_dekker_public_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [dk0D, dk1D] dkInitMemV) := by
  have h0 : StartDVD dkDeclsD (symD "flag0") (symD "flag1") dk0D := by
    rw [symD_flag0, symD_flag1]; exact dkThreadD_start _ _
  have h1 : StartDVD dkDeclsD (symD "flag1") (symD "flag0") dk1D := by
    rw [symD_flag0, symD_flag1]; exact dkThreadD_start _ _
  exact x64_dekker_public_runner_faultFree dkDeclsD_sized
    (by rw [symD_flag0, symD_flag1, symD_counter]; decls_agrees_on) h0 h1

end

end Kraken.Promising.X64.EnvG.DekkerAbs.Concrete

/-! ## `ticketlock3.kl` -/

namespace Kraken.Promising.X64.EnvG.TicketX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.TicketLock
open Kraken.Promising.X64.EnvG

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tk3ImageV)]

omit layout [Executable.ValidLayout (layout tk3ImageV)] in
/-- Every fence of the purity-and-phase environment has an outcome. -/
theorem dispPureX_fenceTotal (A : Arch) (Q : Loc → Val → Prop) (x : Loc) (N : Nat) :
    (dispPureX A Q x N).FenceTotal :=
  fun _ b => ⟨b, rfl⟩

omit layout [Executable.ValidLayout (layout tk3ImageV)] in
/-- **The tree of a thread where a purity-and-phase specification holds is
fault-free** (`noFault_QX64MD_rootD` at `dispPureX`, in either phase). -/
theorem noFault_dispSpecXD {A : Arch} {Q : Loc → Val → Prop} {x : Loc} {N : Nat} (sp : DispSpecX A Q x N)
    {ds : Decls} (hag : ds.AgreesOn sp.S) (hnf : DirsNoFaultCode sp.e)
    (hro : ∀ st : State, st.exe = sp.e → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyD)
    {b : Bool} {st : State} (h : sp.HoldsD ds b st) (tree : EvTree State) (hex : isa.exec st = some tree) :
    tree.NoFault :=
  haveI := sp.valid
  noFault_QX64MD_rootD (E := dispPureX A Q x N) hag (dispPureX_fenceTotal A Q x N) (MaskOf.refl _) sp.le16 hnf
    sp.post_end hro st b tree ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩ hex

/-- **No reachable configuration of verbatim ticket-lock workers with the
runner's declarations has a faulting step**, for `ds` agreeing on `next`,
`owner` and `counter` (the purity-and-phase specification `tk3DispSpec N`
of any bound `N + 1 < 2 ^ 32`, in any phase, at every reachable thread). -/
theorem ticket3_counter_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized) (N : Nat)
    (hN32 : N + 1 < 2 ^ 32) (hxo : symTk "next" ≠ symTk "owner") (hxc : symTk "next" ≠ symTk "counter")
    (hag : ds.AgreesOn [(symTk "next", 4), (symTk "owner", 4), (symTk "counter", 4)])
    {states : List isa.State} {initMem : List (Loc × Val)} (hst : ∀ s ∈ states, StartStateTk ds s) :
    Config.FaultFree A fuel (Config.init states initMem) :=
  faultFree_of_valInv (L := fun _ => False) (V := fun _ => True)
    (P := fun st => ∃ b, (tk3DispSpec N).HoldsD ds b st)
    (fun _ tree ⟨_, h⟩ hex => valX_of_all_empty _ (dispSpecX_stepD _ (.inl hsz) h tree hex).2.1)
    (fun _ tree ⟨_, h⟩ hex => noFault_dispSpecXD (tk3DispSpec N) hag tk3ImageV_noFaultCode
      (rootOnlyD_of_phase1TreeRX tk3ImageV_phase1) h tree hex)
    ⟨memVals_empty _ _, init_threads_of (P := fun _ st => ∃ b, (tk3DispSpec N).HoldsD ds b st) fun _ s hs =>
      ⟨false, tk3DispSpec_holds hN32 hxo hxc (hst s (List.mem_of_getElem? hs))⟩⟩

end Kraken.Promising.X64.EnvG.TicketX

namespace Kraken.Promising.X64.EnvG.TicketX.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR
open Kraken.Promising.X64.EnvG.TicketX Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvG.TicketLock

section
attribute [local instance] tk3LayoutV

/-- **`ticketlock3.kl` (`N = 3`) never faults**, nor does any number
`N + 1 < 2 ^ 32` of its workers, from the runner's exact configuration. -/
theorem ticket3_counter_envG_runner_faultFree_concreteN (N : Nat) (hN32 : N + 1 < 2 ^ 32) {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init (List.replicate N tk3WorkerD0) tk3InitMemV) :=
  ticket3_counter_envG_runner_faultFree tk3DeclsD_sized N hN32
    (by rw [symTk_next, symTk_owner]; decide) (by rw [symTk_next, symTk_counter]; decide)
    (by rw [symTk_next, symTk_owner, symTk_counter]; decls_agrees_on)
    fun s hs => (List.eq_of_mem_replicate hs) ▸ tk3WorkerD0_start

end

end Kraken.Promising.X64.EnvG.TicketX.Concrete

/-! ## `mp_relay3_xchg.kl` -/

namespace Kraken.Promising.X64.EnvG.RelayAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.MpLink Kraken.Promising.X64.EnvG.MpRelPure Kraken.Promising.X64.EnvG.MpPublic
open Kraken.Promising.X64.EnvG.TakeMp Kraken.Promising.X64.EnvG.RelayX

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relayImageV)]

omit layout [Executable.ValidLayout (layout relayImageV)] in
/-- Every cell of the image repeats its root's location (the purity
specifications are unmasked: every thread may run any cell). -/
theorem relayImageV_cellsRootSame : ∀ d ∈ relayImageV, ∀ (e : _root_.Executable) z, DirRootSameX e d z := by
  intro d hd e z s pc
  simp only [relayImageV, relayCodeV, relayDataV, List.cons_append, List.nil_append] at hd
  cells_root_same relayImageV hd

/-- **The whole image's trees repeat their root's location.** -/
theorem relayImageV_rootSame :
    ∀ st : State, st.exe = layout relayImageV → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootSameD :=
  rootSameTreeX_of_dirs (dirsRootSameX_layout relayImageV_cellsRootSame)

/-- **No reachable configuration of the verbatim relay's three threads with
the runner's declarations has a faulting step**, for `ds` agreeing on `f1`,
`d` and `f2`. -/
theorem mp_relay3_xchg_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hag : ds.AgreesOn [(symY "f1", 4), (symY "d", 4), (symY "f2", 4)])
    {sW sY sR : isa.State} {initMem : List (Loc × Val)} (hW : StartWVD ds sW) (hY : StartYVD ds sY)
    (hR : StartRVD ds sR) :
    Config.FaultFree A fuel (Config.init [sW, sY, sR] initMem) := by
  have hag' : ∀ tid, ds.AgreesOn (relayNoNTSpecV tid).S := fun tid => by
    refine Decls.agreesOn_sub hag fun p hp => ?_
    rcases tid with _ | _ | _ <;>
    · simp only [relayNoNTSpecV, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      rcases hp with rfl | rfl | rfl <;> simp
  exact x64_faultFree_of_relPureSpecsQXD' relayNoNTSpecV (fun _ => ds) (fun _ => hsz)
    (fun tid _ tree h hex => noFault_relPureSpecQXD_same (relayNoNTSpecV tid) (hag' tid)
      (by rcases tid with _ | _ | _ <;> exact relayImageV_noFaultCode)
      (by rcases tid with _ | _ | _ <;> exact relayImageV_rootSame) h tree hex)
    (init_threads_of (relayNoNTSpecV_initD hW hY hR))

end Kraken.Promising.X64.EnvG.RelayAbs

namespace Kraken.Promising.X64.EnvG.RelayAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR
open Kraken.Promising.X64.EnvG.RelayAbs Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG.RelayX

section
attribute [local instance] relayLayoutV

/-- **`mp_relay3_xchg.kl` never faults**, from the runner's exact
configuration (`[relayW0D, relayY1D, relayR2D]`, `relayInitMemV`). -/
theorem mp_relay3_xchg_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [relayW0D, relayY1D, relayR2D] relayInitMemV) :=
  mp_relay3_xchg_envG_runner_faultFree relayDeclsD_sized
    (by rw [symY_f1, symY_d, symY_f2]; decls_agrees_on) relayW0D_start relayY1D_start relayR2D_start

end

end Kraken.Promising.X64.EnvG.RelayAbs.Concrete

/-! ## `mp_incl.kl` -/

namespace Kraken.Promising.X64.EnvG.MpInclAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.MpLink Kraken.Promising.X64.EnvG.MpRelPure Kraken.Promising.X64.EnvG.MpPublic
open Kraken.Promising.X64.EnvG.MpInc Kraken.Promising.X64.EnvG.MpIncV

variable [layout : _root_.Layout] [Executable.ValidLayout (layout mpInclImageV)]

omit layout [Executable.ValidLayout (layout mpInclImageV)] in
/-- Every cell of the image repeats its root's location (`incl` loads and
stores `⟨rdi, 4⟩`; every other cell is single-access). -/
theorem mpInclImageV_cellsRootSame : ∀ d ∈ mpInclImageV, ∀ (e : _root_.Executable) z, DirRootSameX e d z := by
  intro d hd e z s pc
  simp only [mpInclImageV, mpInclCodeV, mpInclDataV, List.cons_append, List.nil_append] at hd
  cells_root_same mpInclImageV hd

/-- **The whole image's trees repeat their root's location.** -/
theorem mpInclImageV_rootSame :
    ∀ st : State, st.exe = layout mpInclImageV → st.decls = {} → ∀ tree, isa.exec st = some tree →
      tree.RootSameD :=
  rootSameTreeX_of_dirs (dirsRootSameX_layout mpInclImageV_cellsRootSame)

/-- **No reachable configuration of `mp_incl.kl`'s verbatim writer and
reader with the runner's declarations has a faulting step**, for `ds`
agreeing on `f` and `d`. -/
theorem x64_mp_incl_envGV_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hag : ds.AgreesOn [(symM "f", 4), (symM "d", 4)]) {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartWMD ds sW) (hR : StartRMD ds sR) :
    Config.FaultFree A fuel (Config.init [sW, sR] initMem) :=
  x64_faultFree_of_relPureSpecsQXD' mpInclNoNTSpecV (fun _ => ds) (fun _ => hsz)
    (fun tid _ tree h hex => noFault_relPureSpecQXD_same (mpInclNoNTSpecV tid)
      (by rcases tid with _ | _ <;> exact hag)
      (by rcases tid with _ | _ <;> exact mpInclImageV_noFaultCode)
      (by rcases tid with _ | _ <;> exact mpInclImageV_rootSame) h tree hex)
    (init_threads_of (mpInclNoNTSpecV_initD hW hR))

end Kraken.Promising.X64.EnvG.MpInclAbs

namespace Kraken.Promising.X64.EnvG.MpInclAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR
open Kraken.Promising.X64.EnvG.MpInclAbs Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG.Mp

section
attribute [local instance] mpInclLayoutV

/-- **`mp_incl.kl` never faults**, from the runner's exact configuration
(`[mpInclW0D, mpInclR1D]`, `mpInclInitMemV`). -/
theorem x64_mp_incl_envGV_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [mpInclW0D, mpInclR1D] mpInclInitMemV) :=
  x64_mp_incl_envGV_runner_faultFree mpInclDeclsD_sized (by rw [symM_f, symM_d]; decls_agrees_on)
    mpInclW0D_start mpInclR1D_start

end

end Kraken.Promising.X64.EnvG.MpInclAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.SpinAbs.Concrete.x64_spin_counter_envG_runner_faultFree_concreteN
#print axioms Kraken.Promising.X64.EnvG.CmpxAbs.Concrete.x64_cmpx_counter_envG_runner_faultFree_concreteN
#print axioms Kraken.Promising.X64.EnvG.DekkerAbs.Concrete.x64_dekker_public_runner_faultFree_concrete
#print axioms Kraken.Promising.X64.EnvG.TicketX.Concrete.ticket3_counter_envG_runner_faultFree_concreteN
#print axioms Kraken.Promising.X64.EnvG.RelayAbs.Concrete.mp_relay3_xchg_envG_runner_faultFree_concrete
#print axioms Kraken.Promising.X64.EnvG.MpInclAbs.Concrete.x64_mp_incl_envGV_runner_faultFree_concrete
