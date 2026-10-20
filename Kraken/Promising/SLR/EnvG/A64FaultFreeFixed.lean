/-
**Program-level fault freedom at the runner's declarations for the
fixed-layout AArch64 programs**:
`spinlock_cas2/3.kl`, `spinlock_swpl2/3.kl`, `ticketlock{2,3}.kl`,
`ticketlock_al{2,3}.kl`, `mp_relay3.kl`, `mp_relay3_swpl.kl`,
`spsc_queue.kl`.

The AArch64 no-fault-at-declarations proofs' `*_runner_noFault` theorems (`A64NoFaultDLocks`,
`A64NoFaultDRelay`, `A64NoFaultDSpsc`) are rule-level: each thread rule's
invariant excludes a fault. The `*_runner_faultFree` theorems here are
**program-level**: no configuration reachable from the runner's start
states (under any architecture, promises included) has a faulting step
(`Config.FaultFree`). They need no SLR and no ghost state: the AArch64
no-fault-at-declarations proofs'
address runs (`AddrSafeA`, in `invTop S`) are value specifications at
`G = ⊤` (`ValSpecA.ofAddr`), which hold at every reachable thread state and
whose trees are fault-free at declarations agreeing on the layout
(`a64_faultFree_of_addrSpecs`, `MemValsA64`). The `_concrete` instances are
at the runner's own threads, declarations and initial memory.

Phase-1 limit: single-access trees (`RootOnlyDA`).
-/
import Kraken.Promising.SLR.EnvG.MemValsA64
import Kraken.Promising.SLR.EnvG.A64NoFaultDLocks
import Kraken.Promising.SLR.EnvG.A64NoFaultDRelay
import Kraken.Promising.SLR.EnvG.A64NoFaultDSpsc

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP

/-! ## `spinlock_cas2/3.kl` -/

namespace Kraken.Promising.SLR.EnvG.CasSmoke

open Kraken.Promising.AArch64.EnvG Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

variable [layout : _root_.Layout] [Executable.ValidLayout (layout casTtasWorker)]

/-- The CAS worker's address run as a value specification at `G = ⊤`. -/
def casSpecA (l c : BitVec 64) : ValSpecA fun _ _ => True :=
  .ofAddr (casS l c) (layout casTtasWorker) (layout casTtasWorker)
    ((layout casTtasWorker).addrOf casTtasWorker.length) casTtasWorker_noPairs (MaskOf.refl _)
    casTtasWorker_rmwLive casTtasWorker_noFault (rootOnlyDA_of_phase1Tree casTtasWorker_phase1)

theorem casSpecA_holdsD {ds : Decls} {l c : BitVec 64} {s : isa.State} (hst : WithDeclsD ds (StartState l c) s) :
    (casSpecA l c).HoldsD ds s := by
  letI : CodeEnv := ⟨layout casTtasWorker⟩
  obtain ⟨hds, hst⟩ := hst
  exact holdsD_ofAddr (st := s) hst.exe hds hst.endPc
    (addrSafeA_of_partialTripleEnv (casWorker_addr l c).uncount rfl hst.pc ⟨0, hst.x0, hst.x1, hst.dl, hst.dc⟩)

/-- **No reachable configuration of CAS spinlock workers with the runner's
declarations has a faulting step**, for strict sized `ds` agreeing on the
lock and the counter words. -/
theorem cas_counter_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized)
    (l c : BitVec 64) (hag : ds.AgreesOnA (casS l c)) {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, WithDeclsD ds (StartState l c) s) :
    Config.FaultFree A fuel (Config.init states initMem) :=
  a64_faultFree_of_addrSpecs (fun _ => casSpecA l c) (fun _ => ds) (fun _ => hsz) (fun _ => hag)
    (init_threads_ofA fun _ s hs => casSpecA_holdsD (hst s (List.mem_of_getElem? hs)))

end Kraken.Promising.SLR.EnvG.CasSmoke

namespace Kraken.Promising.SLR.EnvG.ConcreteCas

open Kraken.Promising.SLR.EnvG.CasSmoke
open Kraken.Promising.SLR.EnvG.A64Whole (withDeclsD_of)

/-- **`spinlock_cas2.kl` (`N = 2`) and `spinlock_cas3.kl` (`N = 3`) never
fault**, from the runner's exact configuration (`N` workers `casWorkerD0`,
initial memory `casInitMem`), under any architecture. -/
theorem cas_counter_envG_runner_faultFree_concreteN (N : Nat) {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init (List.replicate N casWorkerD0) casInitMem) :=
  cas_counter_envG_runner_faultFree (layout := casLayout) casDeclsD_sized _ _ casDeclsD_agreesA
    fun _ hs => (List.eq_of_mem_replicate hs) ▸ withDeclsD_of rfl casWorker0_start

end Kraken.Promising.SLR.EnvG.ConcreteCas

/-! ## `spinlock_swpl2/3.kl` -/

namespace Kraken.Promising.SLR.EnvG.SwplLock

open Kraken.Promising.AArch64.EnvG Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.CasSmoke (casS)
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swplWorker)]

/-- The `swpl` worker's address run as a value specification at `G = ⊤`. -/
def swplSpecA (l c : BitVec 64) : ValSpecA fun _ _ => True :=
  .ofAddr (casS l c) (layout swplWorker) (layout swplWorker)
    ((layout swplWorker).addrOf swplWorker.length) swplWorker_noPairs (MaskOf.refl _)
    swplWorker_rmwLive swplWorker_noFault (rootOnlyDA_of_phase1TreeR swplWorker_phase1R)

theorem swplSpecA_holdsD {ds : Decls} {l c : BitVec 64} {s : isa.State}
    (hst : WithDeclsD ds (StartState l c) s) : (swplSpecA l c).HoldsD ds s := by
  letI : CodeEnv := ⟨layout swplWorker⟩
  obtain ⟨hds, hst⟩ := hst
  exact holdsD_ofAddr (st := s) hst.exe hds hst.endPc
    (addrSafeA_of_partialTripleEnv (swplWorker_addr l c).uncount rfl hst.pc ⟨0, hst.x0, hst.x1, hst.dl, hst.dc⟩)

/-- **No reachable configuration of `swpl`-released spinlock workers with
the runner's declarations has a faulting step.** -/
theorem swpl_counter_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized)
    (l c : BitVec 64) (hag : ds.AgreesOnA (casS l c)) {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, WithDeclsD ds (StartState l c) s) :
    Config.FaultFree A fuel (Config.init states initMem) :=
  a64_faultFree_of_addrSpecs (fun _ => swplSpecA l c) (fun _ => ds) (fun _ => hsz) (fun _ => hag)
    (init_threads_ofA fun _ s hs => swplSpecA_holdsD (hst s (List.mem_of_getElem? hs)))

end Kraken.Promising.SLR.EnvG.SwplLock

namespace Kraken.Promising.SLR.EnvG.ConcreteSwpl

open Kraken.Promising.SLR.EnvG.SwplLock
open Kraken.Promising.SLR.EnvG.A64Whole (withDeclsD_of)

/-- **`spinlock_swpl2.kl` (`N = 2`) and `spinlock_swpl3.kl` (`N = 3`) never
fault**, from the runner's exact configuration. -/
theorem swpl_counter_envG_runner_faultFree_concreteN (N : Nat) {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init (List.replicate N swplWorkerD0) swplInitMem) :=
  swpl_counter_envG_runner_faultFree (layout := swplLayout) swplDeclsD_sized _ _ swplDeclsD_agreesA
    fun _ hs => (List.eq_of_mem_replicate hs) ▸ withDeclsD_of rfl swplWorker0_start

end Kraken.Promising.SLR.EnvG.ConcreteSwpl

/-! ## `ticketlock{2,3}.kl` and `ticketlock_al{2,3}.kl` -/

namespace Kraken.Promising.SLR.EnvG.TicketLock

open Kraken.Promising.AArch64.EnvG Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

variable [layout : _root_.Layout]

/-- The `ldadda` worker's address run as a value specification at `G = ⊤`. -/
def tkSpecA [Executable.ValidLayout (layout tkWorker)] (x o c : BitVec 64) :
    ValSpecA fun _ _ => True :=
  .ofAddr (tkS x o c) (layout tkWorker) (layout tkWorker)
    ((layout tkWorker).addrOf tkWorker.length) tkWorker_noPairs (MaskOf.refl _)
    tkWorker_rmwLive tkWorker_noFault (rootOnlyDA_of_phase1Tree tkWorker_phase1)

/-- The `ldaddal` worker's address run as a value specification at `G = ⊤`. -/
def tkAlSpecA [Executable.ValidLayout (layout tkWorkerAl)] (x o c : BitVec 64) :
    ValSpecA fun _ _ => True :=
  .ofAddr (tkS x o c) (layout tkWorkerAl) (layout tkWorkerAl)
    ((layout tkWorkerAl).addrOf tkWorkerAl.length) tkWorkerAl_noPairs (MaskOf.refl _)
    tkWorkerAl_rmwLive tkWorkerAl_noFault (rootOnlyDA_of_phase1TreeR tkWorkerAl_phase1R)

theorem tkSpecA_holdsD [Executable.ValidLayout (layout tkWorker)] {ds : Decls} {x o c : BitVec 64}
    {s : isa.State} (hst : WithDeclsD ds (StartState x o c) s) : (tkSpecA x o c).HoldsD ds s := by
  letI : CodeEnv := ⟨layout tkWorker⟩
  obtain ⟨hds, hst⟩ := hst
  exact holdsD_ofAddr (st := s) hst.exe hds hst.endPc (addrSafeA_of_partialTripleEnv (tkWorker_addr x o c).uncount rfl
    hst.pc ⟨0, hst.x0, hst.x1, hst.x2, hst.dx, hst.dO, hst.dc⟩)

theorem tkAlSpecA_holdsD [Executable.ValidLayout (layout tkWorkerAl)] {ds : Decls} {x o c : BitVec 64}
    {s : isa.State} (hst : WithDeclsD ds (StartStateAl x o c) s) : (tkAlSpecA x o c).HoldsD ds s := by
  letI : CodeEnv := ⟨layout tkWorkerAl⟩
  obtain ⟨hds, hst⟩ := hst
  exact holdsD_ofAddr (st := s) hst.exe hds hst.endPc (addrSafeA_of_partialTripleEnv (tkWorkerAl_addr x o c).uncount rfl
    hst.pc ⟨0, hst.x0, hst.x1, hst.x2, hst.dx, hst.dO, hst.dc⟩)

/-- **No reachable configuration of `ldadda` ticket-lock workers with the
runner's declarations has a faulting step.** -/
theorem ticket_counter_envG_runner_faultFree [Executable.ValidLayout (layout tkWorker)] {A : Arch} {fuel : Nat}
    {ds : Decls} (hsz : ds.StrictSized) (x o c : BitVec 64) (hag : ds.AgreesOnA (tkS x o c))
    {states : List isa.State} {initMem : List (Loc × Val)} (hst : ∀ s ∈ states, WithDeclsD ds (StartState x o c) s) :
    Config.FaultFree A fuel (Config.init states initMem) :=
  a64_faultFree_of_addrSpecs (fun _ => tkSpecA x o c) (fun _ => ds) (fun _ => hsz) (fun _ => hag)
    (init_threads_ofA fun _ s hs => tkSpecA_holdsD (hst s (List.mem_of_getElem? hs)))

/-- **No reachable configuration of `ldaddal` ticket-lock workers with the
runner's declarations has a faulting step.** -/
theorem ticket_al_counter_envG_runner_faultFree [Executable.ValidLayout (layout tkWorkerAl)] {A : Arch}
    {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized) (x o c : BitVec 64) (hag : ds.AgreesOnA (tkS x o c))
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, WithDeclsD ds (StartStateAl x o c) s) :
    Config.FaultFree A fuel (Config.init states initMem) :=
  a64_faultFree_of_addrSpecs (fun _ => tkAlSpecA x o c) (fun _ => ds) (fun _ => hsz) (fun _ => hag)
    (init_threads_ofA fun _ s hs => tkAlSpecA_holdsD (hst s (List.mem_of_getElem? hs)))

end Kraken.Promising.SLR.EnvG.TicketLock

namespace Kraken.Promising.SLR.EnvG.ConcreteTicketD

open Kraken.Promising.SLR.EnvG.TicketLock
open Kraken.Promising.SLR.EnvG.ConcreteTicketAl
open Kraken.Promising.SLR.EnvG.A64Whole (withDeclsD_of)

/-- **`ticketlock2.kl` (`N = 2`) and `ticketlock3.kl` (`N = 3`) never
fault**, from the runner's exact configuration. -/
theorem ticket_counter_envG_runner_faultFree_concreteN (N : Nat) {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init (List.replicate N tkWorkerD0) tkAlInitMem) :=
  ticket_counter_envG_runner_faultFree (layout := tkLayoutD) tkDeclsD_sized _ _ _ tkDeclsD_agreesA
    fun _ hs => (List.eq_of_mem_replicate hs) ▸ withDeclsD_of rfl tkWorker0_start

/-- **`ticketlock_al2.kl` (`N = 2`) and `ticketlock_al3.kl` (`N = 3`) never
fault**, from the runner's exact configuration. -/
theorem ticket_al_counter_envG_runner_faultFree_concreteN (N : Nat) {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init (List.replicate N tkAlWorkerD0) tkAlInitMem) :=
  ticket_al_counter_envG_runner_faultFree (layout := tkAlLayout) tkDeclsD_sized _ _ _ tkDeclsD_agreesA
    fun _ hs => (List.eq_of_mem_replicate hs) ▸ withDeclsD_of rfl tkAlWorker0_start

end Kraken.Promising.SLR.EnvG.ConcreteTicketD

/-! ## `mp_relay3.kl` and `mp_relay3_swpl.kl` -/

namespace Kraken.Promising.SLR.EnvG.Relay

open Kraken.Promising.AArch64.EnvG Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

section Plain

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relay3Img)]

/-- The whole-image writer's address run (over its mask) at `G = ⊤`. -/
def relayW3SpecA (f1 f2 d : BitVec 64) : ValSpecA fun _ _ => True :=
  .ofAddr (relayS f1 f2 d) (layout relay3Img) (layout relay3ImgW) (labY3 "wdone") relay3Img_noPairs
    relay3ImgW_mask relay3Img_rmwLive relay3Img_noFault (rootOnlyDA_of_phase1Tree relay3ImgW_phase1)

/-- The whole-image relay's address run (over its mask) at `G = ⊤`. -/
def relayY3SpecA (f1 f2 d : BitVec 64) : ValSpecA fun _ _ => True :=
  .ofAddr (relayS f1 f2 d) (layout relay3Img) (layout relay3ImgY) (labY3 "rdone") relay3Img_noPairs
    relay3ImgY_mask relay3Img_rmwLive relay3Img_noFault (rootOnlyDA_of_phase1Tree relay3ImgY_phase1)

/-- The whole-image reader's address run at `G = ⊤`. -/
def relayD3SpecA (f1 f2 d : BitVec 64) : ValSpecA fun _ _ => True :=
  .ofAddr (relayS f1 f2 d) (layout relay3Img) (layout relay3Img) (labY3 "ddone") relay3Img_noPairs
    (MaskOf.refl _) relay3Img_rmwLive relay3Img_noFault (rootOnlyDA_of_phase1Tree relay3Img_phase1)

/-- The three roles' specifications by thread id. -/
def relay3SpecA (f1 f2 d : BitVec 64) : Nat → ValSpecA fun _ _ => True
  | 0 => relayW3SpecA f1 f2 d
  | 1 => relayY3SpecA f1 f2 d
  | _ => relayD3SpecA f1 f2 d

/-- **No reachable configuration of the verbatim `mp_relay3.kl` threads
with the runner's declarations has a faulting step**, for strict sized `ds`
agreeing on `f1`, `f2` and `d`. -/
theorem mp_relay3_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized)
    (f1 f2 d : BitVec 64) (hag : ds.AgreesOnA (relayS f1 f2 d)) {sW sY sR : isa.State}
    {initMem : List (Loc × Val)} (hW : WithDeclsD ds (StartW3 f1 d) sW) (hY : WithDeclsD ds (StartY3 f1 f2 d) sY)
    (hR : WithDeclsD ds (StartD3 f2 d) sR) :
    Config.FaultFree A fuel (Config.init [sW, sY, sR] initMem) := by
  refine a64_faultFree_of_addrSpecs (relay3SpecA f1 f2 d) (fun _ => ds) (fun _ => hsz)
    (fun | 0 => hag | 1 => hag | _ + 2 => hag) (init_threads_of3 ?_ ?_ ?_)
  · obtain ⟨hds, hW⟩ := hW
    refine holdsD_ofAddr (st := sW) hW.exe hds hW.endPc ?_
    unfold AddrSafeA
    rw [show sW.st = (sW.st.1, labY3 "writer") from Prod.ext rfl hW.pc]
    exact (writerW3_addr f1 f2 d _ () fun _ => ⟨hW.x0, hW.x1, hW.df, hW.dd⟩).mono
      fun _ h => h.elim And.left False.elim
  · obtain ⟨hds, hY⟩ := hY
    refine holdsD_ofAddr (st := sY) hY.exe hds hY.endPc ?_
    unfold AddrSafeA
    rw [show sY.st = (sY.st.1, labY3 "relay") from Prod.ext rfl hY.pc]
    exact (Safely.uncountA (relayY3_addr f1 f2 d _ ((), 0)
      fun _ => ⟨hY.x0, hY.x1, hY.x2, hY.df1, hY.dd, hY.df2⟩)).mono fun _ ⟨_, h⟩ => h.elim And.left False.elim
  · obtain ⟨hds, hR⟩ := hR
    refine holdsD_ofAddr (st := sR) hR.exe hds hR.endPc ?_
    unfold AddrSafeA
    rw [show sR.st = (sR.st.1, labY3 "reader") from Prod.ext rfl hR.pc]
    exact (Safely.uncountA (readerD3_addr f1 f2 d _ ((), 0)
      fun _ => ⟨hR.x0, hR.x1, hR.df, hR.dd⟩)).mono fun _ ⟨_, h⟩ => h.elim And.left False.elim

end Plain

/-- **`mp_relay3.kl` never faults**, from the runner's exact configuration
(`[writerDY0, relayDY1, readerDY2]`, initial memory `relay3InitMem`), under
any architecture. -/
theorem mp_relay3_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [writerDY0, relayDY1, readerDY2] relay3InitMem) :=
  mp_relay3_envG_runner_faultFree (layout := wLayoutY) relay3DeclsD_sized _ _ _ relay3DeclsD_agreesA
    (withDeclsD_of rfl writerW0_start) (withDeclsD_of rfl relayW1_start) (withDeclsD_of rfl readerW2_start)

section Swpl

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relaySwpl3Img)]

/-- The `swpl` image's writer address run (over its mask) at `G = ⊤`. -/
def relayWS3SpecA (f1 f2 d : BitVec 64) : ValSpecA fun _ _ => True :=
  .ofAddr (relayS f1 f2 d) (layout relaySwpl3Img) (layout relaySwpl3ImgW) (labS3 "wdone") relaySwpl3Img_noPairs
    (maskOf_layout _ _) relaySwpl3Img_rmwLive relaySwpl3Img_noFault (rootOnlyDA_of_phase1Tree relaySwpl3ImgW_phase1)

/-- The `swpl` image's relay address run (over its mask) at `G = ⊤`. -/
def relayYS3SpecA (f1 f2 d : BitVec 64) : ValSpecA fun _ _ => True :=
  .ofAddr (relayS f1 f2 d) (layout relaySwpl3Img) (layout relaySwpl3ImgY) (labS3 "rdone") relaySwpl3Img_noPairs
    (maskOf_layout _ _) relaySwpl3Img_rmwLive relaySwpl3Img_noFault
    (rootOnlyDA_of_phase1TreeR relaySwpl3ImgY_phase1R)

/-- The `swpl` image's reader address run (over its mask) at `G = ⊤`. -/
def relayDS3SpecA (f1 f2 d : BitVec 64) : ValSpecA fun _ _ => True :=
  .ofAddr (relayS f1 f2 d) (layout relaySwpl3Img) (layout relaySwpl3ImgD) (labS3 "ddone") relaySwpl3Img_noPairs
    (maskOf_layout _ _) relaySwpl3Img_rmwLive relaySwpl3Img_noFault (rootOnlyDA_of_phase1Tree relaySwpl3ImgD_phase1)

/-- The three roles' specifications by thread id. -/
def relaySwpl3SpecA (f1 f2 d : BitVec 64) : Nat → ValSpecA fun _ _ => True
  | 0 => relayWS3SpecA f1 f2 d
  | 1 => relayYS3SpecA f1 f2 d
  | _ => relayDS3SpecA f1 f2 d

/-- **No reachable configuration of the verbatim `mp_relay3_swpl.kl`
threads with the runner's declarations has a faulting step.** -/
theorem mp_relay3_swpl_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized)
    (f1 f2 d : BitVec 64) (hag : ds.AgreesOnA (relayS f1 f2 d)) {sW sY sR : isa.State}
    {initMem : List (Loc × Val)} (hW : WithDeclsD ds (StartWS3 f1 d) sW)
    (hY : WithDeclsD ds (StartYS3 f1 f2 d) sY) (hR : WithDeclsD ds (StartDS3 f2 d) sR) :
    Config.FaultFree A fuel (Config.init [sW, sY, sR] initMem) := by
  refine a64_faultFree_of_addrSpecs (relaySwpl3SpecA f1 f2 d) (fun _ => ds) (fun _ => hsz)
    (fun | 0 => hag | 1 => hag | _ + 2 => hag) (init_threads_of3 ?_ ?_ ?_)
  · obtain ⟨hds, hW⟩ := hW
    refine holdsD_ofAddr (st := sW) hW.exe hds hW.endPc ?_
    unfold AddrSafeA
    rw [show sW.st = (sW.st.1, labS3 "writer") from Prod.ext rfl hW.pc]
    exact (writerS3_addr f1 f2 d _ () fun _ => ⟨hW.x0, hW.x1, hW.df, hW.dd⟩).mono
      fun _ h => h.elim And.left False.elim
  · obtain ⟨hds, hY⟩ := hY
    refine holdsD_ofAddr (st := sY) hY.exe hds hY.endPc ?_
    unfold AddrSafeA
    rw [show sY.st = (sY.st.1, labS3 "relay") from Prod.ext rfl hY.pc]
    exact (Safely.uncountA (relaySwplY3_addr f1 f2 d _ ((), 0)
      fun _ => ⟨hY.x0, hY.x1, hY.x2, hY.df1, hY.dd, hY.df2⟩)).mono fun _ ⟨_, h⟩ => h.elim And.left False.elim
  · obtain ⟨hds, hR⟩ := hR
    refine holdsD_ofAddr (st := sR) hR.exe hds hR.endPc ?_
    unfold AddrSafeA
    rw [show sR.st = (sR.st.1, labS3 "reader") from Prod.ext rfl hR.pc]
    exact (Safely.uncountA (readerS3_addr f1 f2 d _ ((), 0)
      fun _ => ⟨hR.x0, hR.x1, hR.df, hR.dd⟩)).mono fun _ ⟨_, h⟩ => h.elim And.left False.elim

end Swpl

/-- **`mp_relay3_swpl.kl` never faults**, from the runner's exact
configuration (`[writerDS0, relayDS1, readerDS2]`, initial memory
`relaySwpl3InitMem`), under any architecture. -/
theorem mp_relay3_swpl_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [writerDS0, relayDS1, readerDS2] relaySwpl3InitMem) :=
  mp_relay3_swpl_envG_runner_faultFree (layout := wLayoutS) relaySwpl3DeclsD_sized _ _ _ relaySwpl3DeclsD_agreesA
    (withDeclsD_of rfl writerS0_start) (withDeclsD_of rfl relayS1_start) (withDeclsD_of rfl readerS2_start)

end Kraken.Promising.SLR.EnvG.Relay

/-! ## `spsc_queue.kl` -/

namespace Kraken.Promising.SLR.EnvG.SpscA

open Kraken.Promising.AArch64.EnvG Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

section Lay

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscImageA)]

/-- The producer's address run (over its mask) at `G = ⊤`. -/
def spscProdSpecA (P : SP) : ValSpecA fun _ _ => True :=
  .ofAddr (spscS P) (layout spscImageA) (layout spscImageP) (labA "pdone") spscImageA_noPairs spscImageP_mask
    spscImageA_rmwLive spscImageA_noFault (rootOnlyDA_of_phase1Tree spscImageP_phase1)

/-- The consumer's address run at `G = ⊤`. -/
def spscConsSpecA (P : SP) : ValSpecA fun _ _ => True :=
  .ofAddr (spscS P) (layout spscImageA) (layout spscImageA) (labA "cdone") spscImageA_noPairs (MaskOf.refl _)
    spscImageA_rmwLive spscImageA_noFault (rootOnlyDA_of_phase1Tree spscImageA_phase1)

/-- The two roles' specifications by thread id. -/
def spscSpecA (P : SP) : Nat → ValSpecA fun _ _ => True
  | 0 => spscProdSpecA P
  | _ => spscConsSpecA P

/-- **No reachable configuration of the verbatim `spsc_queue.kl` threads
with the runner's declarations has a faulting step**, for strict sized `ds`
agreeing on the two slots, `head` and `tail`. -/
theorem a64_spsc_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized) (P : SP)
    (hag : ds.AgreesOnA (spscS P)) {sP sC : isa.State} {initMem : List (Loc × Val)}
    (hP : WithDeclsD ds (StartPW P) sP) (hC : WithDeclsD ds (StartCW P) sC) :
    Config.FaultFree A fuel (Config.init [sP, sC] initMem) := by
  refine a64_faultFree_of_addrSpecs (spscSpecA P) (fun _ => ds) (fun _ => hsz)
    (fun | 0 => hag | _ + 1 => hag) (init_threads_of2 ?_ ?_)
  · obtain ⟨hds, he, -, hpc, hend, hfr⟩ := hP
    refine holdsD_ofAddr (st := sP) he hds hend ?_
    unfold AddrSafeA
    rw [show sP.st = (sP.st.1, labA "prod") from Prod.ext rfl hpc]
    exact (Safely.uncountA (spscProdW_addr P _ ((), 0) ⟨hfr, fun h => absurd h (by decide)⟩)).mono
      fun _ ⟨_, h⟩ => h.elim And.left False.elim
  · obtain ⟨hds, he, -, hpc, hend, hfr⟩ := hC
    refine holdsD_ofAddr (st := sC) he hds hend ?_
    unfold AddrSafeA
    rw [show sC.st = (sC.st.1, labA "cons") from Prod.ext rfl hpc]
    exact (Safely.uncountA (spscConsW_addr P _ ((), 0)
      ⟨hfr, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩)).mono
      fun _ ⟨_, h⟩ => h.elim And.left False.elim

end Lay

/-- **`spsc_queue.kl` never faults**, from the runner's exact configuration
(`[spscProdWD0, spscConsWD1]`, initial memory `spscInitMemD`), under any
architecture. -/
theorem a64_spsc_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [spscProdWD0, spscConsWD1] spscInitMemD) :=
  a64_spsc_envG_runner_faultFree (layout := wLayoutA) spscDeclsD_sized _ spscDeclsD_agreesA
    (withDeclsD_of rfl spscProdW0_start) (withDeclsD_of rfl spscConsW1_start)

end Kraken.Promising.SLR.EnvG.SpscA

#print axioms Kraken.Promising.SLR.EnvG.ConcreteCas.cas_counter_envG_runner_faultFree_concreteN
#print axioms Kraken.Promising.SLR.EnvG.ConcreteSwpl.swpl_counter_envG_runner_faultFree_concreteN
#print axioms Kraken.Promising.SLR.EnvG.ConcreteTicketD.ticket_counter_envG_runner_faultFree_concreteN
#print axioms Kraken.Promising.SLR.EnvG.ConcreteTicketD.ticket_al_counter_envG_runner_faultFree_concreteN
#print axioms Kraken.Promising.SLR.EnvG.Relay.mp_relay3_envG_runner_faultFree_concrete
#print axioms Kraken.Promising.SLR.EnvG.Relay.mp_relay3_swpl_envG_runner_faultFree_concrete
#print axioms Kraken.Promising.SLR.EnvG.SpscA.a64_spsc_envG_runner_faultFree_concrete
