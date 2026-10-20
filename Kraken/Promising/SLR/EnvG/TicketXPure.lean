/-
**Part 4: the x64 purity-and-phase
environment of a single-RMW dispenser program** (`dispPureX`), and the x64
assembly of the ticket lock (`ticket_counter_ofX`).

`dispPureX` and `TreeJ.dispX` are `TicketLock.dispPure` / `TreeJ.disp`
(the x64 ticket lock proof copied them verbatim because they sat in the AArch64-importing
`DispenserPureA64.lean`; they are now in the ISA-neutral
`EnvG/DispenserPure.lean` and made the copies these definitions). The
specification is the x64 one: as `RelPureSpecQX` (`RelPureEnvX64.lean`), the
environment is restricted to a shared layout `S` (`Le16 S`), the private
memory is split from it, and the thread may carry strict sized declarations
`ds` (`X64DeclsLink.lean`: the tree is the `decls = {}` tree re-resolved,
`exec_treeJ_of_underDecls`).

- `dispPureX A Q x N`, `TreeJ.dispX`: as `dispPure`/`TreeJ.disp`.
- `DispSpecX A Q x N`, `DispSpecX.HoldsD ds b st` (`decls = ds`, phase `b`),
  `dispSpecX_stepD` (one instruction), `DispSpecX.ofProgram`,
  `DispSpecX.holdsD_of_partialTripleEnv` (from a `vcgen` triple at
  `decls = {}`, moved to `decls = ds` by `hds`).
- Under `Arch.tso` at `Q := fun _ _ => False` (every x64 write but `movnti`
  is a release, so the `vcgen` obligations are those of `dispPure` without
  purity): `noNTInv_of_dispSpecX` (the scope `NTFree`), and every tree writes
  every location by a release (`EvTree.NoNT.relWrites`), so purity holds for
  any ghost.
- **`ticket_counter_ofX`**: `TicketLock.ticket_counter_of` for x64
  (`Arch.tso`), from a `DispSpecX` holding at every start state (with the
  thread's declarations `ds tid`, strict sized) and each thread's `NPSafeP`.
  An instance of the ISA-generic
  `TicketLock.ticket_counter_core` (`EnvG/TicketCounterCore.lean`).
-/
import Kraken.Promising.SLR.EnvG.DispenserPure
import Kraken.Promising.SLR.EnvG.TicketCounterCore
import Kraken.Promising.SLR.EnvG.TicketLockGhost
import Kraken.Promising.SLR.EnvG.TicketLockVC
import Kraken.Promising.SLR.EnvG.X64DeclsLink
import Kraken.Promising.SLR.EnvG.X64SpinPublicG
import Kraken.Promising.SLR.DispenserFresh
import Kraken.Promising.SLR.DispenserRun
import Kraken.Promising.SLR.Theorem1FinalP

namespace Kraken.Promising.X64.EnvG.TicketX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.TicketLock
open Kraken.Promising.X64.EnvG

/-! ## The environment (`TicketLock.dispPure`) -/

/-- **The purity-and-phase environment** of a single-RMW dispenser program
on `x` with bound `N`: `TicketLock.dispPure` (ISA-neutral,
`EnvG/DispenserPure.lean`). -/
abbrev dispPureX (A : Arch) (Q : Loc → Val → Prop) (x : Loc) (N : Nat) : SharedEnv :=
  dispPure A Q x N

variable {A : Arch} {Q : Loc → Val → Prop} {x : Loc} {N : Nat}

instance : (dispPureX A Q x N).Skips := inferInstanceAs (dispPure A Q x N).Skips

/-- **The tree judgment of `dispPureX`**: `TicketLock.TreeJ.disp`. -/
def TreeJ.dispX (A : Arch) (Q : Loc → Val → Prop) (x : Loc) (N : Nat) {σ : Type} (Post : σ → Bool → Prop) :
    TreeJ (dispPureX A Q x N) σ :=
  TreeJ.disp A Q x N Post

/-! ## The x64 specification -/

/-- **A thread's purity-and-phase specification, x64**: the shared layout,
code, end address, and a postcondition at the end address. -/
structure DispSpecX (A : Arch) (Q : Loc → Val → Prop) (x : Loc) (N : Nat) where
  S : SharedEnv.Layout
  le16 : Le16 S
  e : Kraken.Executable Directive
  valid : Kraken.Executable.ValidLayout e
  endPc : Int64
  post : MachineState × Bool → Prop
  post_end : ∀ y, post y → y.1.2 = endPc

/-- The specification holds at a thread state with declarations `ds`, in
phase `b`. -/
def DispSpecX.HoldsD (sp : DispSpecX A Q x N) (ds : Decls) (b : Bool) (st : State) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = ds ∧ Split sp.S st.st.1.dmem ∧
    Safely (sp.e.instrStepEnv ((dispPureX A Q x N).within sp.S)) sp.post (st.st, b)

/-- **One instruction, x64, with strict sized declarations or none**
(`dispSpec_step` for x64; `relPureSpecQX_stepD` / `relPureSpecQX_step` for
`dispPureX`). -/
theorem dispSpecX_stepD (sp : DispSpecX A Q x N) {ds : Decls} (hsz : ds.Sized ∨ ds = {}) {b : Bool} {st : State}
    (h : sp.HoldsD ds b st) (tree : EvTree State) (hex : isa.exec st = some tree) :
    (TreeJ.dispX A Q x N (fun s b => sp.HoldsD ds b s)).W tree b :=
  haveI := sp.valid
  TicketX2.treeJ_of_QX64MD (TreeJ.dispX A Q x N (fun s b => sp.HoldsD ds b s)) hsz sp.le16
    (fun _ _ h => ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩) sp.post_end ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩ tree hex

/-- The specification of a laid-out program `p` on the layout `S`: the end
of its text. -/
def DispSpecX.ofProgram [layout : _root_.Layout] (S : SharedEnv.Layout) (hS : Le16 S) (p : Program)
    [hv : Kraken.Executable.ValidLayout (layout p)] (Q' : MachineData → Bool → Prop) : DispSpecX A Q x N where
  S := S
  le16 := hS
  e := layout p
  valid := hv
  endPc := (layout p).addrOf p.length
  post y := (y.1.2 = (layout p).addrOf p.length ∧ Q' y.1.1 y.2) ∨ False
  post_end _ h := h.elim And.left False.elim

/-- **The spec from a partial triple** in `(dispPureX A Q x N).within S`, at
a thread state at the start of `p` with declarations `ds` and a split private
memory. -/
theorem DispSpecX.holdsD_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {S : SharedEnv.Layout}
    {hS : Le16 S} {p : Program} [Kraken.Executable.ValidLayout (layout p)] {P Q' : MachineData → Bool → Prop}
    {E : Int64 → MachineData → Bool → Prop}
    (ht : MachineWP.PartialTripleEnv ((dispPureX A Q x N).within S) P p Q' E)
    (henv : cenv = layout p) {ds : Decls} {st : State} (he : st.exe = layout p) (hds : st.decls = ds)
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hs : Split S st.st.1.dmem) {b : Bool} (hP : P st.st.1 b) (hE : ∀ a s g, ¬ E a s g := by simp) :
    (DispSpecX.ofProgram (A := A) (Q := Q) (x := x) (N := N) S hS p Q').HoldsD ds b st := by
  refine ⟨he, hend, hds, hs, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-! ## No non-temporal store under `Arch.tso` -/

private theorem all_monoX {σ : Type} {P P' : σ → Prop} (hP : ∀ s, P s → P' s) :
    ∀ {t : EvTree σ}, t.All P → t.All P'
  | .done s, h => hP s h
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => all_monoX hP (h i)
  | .load _ _ _ _, h => fun v => all_monoX hP (h v)
  | .store _ _ _ _ _, h => fun b => all_monoX hP (h b)
  | .rmw _ _ _ _ _, h => fun v => all_monoX hP (h v)
  | .fence _ _, h => fun u => all_monoX hP (h u)

/-- **The no-NT invariant of a dispenser program, x64, `Arch.tso`**: the
threads' all-release purity-and-phase specifications (any phase). -/
theorem noNTInv_of_dispSpecX (sp : DispSpecX Arch.tso (fun _ _ => False) x N) (ds : Nat → Decls)
    (hsz : ∀ tid, (ds tid).Sized ∨ ds tid = {}) :
    isa.NoNTInv Arch.tso (fun st => ∃ tid b, sp.HoldsD (ds tid) b st) where
  noNT st h tree hex := by
    obtain ⟨tid, b, h⟩ := h
    exact EvTree.noNT_tso_of_relWrites_false (dispSpecX_stepD sp (hsz tid) h tree hex).1
  step st h tree hex := by
    obtain ⟨tid, b, h⟩ := h
    exact all_monoX (fun _ ⟨b', h'⟩ => ⟨tid, b', h'⟩) (dispSpecX_stepD sp (hsz tid) h tree hex).2.1

/-! ## The assembly -/

/-- The parameters at addresses `x`, `o`, `c` (4-byte words; a copy of the
AArch64-importing `TicketLock.tkSys`). -/
abbrev tkSysX (N : Nat) (x o c : BitVec 64) : Sys := ⟨N, ⟨x, 4⟩, ⟨o, 4⟩, ⟨c, 4⟩⟩

/-- **The x64 ticket lock's assembly** (`TicketLock.ticket_counter_of` under
`Arch.tso`): from an all-release purity-and-phase specification `DS` holding
at every start state with the thread's strict sized declarations `ds tid`,
and each thread's `NPSafeP` at the initial configuration,
`theorem1IIPureX_G₀_S_singleRmw` and `ticket_final` give `counter = N` at
every final reachable configuration. -/
theorem ticket_counter_ofX {fuel : Nat}
    (N : Nat) (x o c : BitVec 64) (hxo : Decls.overlaps x 4 o 4 = false) (hxc : Decls.overlaps x 4 c 4 = false)
    (hoc : Decls.overlaps o 4 c 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)} (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    (DS : DispSpecX Arch.tso (fun _ _ => False) ⟨x, 4⟩ (N + 1)) (ds : Nat → Decls) (hsz : ∀ tid, (ds tid).Sized ∨ ds tid = {})
    (hDS : ∀ tid s, states[tid]? = some s → DS.HoldsD (ds tid) false s)
    (hsafe : ∀ (hL : Locs (tkSysX N x o c)) tid s, states[tid]? = some s → ∀ n m,
      NPSafeP (modelX isa (disp (tkSysX N x o c) hL.xo).TX) Arch.tso (fun cf r _ => TPost (tkSysX N x o c) cf r) tid
        G₀ (K2Scope (model isa) AllocIds) n m True (Config.init states initMem)
        (thRes (Config.init states initMem).mem (tkSysX N x o c) tid) (tkGhost (Config.init states initMem).mem
          (tkSysX N x o c)))
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N :=
  ticket_counter_core Arch.tso N x o c hxo hxc hoc hN32 hN hX0 hO0 hC0 (fun tid b s => DS.HoldsD (ds tid) b s)
    (fun _ hc' => Config.ntFree_of_noNTInv (noNTInv_of_dispSpecX DS ds hsz) (fun s hs => by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
      exact ⟨i, false, hDS i _ (List.getElem?_eq_getElem hi)⟩) hc')
    -- every write is a release: purity for any ghost
    (fun _ tid _ _ tree h hex => ⟨EvTree.NoNT.relWrites tso_storeKind_rel
      (EvTree.noNT_tso_of_relWrites_false (dispSpecX_stepD DS (hsz tid) h tree hex).1),
      (dispSpecX_stepD DS (hsz tid) h tree hex).2⟩)
    (fun _ => hDS) hsafe hc hf

end Kraken.Promising.X64.EnvG.TicketX

#print axioms Kraken.Promising.X64.EnvG.TicketX.dispSpecX_stepD
#print axioms Kraken.Promising.X64.EnvG.TicketX.noNTInv_of_dispSpecX
#print axioms Kraken.Promising.X64.EnvG.TicketX.ticket_counter_ofX
