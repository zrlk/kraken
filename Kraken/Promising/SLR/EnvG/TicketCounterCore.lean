/-
**The ticket lock's assembly, ISA- and architecture-generic**.

`ticket_counter_core` is the shared body of the three ticket-lock
assemblies, which are now its instances (same names and statements):
- `TicketLock.ticket_counter_of` (AArch64, `DispSpec.Holds`, `decls = {}`);
- `TicketLock.ticket_counter_ofD` (AArch64, `DispSpec.HoldsD`, strict sized
  declarations, `EnvG/A64TicketRunner.lean`);
- `TicketX.ticket_counter_ofX` (x64, `Arch.tso`, `DispSpecX.HoldsD`,
  `EnvG/TicketXPure.lean`).

From a phase-indexed per-thread cell predicate `H tid b` that every
instruction keeps (`TreeJ.disp` at the purity predicate of `tkGhost`),
holding in phase `false` at every start state, the architecture's `NTFree`
invariant and each thread's `NPSafeP` at the initial configuration,
`promisePure_of_relWrites`, `SingleRmwDispenser.ofCells`,
`theorem1IIPureX_G₀_S_singleRmw` and `ticket_final` give `counter = N` at
every final reachable configuration.

`tkSys` moved here from `EnvG/TicketLockPublic.lean` (same name). New:
`tkGhost_pure_x`, `tkGhost_pure_c` (the purity predicate of `tkGhost` is
trivial at `next` and `counter`).
-/
import Kraken.Promising.SLR.EnvG.DispenserPure
import Kraken.Promising.SLR.EnvG.TicketLockGhost
import Kraken.Promising.SLR.Theorem1FinalP

namespace Kraken.Promising.SLR.EnvG.TicketLock

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- The parameters at addresses `x`, `o`, `c` (4-byte words). -/
abbrev tkSys (N : Nat) (x o c : BitVec 64) : Sys := ⟨N, ⟨x, 4⟩, ⟨o, 4⟩, ⟨c, 4⟩⟩

/-- The purity predicate of `tkGhost` is trivial at `next` (only `owner`
carries a relation). -/
theorem tkGhost_pure_x {N : Nat} {x o c : BitVec 64} (hL : Locs (tkSys N x o c)) (m : Memory) (v : Val) :
    Pred.Pure ((tkGhost m (tkSys N x o c)).rel ⟨x, 4⟩) v := by
  show Pred.Pure ((tkGhost m (tkSys N x o c)).rel (tkSys N x o c).X) v
  rw [tkGhost_rel_ne hL.xo]; exact Pred.emp_pure v

/-- The purity predicate of `tkGhost` is trivial at `counter`. -/
theorem tkGhost_pure_c {N : Nat} {x o c : BitVec 64} (hL : Locs (tkSys N x o c)) (m : Memory) (v : Val) :
    Pred.Pure ((tkGhost m (tkSys N x o c)).rel ⟨c, 4⟩) v := by
  show Pred.Pure ((tkGhost m (tkSys N x o c)).rel (tkSys N x o c).C) v
  rw [tkGhost_rel_ne (Ne.symm hL.oc)]; exact Pred.emp_pure v

variable {I : ISA} [I.LawfulState]

/-- **The ticket lock's assembly, generic** (see the module docstring): from
cells `H tid b` (phase `b`) kept by every instruction under `TreeJ.disp` at
the purity predicate of `tkGhost`, holding in phase `false` at every start
state, the `NTFree` invariant `hNT` and each thread's `NPSafeP`,
`counter = N` at every final reachable configuration. -/
theorem ticket_counter_core (A : Arch) {fuel : Nat}
    (N : Nat) (x o c : BitVec 64) (hxo : Decls.overlaps x 4 o 4 = false) (hxc : Decls.overlaps x 4 c 4 = false)
    (hoc : Decls.overlaps o 4 c 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List I.State} {initMem : List (Loc × Val)} (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    (H : Nat → Bool → I.State → Prop)
    (hNT : ∀ cf, Reachable A fuel (Config.init states initMem) cf → cf.NTFree A)
    (hstep : ∀ (_ : Locs (tkSys N x o c)) tid b st tree, H tid b st → I.exec st = some tree →
      (TreeJ.disp A (fun l v => Pred.Pure ((tkGhost (Config.init states initMem).mem (tkSys N x o c)).rel l) v)
        ⟨x, 4⟩ (N + 1) (fun s b => H tid b s)).W tree b)
    (h0 : ∀ (_ : Locs (tkSys N x o c)) tid s, states[tid]? = some s → H tid false s)
    (hsafe : ∀ (hL : Locs (tkSys N x o c)) tid s, states[tid]? = some s → ∀ n m,
      NPSafeP (modelX I (disp (tkSys N x o c) hL.xo).TX) A (fun cf r _ => TPost (tkSys N x o c) cf r) tid
        G₀ (K2Scope (model I) AllocIds) n m True (Config.init states initMem)
        (thRes (Config.init states initMem).mem (tkSys N x o c) tid) (tkGhost (Config.init states initMem).mem
          (tkSys N x o c)))
    {cfg : Config I} (hc : Reachable A fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N := by
  have hxo' : x ≠ o := by rintro rfl; simp [Decls.overlaps] at hxo
  have hxc' : x ≠ c := by rintro rfl; simp [Decls.overlaps] at hxc
  have hoc' : o ≠ c := by rintro rfl; simp [Decls.overlaps] at hoc
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · obtain rfl : states = [] := List.length_eq_zero_iff.mp hN
    obtain rfl : cfg = Config.init [] initMem := Reachable.eq_of_init_nil hc
    simpa [Memory.finalVal, Config.init] using hC0
  have hL : Locs (tkSys N x o c) :=
    ⟨fun h => hxo' (congrArg Loc.addr h), fun h => hxc' (congrArg Loc.addr h), fun h => hoc' (congrArg Loc.addr h),
      rfl, rfl, rfl, hN0, hN32⟩
  -- purity and the dispenser phases
  let m := (Config.init states initMem).mem
  let J : Nat → I.State → Prop := fun tid st => ∃ b, H tid b st
  have hJ : ∀ tid st tree, J tid st → I.exec st = some tree →
      tree.RelWrites A (fun l v => Pred.Pure ((tkGhost m (tkSys N x o c)).rel l) v) ∧ tree.All (J tid) :=
    fun tid st tree ⟨_, h⟩ hex => ⟨(hstep hL tid _ st tree h hex).1, (hstep hL tid _ st tree h hex).2.1⟩
  have hJ0 : ∀ tid s, states[tid]? = some s → J tid s := fun tid s hs => ⟨false, h0 hL tid s hs⟩
  have hpure : PromisePure A fuel states initMem (tkGhost m (tkSys N x o c)).rel :=
    promisePure_of_relWrites (fun st => ∃ tid, J tid st)
      (fun _ hc' tid t ht => ⟨tid, relWrites_reach J hJ hJ0 hc' tid t ht⟩)
      (fun st tree ⟨tid, hJt⟩ hex => (hJ tid st tree hJt hex).1)
  have hS : SingleRmwDispenser A fuel (disp (tkSys N x o c) hL.xo).x (disp (tkSys N x o c) hL.xo).N
      states initMem (fun tid => H tid false) (fun tid => H tid true) :=
    SingleRmwDispenser.ofCells J (fun _ hc' tid t ht => relWrites_reach J hJ hJ0 hc' tid t ht) (h0 hL)
      (fun tid st tree _ hb hex => (hstep hL tid _ st tree hb hex).2.2.1 rfl)
      (fun tid st tree _ ha hex => (hstep hL tid _ st tree ha hex).2.2.2 rfl)
  -- theorem 1 and the final argument
  obtain ⟨v, rF', g', hv, E', hX', hle, hB⟩ :=
    theorem1IIPureX_G₀_S_singleRmw A fuel (disp (tkSys N x o c) hL.xo)
      (fun cf r _ => TPost (tkSys N x o c) cf r) states initMem (thRes m (tkSys N x o c))
      (tkGhost m (tkSys N x o c)) hNT (erase_tkInit _ hL hN rfl hC0 hO0)
      (tx_tkInit hL hN hX0) (fun _ h => by simp [tkGhost] at h) (promisePure_iff_G₀.mp hpure) hS hX0
      (by rw [hN]; exact Nat.le_succ N)
      (fun tid htid n m' => by
        obtain ⟨s, hs⟩ : ∃ s, states[tid]? = some s := ⟨_, List.getElem?_eq_getElem htid⟩
        exact hsafe hL tid s hs n m')
      cfg hc ⟨cfg, .refl cfg, hf⟩
  obtain rfl : v = cfg := Config.VirtualOfG.eq_of_final hf hv
  have hsize : v.threads.size = N := by rw [Reachable.size_eq hc, Config.init_size, hN]
  exact ticket_final hL E' hf hsize hle hX' fun i hi => hB i (Config.final_done hf (by rw [hsize]; exact hi))

end Kraken.Promising.SLR.EnvG.TicketLock

#print axioms Kraken.Promising.SLR.EnvG.TicketLock.ticket_counter_core
