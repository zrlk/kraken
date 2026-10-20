/-
The x64 value bridge with value-restricted purity: the x64 twin of
`Lower/KitValsPure.lean`. ISA: x64 (`isa`); machine: the executable
Promising machine (`Reachable Arch.tso`), through Theorem 1′ for `NPSafeF`
over `Erase ∧ MemInv G` (`Vals.final_of_chainVP`, `SLR/PromisePureVals.lean`).

The existing x64 bridge `Vals.envGValsBridgeX_ofSpecs` (`SLR/EnvG/ValsX64.lean`)
takes unrestricted purity specifications (`RelPureSpecQX.Holds`, judgments in
`(relPureQ Arch.tso ⊥).within S`). These are false for a program that loads
through a pointer read from shared memory when its private memory is mapped
(a call stack in `dmem`): the load is a shared access only for the pointer
values the program's value invariant `G` allows, and `within S` asks it to
be a location of `S` for every answer. Here the purity specifications are
judgments in `relInvX S G` (`RelPureSpecQX.HoldsV`, `SLR/EnvG/X64EnvRefine.lean`):
`inv S G`'s and `relPureQ Arch.tso ⊥`'s permissions, load and RMW answers in
`G`. One such judgment per thread is at once the thread's purity
specification on the `G`-branches and its value specification.

- `AccessFree.relWritesV_true`, `AccessFree.noNT`: an access-free tree
  writes nothing.
- `TreeJ.relInvV`: the tree judgment of `relInvX S G`: `AllInv G` and, for a
  phase-1 tree (`Phase1ShapeF`), `RelWritesV` at any write condition and no
  non-temporal store. The phase-1 shape matters because the judgment says
  nothing about the branches with non-`G` answers: in a phase-1 tree those
  continue with no access.
- `relPureSpecQX_stepV`: one instruction of a `HoldsV` state of phase-1 code.
- **`final_of_relPureSafelyQX_tsoFVP`**: `final_of_relPureSafelyQX_tsoFV`
  with the purity specifications in `relInvX S G`, which also serve as the
  value specifications (`J := HoldsV`).
- **`envGValsBridgeX_ofPure`**: `Vals.envGValsBridgeX_ofSpecs` with the
  purity specifications in `relInvX S G` and no separate value specifications.

Phase-1 limits apply (`Phase1TreeFX` of every purity specification's image,
as of the threads' images for `NPSafeF`).
-/
import Kraken.Promising.SLR.EnvG.ValsX64
import Kraken.Promising.SLR.PromisePureVals
import Kraken.Promising.Lower.PilotX64Bridge

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

/-- An access-free tree writes nothing: `RelWritesV` holds at any write and
value condition (leaves unconstrained). -/
theorem AccessFree.relWritesV_true {σ : Type} {A : Arch} {Q G : Loc → Val → Prop} :
    ∀ {t : EvTree σ}, AccessFree t → t.RelWritesV A Q G (fun _ => True)
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => AccessFree.relWritesV_true (h i)
  | .fence _ ret, h => fun ⟨⟩ => AccessFree.relWritesV_true (t := ret ()) h
  | .load .., h => h.elim
  | .store .., h => h.elim
  | .rmw .., h => h.elim

/-- An access-free tree makes no non-temporal store. -/
theorem AccessFree.noNT {σ : Type} {A : Arch} : ∀ {t : EvTree σ}, AccessFree t → t.NoNT A
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => AccessFree.noNT (h i)
  | .fence _ ret, h => AccessFree.noNT (t := ret ()) h
  | .load .., h => h.elim
  | .store .., h => h.elim
  | .rmw .., h => h.elim

end Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.X64.EnvG.Vals

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvSpike
open Kraken.Promising.SLR.EnvG.Vals Kraken.Promising.X64.EnvG
open Kraken.Promising.Lower.PilotX (relInvX)

/-- `relInvX S G` fits its layout (its permissions include `inv S G`'s). -/
theorem relInvX_fit (S : SharedEnv.Layout) (G : Loc → Val → Prop) : X64Fit S (relInvX S G) :=
  ⟨fun h => h.1, fun h => h.1.1⟩

/-- `relInvX S G` permits every fence and has a trivial state: its fence
order is the total relation (for the call rule's straight segments). -/
instance relInvX_fenceMonoX (S : SharedEnv.Layout) (G : Loc → Val → Prop) : (relInvX S G).FenceMonoX :=
  ⟨fun _ _ => True, fun _ => trivial, fun _ _ _ _ => ⟨⟨trivial, trivial⟩, fun _ _ => trivial⟩⟩

/-- **The tree judgment of `relInvX S G`**: every write keeps `G` and every
leaf on a `G`-branch satisfies `R` (`AllInv G R`); a phase-1 tree moreover
writes only by releases on the `G`-branches (`RelWritesV` at any `Q`) and
makes no non-temporal store (under `Arch.tso`). -/
def TreeJ.relInvV (S : SharedEnv.Layout) (G Q : Loc → Val → Prop) {σ : Type} (R : σ → Prop) :
    TreeJ (relInvX S G) σ where
  W t _ := t.AllInv G R ∧ (Phase1ShapeF t → t.RelWritesV Arch.tso Q G (fun _ => True) ∧ t.NoNT Arch.tso)
  Post s _ := R s
  done h := ⟨h, fun _ => ⟨trivial, trivial⟩⟩
  fault := ⟨trivial, fun _ => ⟨trivial, trivial⟩⟩
  choose h := ⟨fun i => (h i).1, fun hs => ⟨fun i => (hs.1 i).relWritesV_true, fun i => (hs.1 i).noNT⟩⟩
  load _ h := ⟨fun v hv => (h v () hv).1, fun hs => ⟨fun v _ => (hs.2.2 v).relWritesV_true, fun v => (hs.2.2 v).noNT⟩⟩
  store hok h := ⟨⟨hok.1.2, fun b _ => (h b () trivial).1⟩, fun hs =>
    ⟨⟨fun hk => (hok.2 hk).elim, fun b => (hs.2.2 b).relWritesV_true⟩,
      ⟨fun hk => hok.2 (by rw [hk]; decide), fun b => (hs.2.2 b).noNT⟩⟩⟩
  rmw hok h := ⟨fun old hold => ⟨hok.1.2 old hold, (h old () hold).1⟩, fun hs =>
    ⟨⟨fun hk old new hon => (hok.2 hk old new hon).elim, fun v => (hs.2.2 v).relWritesV_true⟩,
      ⟨by rename_i k _ _ _ _ _ _; cases k <;> decide, fun v => (hs.2.2 v).noNT⟩⟩⟩
  fence _ h := ⟨fun ⟨⟩ => (h () trivial).1, fun hs =>
    ⟨fun ⟨⟩ => ((h () trivial).2 hs).1, ((h () trivial).2 hs).2⟩⟩

/-- **One instruction of a `HoldsV` state of phase-1 code**: the tree keeps
`HoldsV` on the `G`-branches with every write in `G` (`AllInv`), makes no
non-temporal store, and writes only by releases on the `G`-branches. -/
theorem relPureSpecQX_stepV {G : Loc → Val → Prop} (sp : RelPureSpecQX Arch.tso fun _ _ => False)
    (hshape : Phase1TreeFX sp.e) {st : State} (h : sp.HoldsV G st) (tree : EvTree State)
    (hex : isa.exec st = some tree) (Q : Loc → Val → Prop) :
    tree.AllInv G (sp.HoldsV G) ∧ tree.NoNT Arch.tso ∧ tree.RelWritesV Arch.tso Q G (fun _ => True) := by
  obtain ⟨he, hend, hds, hs, hsafe⟩ := h
  have hv := sp.valid
  rcases hsafe.unfold with hP | ⟨R, hT, hR⟩
  · have hpc : st.st.2 = sp.endPc := sp.post_end _ hP
    have hnone : isa.exec st = none := by
      show exec st = none
      simp [exec, hpc, hend]
    rw [hnone] at hex
    cases hex
  · have H := exec_treeJ_of_instrStepEnv (TreeJ.relInvV sp.S G Q (sp.HoldsV G)) (relInvX_fit sp.S G) sp.le16
      he hds hs hT (fun m g' hm hs' => by cases g'; exact ⟨he, hend, hds, hs', hR _ hm⟩) tree hex
    have hsh := hshape st he hds tree hex
    exact ⟨H.1, (H.2 hsh).2, (H.2 hsh).1⟩

/-- **`final_of_relPureSafelyQX_tsoFV` with value-restricted purity**: the
purity specifications' judgments in `relInvX (sp tid).S G` (`HoldsV`) of
phase-1 code; they are also the value specifications. `NTFree` and
`PromisePure` hold along the run because every reachable memory satisfies
`MemInv G` (`Vals.final_of_chainVP`). -/
theorem final_of_relPureSafelyQX_tsoFVP {fuel : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    (G : Loc → Val → Prop) (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem))
    (hpend : ∀ ts, ts ∉ g₀.pend) (hm0 : MemInv G (Config.init states initMem).mem)
    (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (hshape : ∀ tid, Phase1TreeFX (sp tid).e)
    (h0 : ∀ tid s, states[tid]? = some s → (sp tid).HoldsV G s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeF (modelX isa (MemInvX G)) Arch.tso B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  refine final_of_chainVP (I := isa) G (fun tid (st : isa.State) => (sp tid).HoldsV G st) ?_
    hE hpend hm0 h0 hsafe hc hf hfin
  intro tid _ tree h hex
  have H := relPureSpecQX_stepV (sp tid) (hshape tid) h tree hex fun l v => Pred.Pure (g₀.rel l) v
  exact ⟨H.1, H.2.1, _, H.2.2⟩

/-- **The x64 bridge with value-restricted purity**: `envGValsBridgeX_ofSpecs`
with the purity specifications in `relInvX (sp tid).S G` (`HoldsV`, of
phase-1 code), which also serve as the value specifications, and `MemInv G`
of the initial memory. The per-thread premise `hthr` is unchanged. -/
theorem envGValsBridgeX_ofPure {S : SharedEnv.Layout} (hS : Le16 S) (G : Loc → Val → Prop)
    {fuel : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    {pl : Nat → SLR.EnvG.Plan} {e : Nat → Kraken.Executable Directive} {endPc : Nat → Int64}
    {post : Nat → MachineState × EStateX → Prop}
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (hshape : ∀ tid, Phase1TreeFX (sp tid).e)
    (h0 : ∀ tid s, states[tid]? = some s → (sp tid).HoldsV G s)
    (hm0 : MemInv G (Config.init states initMem).mem)
    (hthr : ∀ tid, tid < states.length →
      Kraken.Executable.ValidLayout (e tid) ∧ (pl tid).Valid ∧ Phase1TreeFX (e tid) ∧
      (∀ y, post tid y → y.1.2 = endPc tid) ∧
      (∀ x R, x.1.2 = endPc tid → ¬ (e tid).instrStepEnv (EnvGCAdjXV Arch.tso tid (pl tid) S G) x R) ∧
      (∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post tid (t.st.st, σ) → t.prom = [] →
        EnvRel tid (pl tid) σ c t r g cl → cl → B c r g) ∧
      ∃ s, states[tid]? = some s ∧
        QX64CAdjV Arch.tso tid (pl tid) S G (e tid) (endPc tid) (post tid) s
          (σInitX (Config.init states initMem) (rF tid) g₀))
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  refine final_of_relPureSafelyQX_tsoFVP G hE hpend hm0 sp hshape h0 ?_ hc hf hfin
  intro tid htid n m
  obtain ⟨hv, hpl, hsh, hpost, hstuck, hB, s, hs, hQ⟩ := hthr tid htid
  exact npSafeFV_of_safelyEnvGFCAdjXV (e := e tid) hpl hS hsh hpost hstuck hB
    (fun st tree h hex => (relPureSpecQX_stepV (sp tid) (hshape tid) h tree hex fun _ _ => False).1) n m
    (invGFCAdjXV_init hs (List.eq_nil_iff_forall_not_mem.mpr hpend) hQ)
    ⟨Thread.init s, by simp [Config.init, hs], h0 tid s hs⟩

end Kraken.Promising.X64.EnvG.Vals

#print axioms Kraken.Promising.X64.EnvG.Vals.relPureSpecQX_stepV
#print axioms Kraken.Promising.X64.EnvG.Vals.final_of_relPureSafelyQX_tsoFVP
#print axioms Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofPure
