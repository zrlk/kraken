/-
**Program-level fault freedom at the runner's declarations, x64**
. The x64 link of `MemVals.lean`.

A thread's **value specification** `ValSpecX L V` is a `Safely` judgment in
`(SharedEnv.valEnv L V).within S` (one stateless `vcgen` run, as the purity
specifications `RelPureSpecQX`): its `L`-reads return `V`-values, its
`L`-writes must write `V`-values, and every access is exactly a location of
the layout `S`. With strict sized declarations `ds` (`Decls.Sized`):

- `valSpecX_stepD`: every tree of a thread where the specification holds
  (`ValSpecX.HoldsD ds`) is `ValX L V` with leaves where it holds again
  (`relPureSpecQX_stepD` for `TreeJ.valX`, through `exec_treeJ_of_underDecls`);
- `noFault_valSpecD`: that tree is structurally fault-free, for `ds` agreeing
  on `S`, fault-free non-data cells and single-access trees
  (`noFault_QX64MD_rootD` at `E := valEnv L V`);
- **`x64_faultFree_of_valSpecs`**: one value specification per thread id and
  `MemVals L V` of the initial memory give `Config.FaultFree` (no reachable
  configuration has a faulting step, promises included) by
  `faultFree_of_valInv`.
- The alignment-tolerant forms `noFault_valSpecD_env` /
  `x64_faultFree_of_valSpecs_env` (`DirsNoFaultEnvX`, `MultiX64Align.lean`,
  moved from `MemValsX64ABA`) are the general ones; the
  `DirsNoFaultCode` forms are their instances (`DirsNoFaultCode.toEnvX`).

**Fixed layouts (`L = ∅`).** The all-release purity specifications
(`RelPureSpecQX`, the NoNT specs of the `*_runner` theorems) already sit at
their programs' layouts; at `L = ∅` the value invariant is trivial and
`ValX` is `EvTree.All` (`valX_of_all_empty`), so
**`x64_faultFree_of_relPureSpecsQXD`** gives `Config.FaultFree` from them
with no memory hypothesis.

Phase-1 limit: single-access trees (`RootOnlyD`), as in `X64NoFaultD`.
-/
import Kraken.Promising.SLR.EnvG.MemVals
import Kraken.Promising.SLR.EnvG.X64NoFaultD
import Kraken.Promising.SLR.EnvG.MultiX64Align

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvSpike

variable {L : Loc → Prop} {V : Val → Prop}

/-- **A thread's value specification, x64**: the shared layout (at most 16
bytes per location), code, end address and a postcondition at the end
address; the invariant is `Safely` in `(valEnv L V).within S`. -/
structure ValSpecX (L : Loc → Prop) (V : Val → Prop) where
  S : SharedEnv.Layout
  le16 : Le16 S
  e : Kraken.Executable Directive
  valid : Kraken.Executable.ValidLayout e
  endPc : Int64
  post : MachineState × Unit → Prop
  post_end : ∀ y, post y → y.1.2 = endPc

/-- The specification holds at a thread state with declarations `ds`: its
code, end address, declarations, a private memory split from `S`, and the
`Safely` judgment at its machine state. -/
def ValSpecX.HoldsD (sp : ValSpecX L V) (ds : Decls) (st : State) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = ds ∧ Split sp.S st.st.1.dmem ∧
    Safely (sp.e.instrStepEnv ((SharedEnv.valEnv L V).within sp.S)) sp.post (st.st, ())

/-- **One instruction, with declarations**: every tree of a thread where the
specification holds is `ValX L V`, with leaves where it holds again. -/
theorem valSpecX_stepD (sp : ValSpecX L V) {ds : Decls} (hsz : ds.Sized) {st : State}
    (h : sp.HoldsD ds st) (tree : EvTree State) (hex : isa.exec st = some tree) :
    ValX L V (sp.HoldsD ds) tree :=
  haveI := sp.valid
  TicketX2.treeJ_of_QX64MD (TreeJ.valX L V (sp.HoldsD ds)) (Or.inl hsz) sp.le16
    (fun _ _ h => ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩) sp.post_end ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩ tree hex

/-- Every fence of the value environment has an outcome. -/
theorem valEnv_fenceTotal (L : Loc → Prop) (V : Val → Prop) : (SharedEnv.valEnv L V).FenceTotal :=
  fun _ _ => ⟨(), trivial⟩

/-- The specification is the generic invariant `QX64MD` (unmasked). -/
theorem ValSpecX.qx64md (sp : ValSpecX L V) {ds : Decls} {st : State} (h : sp.HoldsD ds st) :
    QX64MD ds (SharedEnv.valEnv L V) sp.S sp.e sp.e sp.endPc sp.post st () :=
  ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩

/-- **Statically fault-free non-data cells are fault-free where an
environment runs them**: a data cell has no environment step. -/
theorem DirsNoFaultCode.toEnvX {S : SharedEnv.Layout} {e : _root_.Executable} (h : DirsNoFaultCode e) :
    DirsNoFaultEnvX S e := by
  intro d z hm
  by_cases hb : ∀ b, d ≠ .byteArray b
  · exact DirNoFault.toEnvX (h d z hm hb)
  · obtain ⟨b, rfl⟩ := Classical.not_forall_not.mp hb
    intro _ _ _ _ _ _ _ hstep
    rcases hstep with h | h <;> simp [Directive.interp, Effects.AllEnv] at h

/-- Twin of noFault_valSpecD. **The tree of a thread where the
specification holds is fault-free**, for declarations agreeing on the
layout, code fault-free where the environment runs it (`DirsNoFaultEnvX`)
and single-access trees. (Moved here from `MemValsX64ABA`; the
`DirsNoFaultCode` form `noFault_valSpecD` is its instance.) -/
theorem noFault_valSpecD_env (sp : ValSpecX L V) {ds : Decls} (hag : ds.AgreesOn sp.S)
    (hnf : DirsNoFaultEnvX sp.S sp.e)
    (hro : ∀ st : State, st.exe = sp.e → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyD)
    {st : State} (h : sp.HoldsD ds st) (tree : EvTree State) (hex : isa.exec st = some tree) : tree.NoFault := by
  haveI := sp.valid
  obtain ⟨he, hend, hds, hs, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, -⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact sp.post_end _ hp)
    rw [this] at hex; cases hex
  · rw [exec_underDecls] at hex
    obtain ⟨t₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hex
    refine (EvTree.noFault_map _ _).mpr ?_
    have hnf₀ := noFault_of_instrStepEnvX (within_fit _ _) (st := st.noDecls) he rfl hnf hR t₀ h₀
    have hin : t₀.RootInS sp.S :=
      exec_treeJLive_of_instrStepEnv (rootInJ _ sp.S (valEnv_fenceTotal L V)) (within_fit _ _) sp.le16
        (st := st.noDecls) he rfl hs hR (fun _ _ _ _ => trivial) t₀ h₀
    rw [hds]
    exact noFault_underDecls_rootD hag _ hin (hro st.noDecls he rfl _ h₀) hnf₀

/-- **The tree of a thread where the specification holds is fault-free**,
for declarations agreeing on the layout, fault-free non-data cells and
single-access trees. (`noFault_valSpecD_env` through
`DirsNoFaultCode.toEnvX`.) -/
theorem noFault_valSpecD (sp : ValSpecX L V) {ds : Decls} (hag : ds.AgreesOn sp.S) (hnf : DirsNoFaultCode sp.e)
    (hro : ∀ st : State, st.exe = sp.e → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyD)
    {st : State} (h : sp.HoldsD ds st) (tree : EvTree State) (hex : isa.exec st = some tree) : tree.NoFault :=
  noFault_valSpecD_env sp hag hnf.toEnvX hro h tree hex

/-- Twin of x64_faultFree_of_valSpecs. **Program-level fault freedom
from value specifications, x64, alignment-faulting code**:
`x64_faultFree_of_valSpecs` with `DirsNoFaultEnvX` for `DirsNoFaultCode`.
(Moved here from `MemValsX64ABA`; `x64_faultFree_of_valSpecs` is
its instance.) -/
theorem x64_faultFree_of_valSpecs_env {A : Arch} {fuel : Nat} (sp : Nat → ValSpecX L V) (ds : Nat → Decls)
    (hsz : ∀ tid, (ds tid).Sized) (hag : ∀ tid, (ds tid).AgreesOn (sp tid).S)
    (hnf : ∀ tid, DirsNoFaultEnvX (sp tid).S (sp tid).e)
    (hro : ∀ tid, ∀ st : State, st.exe = (sp tid).e → st.decls = {} → ∀ tree, isa.exec st = some tree →
      tree.RootOnlyD)
    {c₀ : Config isa} (hm : MemVals L V c₀.mem)
    (h0 : ∀ tid t, c₀.threads[tid]? = some t → (sp tid).HoldsD (ds tid) t.st) :
    Config.FaultFree A fuel c₀ :=
  faultFree_of_valInv (L := L) (V := V) (P := fun st => ∃ tid, (sp tid).HoldsD (ds tid) st)
    (fun _ tree ⟨tid, h⟩ hex => ValX.mono (fun _ h' => ⟨tid, h'⟩) (valSpecX_stepD (sp tid) (hsz tid) h tree hex))
    (fun _ tree ⟨tid, h⟩ hex => noFault_valSpecD_env (sp tid) (hag tid) (hnf tid) (hro tid) h tree hex)
    ⟨hm, fun i t ht => ⟨i, h0 i t ht⟩⟩

/-- **Program-level fault freedom from value specifications, x64.** One
value specification per thread id, holding at every initial thread with
strict sized declarations that agree on its layout, fault-free non-data
cells and single-access trees, and `MemVals L V` of the initial memory: no
configuration reachable under any architecture (promises included) has a
faulting step. (`x64_faultFree_of_valSpecs_env` through
`DirsNoFaultCode.toEnvX`.) -/
theorem x64_faultFree_of_valSpecs {A : Arch} {fuel : Nat} (sp : Nat → ValSpecX L V) (ds : Nat → Decls)
    (hsz : ∀ tid, (ds tid).Sized) (hag : ∀ tid, (ds tid).AgreesOn (sp tid).S)
    (hnf : ∀ tid, DirsNoFaultCode (sp tid).e)
    (hro : ∀ tid, ∀ st : State, st.exe = (sp tid).e → st.decls = {} → ∀ tree, isa.exec st = some tree →
      tree.RootOnlyD)
    {c₀ : Config isa} (hm : MemVals L V c₀.mem)
    (h0 : ∀ tid t, c₀.threads[tid]? = some t → (sp tid).HoldsD (ds tid) t.st) :
    Config.FaultFree A fuel c₀ :=
  x64_faultFree_of_valSpecs_env sp ds hsz hag (fun tid => (hnf tid).toEnvX) hro hm h0

/-! ## From `vcgen` triples -/

/-- The specification of a laid-out program `p` on the layout `S`: the end
of its text, and `Q` there (`RelPureSpecQX.ofProgram` for `valEnv`). -/
def ValSpecX.ofProgram [layout : _root_.Layout] (S : SharedEnv.Layout) (hS : Le16 S) (p : Program)
    [hv : Kraken.Executable.ValidLayout (layout p)] (Q' : MachineData → Unit → Prop) : ValSpecX L V where
  S := S
  le16 := hS
  e := layout p
  valid := hv
  endPc := (layout p).addrOf p.length
  post x := (x.1.2 = (layout p).addrOf p.length ∧ Q' x.1.1 x.2) ∨ False
  post_end _ h := h.elim And.left False.elim

/-- **The spec from a partial triple** in `(valEnv L V).within S`, at a
thread state at the start of `p` with declarations `ds` and a split private
memory. -/
theorem ValSpecX.holdsD_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {S : SharedEnv.Layout}
    {hS : Le16 S} {p : Program} [Kraken.Executable.ValidLayout (layout p)] {P Q' : MachineData → Unit → Prop}
    {E : Int64 → MachineData → Unit → Prop} {ds : Decls}
    (ht : MachineWP.PartialTripleEnv ((SharedEnv.valEnv L V).within S) P p Q' E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = ds)
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hs : Split S st.st.1.dmem) (hP : P st.st.1 ()) (hE : ∀ a s g, ¬ E a s g := by simp) :
    (ValSpecX.ofProgram (L := L) (V := V) S hS p Q').HoldsD ds st := by
  refine ⟨he, hend, hds, hs, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-! ## Fixed layouts: the purity specifications at `L = ∅` -/

variable {A : Arch} {Q : Loc → Val → Prop}

/-- Every fence of the purity environment has an outcome. -/
theorem relPureQ_fenceTotal (A : Arch) (Q : Loc → Val → Prop) : (SharedEnv.relPureQ A Q).FenceTotal :=
  fun _ _ => ⟨(), trivial⟩

/-- **The tree of a thread where a purity specification holds is
fault-free** at declarations agreeing on its layout (`noFault_valSpecD` for
`RelPureSpecQX`). -/
theorem noFault_relPureSpecQXD (sp : RelPureSpecQX A Q) {ds : Decls} (hag : ds.AgreesOn sp.S)
    (hnf : DirsNoFaultCode sp.e)
    (hro : ∀ st : State, st.exe = sp.e → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyD)
    {st : State} (h : sp.HoldsD ds st) (tree : EvTree State) (hex : isa.exec st = some tree) : tree.NoFault :=
  haveI := sp.valid
  noFault_QX64MD_rootD hag (relPureQ_fenceTotal A Q) (MaskOf.refl _) sp.le16 hnf sp.post_end hro st () tree
    ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩ hex

/-- **Program-level fault freedom from purity specifications, given their
trees' no-fault** (fixed layouts, `L = ∅`): one specification per thread id
at strict sized declarations, each of whose trees is fault-free; no
hypothesis on the memory. -/
theorem x64_faultFree_of_relPureSpecsQXD' {fuel : Nat} {A' : Arch} (sp : Nat → RelPureSpecQX A Q)
    (ds : Nat → Decls) (hsz : ∀ tid, (ds tid).Sized)
    (hnf : ∀ tid st tree, (sp tid).HoldsD (ds tid) st → isa.exec st = some tree → tree.NoFault)
    {c₀ : Config isa} (h0 : ∀ tid t, c₀.threads[tid]? = some t → (sp tid).HoldsD (ds tid) t.st) :
    Config.FaultFree A' fuel c₀ :=
  faultFree_of_valInv (L := fun _ => False) (V := fun _ => True)
    (P := fun st => ∃ tid, (sp tid).HoldsD (ds tid) st)
    (fun _ tree ⟨tid, h⟩ hex => ValX.mono (fun _ h' => ⟨tid, h'⟩)
      (valX_of_all_empty _ (relPureSpecQX_stepD (sp tid) (hsz tid) h tree hex).2))
    (fun _ tree ⟨tid, h⟩ hex => hnf tid _ tree h hex)
    ⟨memVals_empty _ _, fun i t ht => ⟨i, h0 i t ht⟩⟩

/-- **Program-level fault freedom from purity specifications** (fixed
layouts, `L = ∅`): one specification per thread id at strict sized
declarations agreeing on its layout, fault-free non-data cells and
single-access trees; no hypothesis on the memory. -/
theorem x64_faultFree_of_relPureSpecsQXD {fuel : Nat} {A' : Arch} (sp : Nat → RelPureSpecQX A Q)
    (ds : Nat → Decls) (hsz : ∀ tid, (ds tid).Sized) (hag : ∀ tid, (ds tid).AgreesOn (sp tid).S)
    (hnf : ∀ tid, DirsNoFaultCode (sp tid).e)
    (hro : ∀ tid, ∀ st : State, st.exe = (sp tid).e → st.decls = {} → ∀ tree, isa.exec st = some tree →
      tree.RootOnlyD)
    {c₀ : Config isa} (h0 : ∀ tid t, c₀.threads[tid]? = some t → (sp tid).HoldsD (ds tid) t.st) :
    Config.FaultFree A' fuel c₀ :=
  x64_faultFree_of_relPureSpecsQXD' sp ds hsz
    (fun tid _ tree h hex => noFault_relPureSpecQXD (sp tid) (hag tid) (hnf tid) (hro tid) h tree hex) h0

/-- The threads of `Config.init states initMem` are the start states: a
per-state hypothesis gives the per-thread one. -/
theorem init_threads_of {P : Nat → State → Prop} {states : List isa.State} {initMem : List (Loc × Val)}
    (h0 : ∀ tid s, states[tid]? = some s → P tid s) :
    ∀ tid t, (Config.init states initMem).threads[tid]? = some t → P tid t.st := by
  intro tid t ht
  obtain ⟨s, hs, rfl⟩ := Config.init_get?_thread ht
  exact h0 tid s hs

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.X64.EnvG.x64_faultFree_of_valSpecs
#print axioms Kraken.Promising.X64.EnvG.x64_faultFree_of_relPureSpecsQXD
