/-
**Program-level fault freedom at the runner's declarations, AArch64**
. The AArch64 link of `MemVals.lean`, the analogue of
`MemValsX64.lean`.

A thread's **value specification** `ValSpecA G` is a `QA64MD` judgment over
the invariant environment `SharedEnv.inv S G` (one `vcgen` run, as
`A64NoFaultD`'s address runs, which are the case `G = ⊤`): every access is
exactly a location of the layout `S`, its reads return `G`-values and its
writes must write `G`-values. For `G l v ↔ (L l → V v)` and strict sized
declarations `ds`:

- `valXJA`: `ValXA L V` (`MemValsA64Core`) as a live tree judgment of
  `inv S G`; `rootInJG`: "root accesses in `S`" for any `G` (`rootInJA`);
- `valSpecA_stepD`: every tree of a thread where the specification holds
  (`ValSpecA.HoldsD ds`) is `ValXA L V` with leaves where it holds again
  (`QA64MD.link` at `valXJA`);
- `noFault_QA64MD_invD`, `noFault_valSpecAD`: that tree is fault-free for
  `ds` agreeing on `S` (`noFault_QA64MAD_rootD` with the root judgment read
  off the specification's own run, so the addresses may depend on values);
- **`a64_faultFree_of_valSpecs`**: one value specification per thread id and
  `MemVals L V` of the initial memory give `Config.FaultFree` under any
  architecture, promises included (`faultFree_of_valInvA`).

**Fixed layouts (`L = ∅`).** At `G = ⊤` the value invariant is trivial and a
specification is exactly an `AddrSafeA` address run (`ValSpecA.ofAddr`,
`holdsD_ofAddr`): **`a64_faultFree_of_addrSpecs`** needs no
memory hypothesis, so the AArch64 no-fault-at-declarations proofs' address runs
give program-level fault
freedom directly (`A64FaultFreeFixed`).

Why `ValXA` and not `ValX`: `inv S G` answers a non-exclusive store with
success only, as the machine does (`MemValsA64Core`'s header).

Phase-1 limit: single-access trees (`RootOnlyDA`), as `A64NoFaultD`.
-/
import Kraken.Promising.SLR.EnvG.MemValsA64Core
import Kraken.Promising.SLR.EnvG.A64NoFaultD

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {σ : Type}

/-- **`ValXA` as a live tree judgment of `inv S G`**, for `G` the value
condition of `L` and `V`: `ok` gives the write conditions, `step` the read
conditions and the store answers. -/
def valXJA (S : SharedEnv.Layout) {G : Loc → Val → Prop} {L : Loc → Prop} {V : Val → Prop}
    (hG : ∀ l v, G l v ↔ (L l → V v)) (P : σ → Prop) : TreeJLive (SharedEnv.inv S G) σ where
  W t _ := ValXA L V P t
  Post s _ := P s
  done h := h
  fault := trivial
  choose h := fun i => h i
  load _ h₂ := fun v hv => h₂ v () ((hG _ v).2 hv)
  store h₁ h₂ := ⟨(hG _ _).1 h₁.2, fun b hb => h₂ b () hb⟩
  rmw h₁ h₂ := fun old ho =>
    ⟨fun new hn => (hG _ _).1 (h₁.2 old ((hG _ _).2 ho) new hn), h₂ old () ((hG _ _).2 ho)⟩
  fence _ h₂ := fun _ => h₂ () trivial

/-- **"Root accesses in `S`"**, the live judgment of `inv S G` for any `G`
(`rootInJA` is `G = ⊤`). -/
def rootInJG (S : SharedEnv.Layout) (G : Loc → Val → Prop) : TreeJLive (SharedEnv.inv S G) σ where
  W t _ := t.RootInSA S
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose h := fun i => h i
  load h₁ _ := h₁
  store h₁ _ := h₁.1
  rmw h₁ _ := h₁.1
  fence _ h₂ := h₂ () trivial

end Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## No fault from a run in `inv S G` -/

/-- **Every tree from a `QA64MD`-state over `inv S G` is fault-free**, for
declarations agreeing on `S`, a fault-free image and a single-access mask
(`noFault_QA64MAD_rootD`, the root accesses read off the state's own run:
any `G`, so the addresses may depend on the values read). -/
theorem noFault_QA64MD_invD {ds : Decls} {S : SharedEnv.Layout} {G : Loc → Val → Prop}
    {e e' : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {endPc : Int64}
    {post : MachineState × (SharedEnv.inv S G).State → Prop} (hag : ds.AgreesOnA S)
    (hnp : Kraken.Executable.noPairs e = true) (hm : MaskOf e e') (hlive : e.rmwLive = true) (hnf : DirsNoFault e)
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hro : ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyDA) :
    ∀ st σ tree, QA64MD ds (SharedEnv.inv S G) e e' endPc post st σ → isa.exec st = some tree →
      tree.NoFault := by
  intro st σ tree h hex
  have hQ := h.noDecls
  obtain ⟨he, hds, hend, hsafe⟩ := h
  subst hds he
  rw [exec_reresolve st hnp] at hex
  obtain ⟨t₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hex
  refine (EvTree.noFault_map _ _).mpr ?_
  have hnf₀ : t₀.NoFault := noFault_QA64M hm hnf hpost st.noDecls σ t₀ hQ h₀
  have hin : t₀.RootInSA S := by
    rcases hsafe.unfold with hp | ⟨R, hR, -⟩
    · rw [exec_eq_none_of_end (st := st.noDecls) ((hpost _ hp).trans hend.symm)] at h₀; cases h₀
    · exact exec_treeJLive_of_instrStepEnv' (rootInJG S G) (st := st.noDecls) rfl rfl
        (instrStepEnv_of_mask hm hR).1 (fun _ _ _ => trivial) hlive t₀ h₀
  obtain ⟨tree', hex', rfl⟩ := QA64M.tree hm hpost hQ h₀
  exact noFault_reresolve_rootD hag _ hin (rootOnlyDA_map _ _ (hro _ rfl rfl _ hex')) hnf₀

/-! ## Value specifications -/

/-- **A thread's value specification, AArch64**: the layout, the image `e`
and its mask `e'`, the end address and a postcondition there, and the static
facts of the image the link needs (no pairs, live RMWs, fault-free cells,
single-access mask trees). The invariant is `QA64MD` over `inv S G`. -/
structure ValSpecA (G : Loc → Val → Prop) where
  S : SharedEnv.Layout
  e : Kraken.Executable Directive
  e' : Kraken.Executable Directive
  valid : Kraken.Executable.ValidLayout e
  endPc : Int64
  post : MachineState × Unit → Prop
  post_end : ∀ y, post y → y.1.2 = endPc
  noPairs : Kraken.Executable.noPairs e = true
  mask : MaskOf e e'
  rmwLive : e.rmwLive = true
  noFault : DirsNoFault e
  rootOnly : ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyDA

variable {G : Loc → Val → Prop} {L : Loc → Prop} {V : Val → Prop}

/-- The specification holds at a thread state with declarations `ds`. -/
def ValSpecA.HoldsD (sp : ValSpecA G) (ds : Decls) (st : State) : Prop :=
  QA64MD ds (SharedEnv.inv sp.S G) sp.e sp.e' sp.endPc sp.post st ()

/-- **One instruction, with declarations**: every tree of a thread where the
specification holds is `ValXA L V`, with leaves where it holds again. -/
theorem valSpecA_stepD (hG : ∀ l v, G l v ↔ (L l → V v)) (sp : ValSpecA G) {ds : Decls} (hsz : ds.StrictSized)
    {st : State} (h : sp.HoldsD ds st) (tree : EvTree State) (hex : isa.exec st = some tree) :
    ValXA L V (sp.HoldsD ds) tree :=
  haveI := sp.valid
  QA64MD.link hsz sp.noPairs sp.mask sp.rmwLive sp.post_end (valXJA (σ := State) sp.S hG (sp.HoldsD ds)) h hex
    fun _ _ h' => h'

/-- **The tree of a thread where the specification holds is fault-free**,
for declarations agreeing on its layout. -/
theorem noFault_valSpecAD (sp : ValSpecA G) {ds : Decls} (hag : ds.AgreesOnA sp.S) {st : State}
    (h : sp.HoldsD ds st) (tree : EvTree State) (hex : isa.exec st = some tree) : tree.NoFault :=
  haveI := sp.valid
  noFault_QA64MD_invD hag sp.noPairs sp.mask sp.rmwLive sp.noFault sp.post_end sp.rootOnly st () tree h hex

/-- **Program-level fault freedom from value specifications, AArch64.** One
value specification per thread id (all over the same value condition `G`
of `L` and `V`), holding at every initial thread with strict sized
declarations agreeing on its layout, and `MemVals L V` of the initial
memory: no configuration reachable under any architecture (promises
included) has a faulting step. -/
theorem a64_faultFree_of_valSpecs (hG : ∀ l v, G l v ↔ (L l → V v)) {A : Arch} {fuel : Nat}
    (sp : Nat → ValSpecA G) (ds : Nat → Decls) (hsz : ∀ tid, (ds tid).StrictSized)
    (hag : ∀ tid, (ds tid).AgreesOnA (sp tid).S) {c₀ : Config isa} (hm : MemVals L V c₀.mem)
    (h0 : ∀ tid t, c₀.threads[tid]? = some t → (sp tid).HoldsD (ds tid) t.st) :
    Config.FaultFree A fuel c₀ :=
  faultFree_of_valInvA (L := L) (V := V) (P := fun st => ∃ tid, (sp tid).HoldsD (ds tid) st)
    (fun _ tree ⟨tid, h⟩ hex =>
      ValXA.mono (fun _ h' => ⟨tid, h'⟩) (valSpecA_stepD hG (sp tid) (hsz tid) h tree hex))
    (fun _ tree ⟨tid, h⟩ hex => noFault_valSpecAD (sp tid) (hag tid) h tree hex)
    ⟨hm, fun i t ht => ⟨i, h0 i t ht⟩⟩

/-- **The spec from a partial triple** in `inv S G`, at a thread state at
the start of a laid-out program `p` (its own mask), with declarations `ds`
and no exceptional exit. -/
theorem holdsD_inv_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {S : SharedEnv.Layout}
    {p : Program} [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → Unit → Prop}
    {E : Int64 → MachineData → Unit → Prop} {ds : Decls}
    (ht : MachineWP.PartialTripleEnv (SharedEnv.inv S G) P p Q E) (henv : cenv = layout p) {st : State}
    (he : st.exe = layout p) (hds : st.decls = ds) (hend : st.endPc = (layout p).addrOf p.length)
    (hpc : st.st.2 = (layout p).addrOf 0) (hP : P st.st.1 ()) (hE : ∀ a s g, ¬ E a s g := by simp) :
    QA64MD ds (SharedEnv.inv S G) (layout p) (layout p) ((layout p).addrOf p.length)
      (fun y => y.1.2 = (layout p).addrOf p.length) st () := by
  refine ⟨he, hds, hend, ?_⟩
  have hm : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hm]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h =>
    h.elim And.left (hE _ _ _ ·|>.elim)

/-- **The value specification of a laid-out program** on the layout `S`:
its own mask, postcondition "at the end". -/
def ValSpecA.ofProgram [layout : _root_.Layout] (G : Loc → Val → Prop) (S : SharedEnv.Layout) (p : Program)
    [hv : Kraken.Executable.ValidLayout (layout p)] (hnp : Kraken.Executable.noPairs (layout p) = true)
    (hlive : (layout p).rmwLive = true) (hnf : DirsNoFault (layout p))
    (hro : ∀ st : State, st.exe = layout p → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyDA) :
    ValSpecA G where
  S := S
  e := layout p
  e' := layout p
  valid := hv
  endPc := (layout p).addrOf p.length
  post y := y.1.2 = (layout p).addrOf p.length
  post_end _ h := h
  noPairs := hnp
  mask := MaskOf.refl _
  rmwLive := hlive
  noFault := hnf
  rootOnly := hro

/-! ## Fixed layouts: the address runs at `G = ⊤` -/

/-- **Program-level fault freedom from address runs** (fixed layouts,
`G = ⊤`): one specification over `invTop` per thread id, at strict sized
declarations agreeing on its layout; no hypothesis on the memory. -/
theorem a64_faultFree_of_addrSpecs {A : Arch} {fuel : Nat} (sp : Nat → ValSpecA fun _ _ => True)
    (ds : Nat → Decls) (hsz : ∀ tid, (ds tid).StrictSized) (hag : ∀ tid, (ds tid).AgreesOnA (sp tid).S)
    {c₀ : Config isa} (h0 : ∀ tid t, c₀.threads[tid]? = some t → (sp tid).HoldsD (ds tid) t.st) :
    Config.FaultFree A fuel c₀ :=
  a64_faultFree_of_valSpecs (L := fun _ => False) (V := fun _ => True)
    (fun _ _ => ⟨fun _ _ => trivial, fun _ => trivial⟩) sp ds hsz hag (memVals_empty _ _) h0

/-- **The specification of an address run** (`G = ⊤`, `invTop S`): an
image, its mask, the end address ("at the end" as postcondition) and the
image's static facts. -/
def ValSpecA.ofAddr (S : SharedEnv.Layout) (e e' : Kraken.Executable Directive)
    [hv : Kraken.Executable.ValidLayout e] (endPc : Int64) (hnp : Kraken.Executable.noPairs e = true)
    (hm : MaskOf e e') (hlive : e.rmwLive = true) (hnf : DirsNoFault e)
    (hro : ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyDA) :
    ValSpecA fun _ _ => True where
  S := S
  e := e
  e' := e'
  valid := hv
  endPc := endPc
  post y := y.1.2 = endPc
  post_end _ h := h
  noPairs := hnp
  mask := hm
  rmwLive := hlive
  noFault := hnf
  rootOnly := hro

/-- **An address run is a specification at `G = ⊤`**: the state's code,
declarations and end address, and `AddrSafeA` of its machine state over the
mask. -/
theorem holdsD_ofAddr {S : SharedEnv.Layout} {e e' : Kraken.Executable Directive}
    [Kraken.Executable.ValidLayout e] {endPc : Int64} {hnp : Kraken.Executable.noPairs e = true}
    {hm : MaskOf e e'} {hlive : e.rmwLive = true} {hnf : DirsNoFault e}
    {hro : ∀ st : State, st.exe = e' → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootOnlyDA}
    {ds : Decls} {st : State} (he : st.exe = e) (hds : st.decls = ds) (hend : st.endPc = endPc)
    (ha : AddrSafeA S e' endPc st.st) : (ValSpecA.ofAddr S e e' endPc hnp hm hlive hnf hro).HoldsD ds st :=
  ⟨he, hds, hend, ha⟩

/-- The threads of `Config.init states initMem` are the start states: a
per-state hypothesis gives the per-thread one (`init_threads_of`, AArch64). -/
theorem init_threads_ofA {P : Nat → State → Prop} {states : List isa.State} {initMem : List (Loc × Val)}
    (h0 : ∀ tid s, states[tid]? = some s → P tid s) :
    ∀ tid t, (Config.init states initMem).threads[tid]? = some t → P tid t.st := by
  intro tid t ht
  obtain ⟨s, hs, rfl⟩ := Config.init_get?_thread ht
  exact h0 tid s hs

/-- `init_threads_ofA` for a two-thread start `[s₀, s₁]`. -/
theorem init_threads_of2 {P : Nat → State → Prop} {s₀ s₁ : isa.State} {initMem : List (Loc × Val)}
    (h₀ : P 0 s₀) (h₁ : P 1 s₁) :
    ∀ tid t, (Config.init [s₀, s₁] initMem).threads[tid]? = some t → P tid t.st :=
  init_threads_ofA fun tid s hs => by
    match tid, hs with
    | 0, hs => cases hs; exact h₀
    | 1, hs => cases hs; exact h₁
    | _ + 2, hs => cases hs

/-- `init_threads_ofA` for a three-thread start `[s₀, s₁, s₂]`. -/
theorem init_threads_of3 {P : Nat → State → Prop} {s₀ s₁ s₂ : isa.State} {initMem : List (Loc × Val)}
    (h₀ : P 0 s₀) (h₁ : P 1 s₁) (h₂ : P 2 s₂) :
    ∀ tid t, (Config.init [s₀, s₁, s₂] initMem).threads[tid]? = some t → P tid t.st :=
  init_threads_ofA fun tid s hs => by
    match tid, hs with
    | 0, hs => cases hs; exact h₀
    | 1, hs => cases hs; exact h₁
    | 2, hs => cases hs; exact h₂
    | _ + 3, hs => cases hs

/-- **A 64-bit compare-and-swap writes its new value**: every value an
`rmwOpBits 64` CAS with new value `y` writes is `y` (read at 64 bits), so a
property of `y` is one of the written value. The generic form of the
pointer programs' `msqValA_cas`, `treiberValA_cas` and `treiber2ValA_cas`. -/
theorem rmwOpBits_cas_val {P : BitVec 64 → Prop} {c y : BitVec 64} (hy : P y) :
    ∀ old v, rmwOpBits 64 (fun old => if old = c then some y else none) old = some v → P (v.setWidth 64) := by
  intro old v h
  simp only [rmwOpBits, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  split at ha
  · cases ha
    simpa using hy
  · cases ha

end Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.AArch64.EnvG

/-! ## Specifications in a whole image

Moved from `EnvG/MemValsA64MsQueue.lean` (same names, in the
namespace `…EnvG.MsQueue`). -/

/-- **The value specification of a run to an exit address** in an image
(`e = e'`, no mask): postcondition "at `endPc`". -/
def ValSpecA.ofImageA (G : Loc → Val → Prop) (S : SharedEnv.Layout) (e : Kraken.Executable Directive)
    [hv : Kraken.Executable.ValidLayout e] (endPc : Int64) (hnp : Kraken.Executable.noPairs e = true)
    (hlive : e.rmwLive = true) (hnf : DirsNoFault e) (hph : Phase1TreeF e) : ValSpecA G where
  S := S
  e := e
  e' := e
  valid := hv
  endPc := endPc
  post y := y.1.2 = endPc
  post_end _ h := h
  noPairs := hnp
  mask := MaskOf.refl _
  rmwLive := hlive
  noFault := hnf
  rootOnly st he hd tree hex := rootOnlyDA_of_phase1ShapeF (hph st he hd tree hex)

/-- **A counted value run to `endPc` is the specification**: the state's
code, declarations and end address, and a counted `Safely` from its machine
state. -/
theorem holdsD_ofImageA {G : Loc → Val → Prop} {S : SharedEnv.Layout} {e : Kraken.Executable Directive}
    [Kraken.Executable.ValidLayout e] {endPc : Int64} {hnp : Kraken.Executable.noPairs e = true}
    {hlive : e.rmwLive = true} {hnf : DirsNoFault e} {hph : Phase1TreeF e} {ds : Decls} {st : isa.State}
    (he : st.exe = e) (hds : st.decls = ds) (hend : st.endPc = endPc)
    (hrun : Safely (e.instrStepEnv (SharedEnv.counted (SharedEnv.inv S G)))
      (fun x => (x.1.2 = endPc ∧ True) ∨ False) (st.st, ((), 0))) :
    (ValSpecA.ofImageA G S e endPc hnp hlive hnf hph).HoldsD ds st :=
  ⟨he, hds, hend, (Safely.uncountA hrun).mono fun _ ⟨_, h⟩ => h.elim And.left False.elim⟩

end Kraken.Promising.SLR.EnvG.MsQueue

#print axioms Kraken.Promising.AArch64.EnvG.a64_faultFree_of_valSpecs
#print axioms Kraken.Promising.AArch64.EnvG.a64_faultFree_of_addrSpecs
