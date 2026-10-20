/-
**The purity environment, x64 link**: from one `vcgen` judgment per thread in
`(SharedEnv.relPure A g₀.rel).within S` to the purity hypotheses of
`final_of_relWrites`.

As for `EnvG` (`X64LiveRun.lean`), the x64 run lemma needs the environment
restricted to a shared layout `S` (`SharedEnv.within`, `Le16 S`) and the
thread's private memory split from it (`Split S`): `RelPureSpecX` carries
the layout, `RelPureSpecX.Holds` the split.

Under `Arch.tso` every plain store and every RMW is a release
(`plainStore := .rel`, `plainRmw := .acqRel`), so `relPure Arch.tso rel`
asks nothing of any x64 write but the non-temporal ones (`ntStore := .nt`):
its purity obligations are vacuous for programs without `movnti`.

- `RelPureSpecX A rel`, `RelPureSpecX.Holds`.
- `relPureSpecX_step`: one instruction (`relPureSpec_step`, x64), through the
  x64 run lemma `X64.EnvG.exec_treeJ_of_instrStepEnv` at
  `(TreeJ.relWrites …).toWithin S`.
- `final_of_relPureSafelyX`: `final_of_relWrites` with one spec per thread id
  (`final_of_relPureSafely`, x64).
- `RelPureSpecX.ofProgram`, `RelPureSpecX.holds_of_partialTripleEnv`: the entry
  from a `vcgen` triple.
- `Arch.tso`: `RelPureSpecQX A Q` (the same at a general write
  condition, in `relPureQ A Q`), `relPureSpecQX_step`,
  `EvTree.noNT_tso_of_relWrites_false`, `noNTInv_of_specQX`, and
  `final_of_relPureSafelyQX_tso`: at `Q := fun _ _ => False` one spec per
  thread discharges both the scope `NTFree Arch.tso` and purity for any ghost.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnv
import Kraken.Promising.SLR.EnvG.X64LiveRun
import Kraken.Promising.SLR.TsoPromisePure
import Kraken.EnvCfg

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike

/-- **A thread's purity specification, x64**: the shared layout (at most 16
bytes per location), code, end address and a postcondition at the end
address; the invariant is `Safely` in `(relPure A rel).within S`. -/
structure RelPureSpecX (A : Arch) (rel : Loc → Pred) where
  S : SharedEnv.Layout
  le16 : Le16 S
  e : Kraken.Executable Directive
  valid : Kraken.Executable.ValidLayout e
  endPc : Int64
  post : MachineState × Unit → Prop
  post_end : ∀ y, post y → y.1.2 = endPc

variable {A : Arch} {rel : Loc → Pred}

/-- The specification holds at a thread state: its code, end address, no
declarations, a private memory split from `S`, and the `Safely` judgment at
its machine state. -/
def RelPureSpecX.Holds (sp : RelPureSpecX A rel) (st : State) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = {} ∧ Split sp.S st.st.1.dmem ∧
    Safely (sp.e.instrStepEnv ((SharedEnv.relPure A rel).within sp.S)) sp.post (st.st, ())

/-- **One instruction, x64**: from a state where the spec holds, every tree
of the thread writes only pure values non-release, and every leaf satisfies
the spec. -/
theorem relPureSpecX_step (sp : RelPureSpecX A rel) {st : State} (h : sp.Holds st) (tree : EvTree State)
    (hex : isa.exec st = some tree) :
    tree.RelWrites A (fun l v => Pred.Pure (rel l) v) ∧ tree.All sp.Holds := by
  obtain ⟨he, hend, hds, hs, hsafe⟩ := h
  have hv := sp.valid
  rcases hsafe.unfold with hP | ⟨R, hT, hR⟩
  · have hpc : st.st.2 = sp.endPc := sp.post_end _ hP
    have hnone : isa.exec st = none := by
      show exec st = none
      simp [exec, hpc, hend]
    rw [hnone] at hex
    cases hex
  · exact exec_treeJ_of_instrStepEnv
      ((TreeJ.relWrites A (fun l v => Pred.Pure (rel l) v) sp.Holds).toWithin sp.S) (within_fit _ _) sp.le16
      he hds hs hT (fun m g' hm hs' => by cases g'; exact ⟨he, hend, hds, hs', hR _ hm⟩) tree hex

/-- **`final_of_relWrites` from x64 purity specifications**
(`final_of_relPureSafely`, x64). -/
theorem final_of_relPureSafelyX (A : Arch) (fuel : Nat) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecX A g₀.rel) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model isa) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_relWritesJ A fuel hH hE hpend (fun tid st => (sp tid).Holds st)
    (fun tid _ tree h hex => relPureSpecX_step (sp tid) h tree hex) h0 hsafe hc hf hfin

/-! ## From `vcgen` triples -/

/-- The specification of a laid-out program `p` on the layout `S`: the end
of its text, and `Q` there. -/
def RelPureSpecX.ofProgram [layout : _root_.Layout] (S : SharedEnv.Layout) (hS : Le16 S) (p : Program)
    [hv : Kraken.Executable.ValidLayout (layout p)] (Q : MachineData → Unit → Prop) : RelPureSpecX A rel where
  S := S
  le16 := hS
  e := layout p
  valid := hv
  endPc := (layout p).addrOf p.length
  post x := (x.1.2 = (layout p).addrOf p.length ∧ Q x.1.1 x.2) ∨ False
  post_end _ h := h.elim And.left False.elim

/-- **The spec from a partial triple** in `(relPure A rel).within S`, at a
thread state at the start of `p` with a split private memory. -/
theorem RelPureSpecX.holds_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {S : SharedEnv.Layout}
    {hS : Le16 S} {p : Program} [Kraken.Executable.ValidLayout (layout p)] {P Q : MachineData → Unit → Prop}
    {E : Int64 → MachineData → Unit → Prop}
    (ht : MachineWP.PartialTripleEnv ((SharedEnv.relPure A rel).within S) P p Q E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hs : Split S st.st.1.dmem) (hP : P st.st.1 ()) (hE : ∀ a s g, ¬ E a s g := by simp) :
    (RelPureSpecX.ofProgram (A := A) (rel := rel) S hS p Q).Holds st := by
  refine ⟨he, hend, hds, hs, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-! ## No non-temporal store, and purity, under `Arch.tso`

`final_of_relWrites` also needs the scope `Config.NTFree A`, vacuous under
`Arch.armv8` but not under `Arch.tso` (x86 `movnti`). One judgment per thread
in `(relPureQ A Q).within S` at `Q := fun _ _ => False` (every write a
release) gives both: under `Arch.tso` such a tree has no non-temporal store
(`EvTree.noNT_tso_of_relWrites_false`), so the program has the `ISA.NoNTInv`
invariant `∃ tid, (sp tid).Holds` (`noNTInv_of_specQX`; `NTFreeTso.lean`), and
an NT-free tree writes every location by a release (`EvTree.NoNT.relWrites`),
so purity holds for every ghost (`final_of_relPureSafelyQX_tso`). For x64 code
without `movnti` the `vcgen` obligations of this environment are trivial
(every `mov` store is a release under `Arch.tso`). -/

/-- **Under `Arch.tso`, a tree whose every write is a release has no
non-temporal store** (an RMW never is one under `Arch.tso`). -/
theorem _root_.Kraken.Promising.EvTree.noNT_tso_of_relWrites_false {σ : Type} :
    ∀ {t : EvTree σ}, t.RelWrites Arch.tso (fun _ _ => False) → t.NoNT Arch.tso
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => EvTree.noNT_tso_of_relWrites_false (h i)
  | .load _ _ _ _, h => fun v => EvTree.noNT_tso_of_relWrites_false (h v)
  | .store _ _ _ _ _, h => ⟨fun hk => h.1 (by rw [hk]; decide), fun b => EvTree.noNT_tso_of_relWrites_false (h.2 b)⟩
  | .rmw k _ _ _ _, h => ⟨by cases k <;> decide, fun v => EvTree.noNT_tso_of_relWrites_false (h.2 v)⟩
  | .fence _ ret, h => show EvTree.NoNT _ (ret ()) from EvTree.noNT_tso_of_relWrites_false (t := ret ()) (h ())

private theorem all_mono {σ : Type} {P P' : σ → Prop} (hP : ∀ s, P s → P' s) :
    ∀ {t : EvTree σ}, t.All P → t.All P'
  | .done s, h => hP s h
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => all_mono hP (h i)
  | .load _ _ _ _, h => fun v => all_mono hP (h v)
  | .store _ _ _ _ _, h => fun b => all_mono hP (h b)
  | .rmw _ _ _ _ _, h => fun v => all_mono hP (h v)
  | .fence _ _, h => fun u => all_mono hP (h u)

/-- **A thread's specification in `relPureQ A Q`, x64** (`RelPureSpecX` at a
general write condition `Q`). -/
structure RelPureSpecQX (A : Arch) (Q : Loc → Val → Prop) where
  S : SharedEnv.Layout
  le16 : Le16 S
  e : Kraken.Executable Directive
  valid : Kraken.Executable.ValidLayout e
  endPc : Int64
  post : MachineState × Unit → Prop
  post_end : ∀ y, post y → y.1.2 = endPc

variable {Q : Loc → Val → Prop}

/-- The specification holds at a thread state (`RelPureSpecX.Holds`). -/
def RelPureSpecQX.Holds (sp : RelPureSpecQX A Q) (st : State) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = {} ∧ Split sp.S st.st.1.dmem ∧
    Safely (sp.e.instrStepEnv ((SharedEnv.relPureQ A Q).within sp.S)) sp.post (st.st, ())

/-- **One instruction** (`relPureSpecX_step` at `Q`). -/
theorem relPureSpecQX_step (sp : RelPureSpecQX A Q) {st : State} (h : sp.Holds st) (tree : EvTree State)
    (hex : isa.exec st = some tree) : tree.RelWrites A Q ∧ tree.All sp.Holds := by
  obtain ⟨he, hend, hds, hs, hsafe⟩ := h
  have hv := sp.valid
  rcases hsafe.unfold with hP | ⟨R, hT, hR⟩
  · have hpc : st.st.2 = sp.endPc := sp.post_end _ hP
    have hnone : isa.exec st = none := by
      show exec st = none
      simp [exec, hpc, hend]
    rw [hnone] at hex
    cases hex
  · exact exec_treeJ_of_instrStepEnv ((TreeJ.relWrites A Q sp.Holds).toWithin sp.S) (within_fit _ _) sp.le16
      he hds hs hT (fun m g' hm hs' => by cases g'; exact ⟨he, hend, hds, hs', hR _ hm⟩) tree hex

/-- **The no-NT invariant of a program, x64, `Arch.tso`**: the threads'
all-release specifications. -/
theorem noNTInv_of_specQX (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) :
    isa.NoNTInv Arch.tso (fun st => ∃ tid, (sp tid).Holds st) where
  noNT st h tree hex := by
    obtain ⟨tid, h⟩ := h
    exact EvTree.noNT_tso_of_relWrites_false (relPureSpecQX_step (sp tid) h tree hex).1
  step st h tree hex := by
    obtain ⟨tid, h⟩ := h
    exact all_mono (fun _ h' => ⟨tid, h'⟩) (relPureSpecQX_step (sp tid) h tree hex).2

/-- **`final_of_relWrites` under `Arch.tso` from x64 all-release
specifications**: the scope `NTFree` (`Config.ntFree_of_noNTInv`) and purity
for any initial ghost (`EvTree.NoNT.relWrites`) from one specification per
thread id. -/
theorem final_of_relPureSafelyQX_tso (fuel : Nat) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model isa) Arch.tso B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  have hs : ∀ s ∈ states, ∃ tid, (sp tid).Holds s := fun s hs => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
    exact ⟨i, h0 i _ (List.getElem?_eq_getElem hi)⟩
  exact final_of_relWritesJ Arch.tso fuel (fun _ hc' => Config.ntFree_of_noNTInv (noNTInv_of_specQX sp) hs hc')
    hE hpend (fun tid st => (sp tid).Holds st)
    (fun tid _ tree h hex => ⟨EvTree.NoNT.relWrites tso_storeKind_rel
      (EvTree.noNT_tso_of_relWrites_false (relPureSpecQX_step (sp tid) h tree hex).1),
      (relPureSpecQX_step (sp tid) h tree hex).2⟩) h0 hsafe hc hf hfin

/-- The specification of a laid-out program `p` on the layout `S`
(`RelPureSpecX.ofProgram` at `Q`). -/
def RelPureSpecQX.ofProgram [layout : _root_.Layout] (S : SharedEnv.Layout) (hS : Le16 S) (p : Program)
    [hv : Kraken.Executable.ValidLayout (layout p)] (Q' : MachineData → Unit → Prop) : RelPureSpecQX A Q where
  S := S
  le16 := hS
  e := layout p
  valid := hv
  endPc := (layout p).addrOf p.length
  post x := (x.1.2 = (layout p).addrOf p.length ∧ Q' x.1.1 x.2) ∨ False
  post_end _ h := h.elim And.left False.elim

/-- **The spec from a partial triple** in `(relPureQ A Q).within S`
(`RelPureSpecX.holds_of_partialTripleEnv` at `Q`). -/
theorem RelPureSpecQX.holds_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {S : SharedEnv.Layout}
    {hS : Le16 S} {p : Program} [Kraken.Executable.ValidLayout (layout p)] {P Q' : MachineData → Unit → Prop}
    {E : Int64 → MachineData → Unit → Prop}
    (ht : MachineWP.PartialTripleEnv ((SharedEnv.relPureQ A Q).within S) P p Q' E)
    (henv : cenv = layout p) {st : State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0)
    (hs : Split S st.st.1.dmem) (hP : P st.st.1 ()) (hE : ∀ a s g, ¬ E a s g := by simp) :
    (RelPureSpecQX.ofProgram (A := A) (Q := Q) S hS p Q').Holds st := by
  refine ⟨he, hend, hds, hs, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

end Kraken.Promising.X64.EnvG
