/-
**Declarations that resolve as none do: the `decls = {}` links for threads
with declarations**. Generic, x64.

Every x64 link assumes a thread with no declarations (`st.decls = {}`:
`ThreadSpec.Holds`, `QX64*`, `exec_treeJ(Live)_of_instrStepEnv(W)`,
`noFault_of_exec_step`), and each uses it only to unfold `exec` to
`toEv {} …` (`subst hds`). The `.kl` runner's threads carry the runner's
declarations (`MemLayout.decls`, `Kraken/Litmus/Layout.lean`); declarations
are semantic, since `exec` resolves every access through `toEv s.decls`
(`Promising/X64.lean`) and so `Decls.resolve` (`Promising/Basic.lean`) fixes
each event's location. But a declaration that names an access *at its own
footprint* changes nothing: if `ds.resolve a n = .ok ⟨a, n⟩` for every access
`(a, n)` of the thread's code, then `toEv ds` and `toEv {}` build the same
tree. This holds for a sized `.kl` whose code accesses each typed symbol at
its declared width (for example `publish_movdqa.kl`'s `__int128 rec`, accessed
only by 16-byte `movdqa`), and for an untyped symbol accessed in no other
way. It fails for a legacy (unsized) declaration, whose location `⟨a, 0⟩` is a
renaming of `⟨a, n⟩`, which this file does not cover (item 7).

## Contents

- `Decls.AgreesAt ds a n`: `ds` resolves an `n`-byte access at `a` to its
  footprint `⟨a, n⟩`, as `{}` does (`Decls.resolve_empty`). It and
  `Decls.agreesAt_empty`, `EvTree.access_of_agreesAt` moved, same names, to
  the ISA-neutral `EnvG/NoFaultDCommon.lean` (imported here).
- `Effects.DeclsAgree ds eff`: every access of the effect tree agrees
  (16-byte atomic accesses at `16`, non-atomic vector accesses piece by
  piece); `toEv_eq_of_declsAgree`: then `toEv ds eff = toEv {} eff`.
- `CellsDeclsAgree ds e`: every cell of the executable `e`, at every machine
  state and pc, has an agreeing tree (a static, per-program fact, proved by
  unfolding each cell; `cellsDeclsAgree_layout` reduces it to the program's
  directives).
- **`exec_declsAgree`**: for a thread state whose executable's cells agree
  with its declarations, `exec st` is `exec {st with decls := {}}` with the
  declarations put back in the leaves. This is the reusable bridge: any link
  stated at `decls = {}` applies to the state with no declarations, and its
  conclusion is read through `EvTree.map`.
- Instances of the bridge:
  - the run lemmas `exec_treeJ_of_instrStepEnvD`,
    `exec_treeJLive_of_instrStepEnvD`, `exec_treeJLive_of_instrStepEnvWD`
    (the EnvG links' one-instruction step, through `TreeJ.comap`);
  - `noFault_of_exec_stepD` (`noFault_of_exec_step`);
  - the invariant link: `ThreadSpec.HoldsD` (`Holds` with `decls = ds`),
    `threadSpec_stepPreservesD`, `inv_reachableD`, `inv_reachable_postD`, and
    `faultFree_of_threadSpecD` (`Config.FaultFree`).

The `QX64*` link families take `decls = {}` inside their invariant `Q`; a
`…D` copy of each is the corresponding `exec_treeJLive_of_instrStepEnvWD` /
`noFault_of_exec_stepD` application (not done here; no current user).
-/
import Kraken.Promising.SLR.EnvG.X64ImageNoFault
import Kraken.Promising.InvLinkX64
import Kraken.Promising.SLR.Sim.NoFault
import Kraken.Promising.Faults
import Kraken.Promising.SLR.EnvG.NoFaultDCommon

namespace Kraken.Promising

/-- Every piece of an access of `n` 8-byte pieces from `a` agrees. -/
def Decls.PiecesAgree (ds : Decls) : BitVec 64 → Nat → Prop
  | _, 0 => True
  | a, n + 1 => ds.AgreesAt a 8 ∧ Decls.PiecesAgree ds (a + 8) n

end Kraken.Promising

namespace Kraken.Promising.X64

open Kraken Kraken.Promising

/-- **Every access of the effect tree resolves under `ds` as under `{}`**:
an atomic 16-byte access or `rmw16` at `16` bytes, a non-atomic vector access
piece by piece, any other access at its width; on every branch. -/
def _root_.Effects.DeclsAgree (ds : Decls) : Effects → Prop
  | .done _ => True
  | .unimplemented _ => True
  | .gp_unaligned _ _ => True
  | .nonmem_load _ addr w ret => ds.AgreesAt addr w.bytes ∧ ∀ v d, (ret v d).DeclsAgree ds
  | @Effects.nonmem_store _ addr w _ ret => ds.AgreesAt addr w.bytes ∧ ∀ d, (ret d).DeclsAgree ds
  | @Effects.undefined _ _ ret => ∀ a, (ret a).DeclsAgree ds
  | .require_read_access _ _ ok => (ok ()).DeclsAgree ds
  | .require_write_access _ _ ok => (ok ()).DeclsAgree ds
  | .require_exec_access _ ok => (ok ()).DeclsAgree ds
  | .sync_load _ _ _ addr w ret => ds.AgreesAt addr w.bytes ∧ ∀ v d, (ret v d).DeclsAgree ds
  | @Effects.sync_store _ _ _ addr w _ ret => ds.AgreesAt addr w.bytes ∧ ∀ b d, (ret b d).DeclsAgree ds
  | .rmw _ _ addr w _ ret => ds.AgreesAt addr w.bytes ∧ ∀ v d, (ret v d).DeclsAgree ds
  | .fence _ ok => (ok ()).DeclsAgree ds
  | .require_read_access_avx _ _ _ ok => (ok ()).DeclsAgree ds
  | .require_write_access_avx _ _ _ ok => (ok ()).DeclsAgree ds
  | .nonmem_load_avx atomic _ addr w ret =>
    (if atomic && w == .W128 then ds.AgreesAt addr 16 else ds.PiecesAgree addr (w.bytes / 8)) ∧
      ∀ v d, (ret v d).DeclsAgree ds
  | @Effects.nonmem_store_avx atomic _ addr w _ ret =>
    (if atomic && w == .W128 then ds.AgreesAt addr 16 else ds.PiecesAgree addr (w.bytes / 8)) ∧
      ∀ d, (ret d).DeclsAgree ds
  | .rmw16 _ _ addr _ ret => ds.AgreesAt addr 16 ∧ ∀ v d, (ret v d).DeclsAgree ds

theorem loadPieces_of_piecesAgree {σ : Type} {ds : Decls} (dmem : DataMem) :
    ∀ (addr : BitVec 64) (n : Nat) (k : List UInt8 → EvTree σ), ds.PiecesAgree addr n →
      loadPieces ds dmem addr n k = loadPieces {} dmem addr n k
  | _, 0, _, _ => rfl
  | addr, n + 1, k, ⟨h, hs⟩ => by
    simp only [loadPieces]
    have ih : ∀ k' : List UInt8 → EvTree σ, loadPieces ds dmem (addr + 8) n k' = loadPieces {} dmem (addr + 8) n k' :=
      fun k' => loadPieces_of_piecesAgree dmem (addr + 8) n k' hs
    simp only [ih, EvTree.access_of_agreesAt h]

theorem storePieces_of_piecesAgree {σ : Type} {ds : Decls} :
    ∀ (addr : BitVec 64) (n : Nat) (bs : List UInt8) (dmem : DataMem) (k : DataMem → EvTree σ),
      ds.PiecesAgree addr n → storePieces ds addr n bs dmem k = storePieces {} addr n bs dmem k
  | _, 0, _, _, _, _ => rfl
  | addr, n + 1, bs, dmem, k, ⟨h, hs⟩ => by
    simp only [storePieces]
    have ih : ∀ bs' dmem', storePieces ds (addr + 8) n bs' dmem' k = storePieces {} (addr + 8) n bs' dmem' k :=
      fun bs' dmem' => storePieces_of_piecesAgree (addr + 8) n bs' dmem' k hs
    simp only [ih, EvTree.access_of_agreesAt h]

/-- **An agreeing effect tree translates as with no declarations.** -/
theorem toEv_eq_of_declsAgree {ds : Decls} : ∀ eff : Effects, eff.DeclsAgree ds → toEv ds eff = toEv {} eff := by
  intro eff
  induction eff with
  | done _ => intro _; rfl
  | unimplemented _ => intro _; rfl
  | gp_unaligned _ _ => intro _; rfl
  | nonmem_load dmem addr w ret ih =>
    intro h
    have e : ∀ a b, toEv ds (ret a b) = toEv {} (ret a b) := fun a b => ih a b (h.2 a b)
    simp only [toEv, EvTree.access_of_agreesAt h.1, e]
  | nonmem_store dmem addr v ret ih =>
    intro h
    have e : ∀ a, toEv ds (ret a) = toEv {} (ret a) := fun a => ih a (h.2 a)
    simp only [toEv, EvTree.access_of_agreesAt h.1, e]
  | undefined ret ih =>
    intro h
    rename_i inst
    have e : ∀ a, toEv ds (ret a) = toEv {} (ret a) := fun a => ih a (h a)
    cases inst <;> simp only [toEv, e]
  | require_read_access _ _ ok ih => intro h; exact ih () h
  | require_write_access _ _ ok ih => intro h; exact ih () h
  | require_exec_access _ ok ih => intro h; exact ih () h
  | sync_load k xcl dmem addr w ret ih =>
    intro h
    have e : ∀ a b, toEv ds (ret a b) = toEv {} (ret a b) := fun a b => ih a b (h.2 a b)
    simp only [toEv, EvTree.access_of_agreesAt h.1, e]
  | sync_store k xcl dmem addr v ret ih =>
    intro h
    have e : ∀ a b, toEv ds (ret a b) = toEv {} (ret a b) := fun a b => ih a b (h.2 a b)
    simp only [toEv, EvTree.access_of_agreesAt h.1, e]
  | rmw k dmem addr w op ret ih =>
    intro h
    have e : ∀ a b, toEv ds (ret a b) = toEv {} (ret a b) := fun a b => ih a b (h.2 a b)
    simp only [toEv, EvTree.access_of_agreesAt h.1, e]
  | fence k ok ih =>
    intro h
    have e : toEv ds (ok ()) = toEv {} (ok ()) := ih () h
    simp only [toEv, e]
  | require_read_access_avx _ _ _ ok ih => intro h; exact ih () h
  | require_write_access_avx _ _ _ ok ih => intro h; exact ih () h
  | nonmem_load_avx atomic dmem addr w ret ih =>
    intro h
    obtain ⟨ha, hk⟩ := h
    simp only [toEv]
    split
    · next hc =>
      simp only [hc] at ha
      have e : ∀ a b, toEv ds (ret a b) = toEv {} (ret a b) := fun a b => ih a b (hk a b)
      simp only [EvTree.access_of_agreesAt ha, e]
    · next hc =>
      simp only [hc] at ha
      have e : ∀ a b, toEv ds (ret a b) = toEv {} (ret a b) := fun a b => ih a b (hk a b)
      simp only [loadPieces_of_piecesAgree dmem addr _ _ ha, e]
  | nonmem_store_avx atomic dmem addr v ret ih =>
    intro h
    obtain ⟨ha, hk⟩ := h
    simp only [toEv]
    split
    · next hc =>
      simp only [hc] at ha
      have e : ∀ a, toEv ds (ret a) = toEv {} (ret a) := fun a => ih a (hk a)
      simp only [EvTree.access_of_agreesAt ha, e]
    · next hc =>
      simp only [hc] at ha
      have e : ∀ a, toEv ds (ret a) = toEv {} (ret a) := fun a => ih a (hk a)
      simp only [storePieces_of_piecesAgree addr _ _ dmem _ ha, e]
  | rmw16 k dmem addr op ret ih =>
    intro h
    have e : ∀ a b, toEv ds (ret a b) = toEv {} (ret a b) := fun a b => ih a b (h.2 a b)
    simp only [toEv, EvTree.access_of_agreesAt h.1, e]

/-- **Every cell of the executable has an agreeing tree**, at every machine
state and pc (with the step's own continuations: fall through to
`pc + z`, or jump). A static, per-program fact. -/
def CellsDeclsAgree (ds : Decls) (e : _root_.Executable) : Prop :=
  ∀ d z, (d, z) ∈ e.2 → ∀ (s : MachineData) (pc : Int64),
    Effects.DeclsAgree ds (@Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
      (fun s' => .done (s', pc + .ofNat z)) (fun pc' s' => .done (s', pc')))

theorem piecesAgree_empty : ∀ (a : BitVec 64) (n : Nat), Decls.PiecesAgree {} a n
  | _, 0 => trivial
  | a, n + 1 => ⟨rfl, piecesAgree_empty (a + 8) n⟩

/-- With no declarations every effect tree agrees. -/
theorem declsAgree_empty : ∀ eff : Effects, eff.DeclsAgree {} := by
  intro eff
  induction eff with
  | done _ => trivial
  | unimplemented _ => trivial
  | gp_unaligned _ _ => trivial
  | nonmem_load _ _ _ _ ih => exact ⟨rfl, fun v d => ih v d⟩
  | nonmem_store _ _ _ _ ih => exact ⟨rfl, fun d => ih d⟩
  | undefined _ ih => exact fun a => ih a
  | require_read_access _ _ _ ih => exact ih ()
  | require_write_access _ _ _ ih => exact ih ()
  | require_exec_access _ _ ih => exact ih ()
  | sync_load _ _ _ _ _ _ ih => exact ⟨rfl, fun v d => ih v d⟩
  | sync_store _ _ _ _ _ _ ih => exact ⟨rfl, fun b d => ih b d⟩
  | rmw _ _ _ _ _ _ ih => exact ⟨rfl, fun v d => ih v d⟩
  | fence _ _ ih => exact ih ()
  | require_read_access_avx _ _ _ _ ih => exact ih ()
  | require_write_access_avx _ _ _ _ ih => exact ih ()
  | nonmem_load_avx atomic _ addr w _ ih =>
    refine ⟨?_, fun v d => ih v d⟩
    split
    · rfl
    · exact piecesAgree_empty _ _
  | nonmem_store_avx atomic _ addr _ _ ih =>
    refine ⟨?_, fun d => ih d⟩
    split
    · rfl
    · exact piecesAgree_empty _ _
  | rmw16 _ _ _ _ _ ih => exact ⟨rfl, fun v d => ih v d⟩

/-- With no declarations every executable agrees. -/
theorem cellsDeclsAgree_of_forall {ds : Decls} {e : _root_.Executable}
    (h : ∀ eff : Effects, eff.DeclsAgree ds) : CellsDeclsAgree ds e :=
  fun _ _ _ _ _ => h _

/-- A laid-out program's cells are the program's: it suffices that every
directive of the program agrees, at every placement and continuation. -/
theorem cellsDeclsAgree_layout [layout : _root_.Layout] {ds : Decls} {p : Program}
    (h : ∀ d ∈ p, ∀ (lb : Labels) (s : MachineData) (rng : Std.Rco Int64)
      (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects),
      (∀ s', (next s').DeclsAgree ds) → (∀ pc' s', (jmp pc' s').DeclsAgree ds) →
      Effects.DeclsAgree ds (@Directive.interp lb d s rng next jmp)) :
    CellsDeclsAgree ds (layout p) := by
  intro d z hm s pc
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _ _ _ _ (fun _ => trivial) (fun _ _ => trivial)

/-- `EvTree.map` composes (a local copy of `A64MaskCore.evTree_map_map`, which
is in an AArch64 file). -/
theorem evTree_map_map_vec {σ τ υ : Type} (f : σ → τ) (g : τ → υ) :
    ∀ t : EvTree σ, (t.map f).map g = t.map (g ∘ f)
  | .done _ => rfl
  | .fault _ => rfl
  | .choose _ k => by simp only [EvTree.map]; congr 1; funext i; exact evTree_map_map_vec f g (k i)
  | .load _ _ _ ret => by simp only [EvTree.map]; congr 1; funext v; exact evTree_map_map_vec f g (ret v)
  | .store _ _ _ _ ret => by simp only [EvTree.map]; congr 1; funext b; exact evTree_map_map_vec f g (ret b)
  | .rmw _ _ _ _ ret => by simp only [EvTree.map]; congr 1; funext v; exact evTree_map_map_vec f g (ret v)
  | .fence _ ret => by simp only [EvTree.map]; congr 1; funext u; exact evTree_map_map_vec f g (ret u)

/-- The thread state with its declarations dropped. -/
abbrev State.noDecls (st : State) : State := { st with decls := {} }

/-- Put the declarations `ds` back. -/
abbrev State.withDecls (ds : Decls) (st : State) : State := { st with decls := ds }

theorem State.withDecls_noDecls_st (st : State) (m : MachineState) :
    State.withDecls st.decls { st.noDecls with st := m } = { st with st := m } := by
  cases st; rfl

/-- **The bridge.** For a thread state whose executable's cells agree with
its declarations, the tree is the tree of the state with no declarations,
with the declarations put back in the leaves. -/
theorem exec_declsAgree {st : State} [Kraken.Executable.ValidLayout st.exe]
    (hcells : CellsDeclsAgree st.decls st.exe) :
    isa.exec st = (isa.exec st.noDecls).map (EvTree.map (State.withDecls st.decls)) := by
  show exec st = (exec st.noDecls).map _
  have hdir : st.noDecls.directive = st.directive := rfl
  unfold exec
  rw [hdir]
  split
  · rfl
  · next hc =>
    simp only [Option.map_some, evTree_map_map_vec]
    obtain ⟨d, z, rest, hcode⟩ : ∃ d z rest, Kraken.Executable.codeAt st.exe st.st.2 = (d, z) :: rest := by
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hc
      have hd := hc.2
      unfold State.directive at hd
      rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress st.exe st.st.2) =
        Kraken.Executable.codeAt st.exe st.st.2 from by unfold Kraken.Executable.codeAt; congr 1] at hd
      cases hc' : Kraken.Executable.codeAt st.exe st.st.2 with
      | nil => rw [hc'] at hd; simp at hd
      | cons x rest => exact ⟨x.1, x.2, rest, rfl⟩
    have hmem := EnvG.mem_of_codeAt hcode
    obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
    have hstep : _root_.Executable.step st.exe st.st (fun s' => .done s') =
        @Directive.interp (_root_.Executable.labels st.exe) d st.st.1 (.mk st.st.2 (st.st.2 + .ofNat z))
          (fun s' => .done (s', st.st.2 + .ofNat z)) (fun pc' s' => .done (s', pc')) := by
      unfold Executable.step
      letI := Executable.labels st.exe
      simp only
      rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
      simp only [Directives.interp]
    rw [hstep, toEv_eq_of_declsAgree _ (hcells d z hmem st.st.1 st.st.2)]
    rfl

/-! ## The EnvG one-instruction run, with declarations -/

/-- **`exec_treeJ_of_instrStepEnv` with agreeing declarations.** -/
theorem exec_treeJ_of_instrStepEnvD {E : SharedEnv} (J : SLR.EnvSpike.TreeJ E State) {S : SharedEnv.Layout}
    (hF : X64Fit S E) (hS : Le16 S)
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State} {g : E.State}
    {R : MachineState × E.State → Prop} (he : st.exe = e) (hcells : CellsDeclsAgree st.decls e)
    (hs : Split S st.st.1.dmem) (h : e.instrStepEnv E (st.st, g) R)
    (hR : ∀ m g', R (m, g') → Split S m.1.dmem → J.Post { st with st := m } g') :
    ∀ tree, isa.exec st = some tree → J.W tree g := by
  intro tree htree
  haveI : Kraken.Executable.ValidLayout st.exe := he ▸ inferInstance
  rw [exec_declsAgree (he ▸ hcells)] at htree
  obtain ⟨tree₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp htree
  exact EnvG.exec_treeJ_of_instrStepEnv (J.comap (State.withDecls st.decls)) hF hS (st := st.noDecls) he rfl hs h
    (fun m g' hm hs' => by
      show J.Post (State.withDecls st.decls { st.noDecls with st := m }) g'
      rw [State.withDecls_noDecls_st]; exact hR m g' hm hs') tree₀ h₀

/-- **`exec_treeJLive_of_instrStepEnv` with agreeing declarations.** -/
theorem exec_treeJLive_of_instrStepEnvD {E : SharedEnv} (J : SLR.EnvG.TreeJLive E State) {S : SharedEnv.Layout}
    (hF : X64Fit S E) (hS : Le16 S)
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State} {g : E.State}
    {R : MachineState × E.State → Prop} (he : st.exe = e) (hcells : CellsDeclsAgree st.decls e)
    (hs : Split S st.st.1.dmem) (h : e.instrStepEnv E (st.st, g) R)
    (hR : ∀ m g', R (m, g') → Split S m.1.dmem → J.Post { st with st := m } g') :
    ∀ tree, isa.exec st = some tree → J.W tree g := by
  intro tree htree
  haveI : Kraken.Executable.ValidLayout st.exe := he ▸ inferInstance
  rw [exec_declsAgree (he ▸ hcells)] at htree
  obtain ⟨tree₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp htree
  exact EnvG.exec_treeJLive_of_instrStepEnv (J.comap (State.withDecls st.decls)) hF hS (st := st.noDecls) he rfl
    hs h (fun m g' hm hs' => by
      show J.Post (State.withDecls st.decls { st.noDecls with st := m }) g'
      rw [State.withDecls_noDecls_st]; exact hR m g' hm hs') tree₀ h₀

/-- **`exec_treeJLive_of_instrStepEnvW` with agreeing declarations** (the
form the `QX64*` links use). -/
theorem exec_treeJLive_of_instrStepEnvWD {E : SharedEnv} (J : SLR.EnvG.TreeJLive E State)
    {S : SharedEnv.Layout} (hS : Le16 S)
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State} {g : E.State}
    {R : MachineState × E.State → Prop} (he : st.exe = e) (hcells : CellsDeclsAgree st.decls e)
    (hs : Split S st.st.1.dmem) (h : e.instrStepEnv (E.within S) (st.st, g) R)
    (hR : ∀ m g', R (m, g') → Split S m.1.dmem → J.Post { st with st := m } g') :
    ∀ tree, isa.exec st = some tree → J.W tree g := by
  intro tree htree
  haveI : Kraken.Executable.ValidLayout st.exe := he ▸ inferInstance
  rw [exec_declsAgree (he ▸ hcells)] at htree
  obtain ⟨tree₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp htree
  exact EnvG.exec_treeJLive_of_instrStepEnvW (J.comap (State.withDecls st.decls)) hS (st := st.noDecls) he rfl
    hs h (fun m g' hm hs' => by
      show J.Post (State.withDecls st.decls { st.noDecls with st := m }) g'
      rw [State.withDecls_noDecls_st]; exact hR m g' hm hs') tree₀ h₀

/-- **`noFault_of_exec_step` with agreeing declarations.** -/
theorem noFault_of_exec_stepD {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State}
    (he : st.exe = e) (hcells : CellsDeclsAgree st.decls e) (hnf : EnvG.DirsNoFaultCode e) {E : SharedEnv}
    {g : E.State} {R : MachineState × E.State → Prop} (hR : e.instrStepEnv E (st.st, g) R) :
    ∀ tree, isa.exec st = some tree → tree.NoFault := by
  intro tree htree
  haveI : Kraken.Executable.ValidLayout st.exe := he ▸ inferInstance
  rw [exec_declsAgree (he ▸ hcells)] at htree
  obtain ⟨tree₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp htree
  exact (EvTree.noFault_map _ _).mpr (EnvG.noFault_of_exec_step (st := st.noDecls) he rfl hnf hR tree₀ h₀)

/-! ## The invariant link, with declarations -/

/-- The specification holds at a thread state with declarations `ds` that
agree with the code (`ThreadSpec.Holds` with `decls = ds` in place of
`decls = {}`). -/
def ThreadSpec.HoldsD {S : SharedEnv.Layout} {G : Loc → Val → Prop} (sp : ThreadSpec S G) (ds : Decls)
    (st : State) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = ds ∧ CellsDeclsAgree ds sp.e ∧
    Split S st.st.1.dmem ∧ sp.inv (st.st, ())

/-- `Holds` is `HoldsD {}`. -/
theorem ThreadSpec.holdsD_of_holds {S : SharedEnv.Layout} {G : Loc → Val → Prop} {sp : ThreadSpec S G}
    {st : State} (h : sp.Holds st) : sp.HoldsD {} st :=
  ⟨h.1, h.2.1, h.2.2.1, cellsDeclsAgree_of_forall declsAgree_empty, h.2.2.2.1, h.2.2.2.2⟩

/-- A thread specification with agreeing declarations is kept by every
instruction against a memory satisfying `MemInv G`, which the instruction
keeps too (`threadSpec_stepPreserves` through `exec_declsAgree`). -/
theorem threadSpec_stepPreservesD {A : Arch} {S : SharedEnv.Layout} {G : Loc → Val → Prop} (hS : Le16 S)
    (sp : Nat → ThreadSpec S G) (ds : Nat → Decls) :
    StepPreserves (I := isa) A G (fun tid st => (sp tid).HoldsD (ds tid) st) := by
  intro tid t mem outs o ⟨he, hend, hds, hcells, hs, hinv⟩ hm hstep ho
  have hv := (sp tid).valid
  rcases (sp tid).closed _ hinv with hP | ⟨R, hT, hR⟩
  · have hpc : t.st.st.2 = (sp tid).endPc := (sp tid).post_end _ hP
    unfold stepOne at hstep
    have hex : isa.exec t.st = none := by
      show exec t.st = none
      simp [exec, hpc, hend]
    rw [hex] at hstep
    cases hstep
  · have hc' : CellsDeclsAgree t.st.decls t.st.exe := by rw [hds, he]; exact hcells
    obtain ⟨⟨⟨hRo, hs'⟩, he', hend', hds'⟩, hm'⟩ :=
      stepOne_allInv A (Q := fun st' : State => (R (st'.st, ()) ∧ Split S st'.st.1.dmem) ∧
          st'.exe = t.st.exe ∧ st'.endPc = t.st.endPc ∧ st'.decls = t.st.decls) hstep ho (fun tree htree => by
        haveI : Kraken.Executable.ValidLayout t.st.exe := he ▸ hv
        rw [exec_declsAgree hc'] at htree
        obtain ⟨tree₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp htree
        refine (EvTree.allInv_map (σ := State) (τ := State) G (State.withDecls t.st.decls) _ tree₀).mpr ?_
        have := exec_allInv_of_instrStepEnv hS (st := t.st.noDecls) he rfl hs hT tree₀ h₀
        refine EvTree.AllInv.mono ?_ this
        rintro x ⟨⟨hx1, hx2⟩, hx3, hx4, -⟩
        exact ⟨⟨hx1, hx2⟩, hx3, hx4, rfl⟩) hm
    exact ⟨⟨he'.trans he, hend'.trans hend, hds'.trans hds, hcells, hs', hR _ hRo⟩, hm'⟩

/-- **Links A and B with agreeing declarations** (`inv_reachable` for
`HoldsD`): at every configuration reachable from `c0` the memory satisfies
`MemInv G` and every thread its specification. -/
theorem inv_reachableD {A : Arch} {fuel : Nat} {S : SharedEnv.Layout} {G : Loc → Val → Prop} (hS : Le16 S)
    (sp : Nat → ThreadSpec S G) (ds : Nat → Decls) {c0 c : Config isa} (hm0 : MemInv G c0.mem)
    (h0 : ∀ tid t, c0.threads[tid]? = some t → (sp tid).HoldsD (ds tid) t.st) (h : Reachable A fuel c0 c) :
    MemInv G c.mem ∧ ∀ tid t, c.threads[tid]? = some t → (sp tid).HoldsD (ds tid) t.st :=
  configInv_reachable (threadSpec_stepPreservesD hS sp ds) ⟨hm0, h0⟩ h

/-- **Link B at the end address, with agreeing declarations**
(`inv_reachable_post` for `HoldsD`). -/
theorem inv_reachable_postD {A : Arch} {fuel : Nat} {S : SharedEnv.Layout} {G : Loc → Val → Prop}
    (hS : Le16 S) (sp : Nat → ThreadSpec S G) (ds : Nat → Decls) {c0 c : Config isa} (hm0 : MemInv G c0.mem)
    (h0 : ∀ tid t, c0.threads[tid]? = some t → (sp tid).HoldsD (ds tid) t.st) (h : Reachable A fuel c0 c)
    {tid : Nat} {t : Thread isa} (ht : c.threads[tid]? = some t)
    (hstuck : ∀ x R, x.1.2 = (sp tid).endPc → ¬ (sp tid).e.instrStepEnv (SharedEnv.inv S G) x R)
    (hend : t.st.st.2 = (sp tid).endPc) : (sp tid).post (t.st.st, ()) := by
  obtain ⟨-, -, -, -, -, hinv⟩ := (inv_reachableD hS sp ds hm0 h0 h).2 tid t ht
  rcases (sp tid).closed _ hinv with hP | ⟨R, hT, -⟩
  · exact hP
  · exact (hstuck _ R hend hT).elim

/-- **No reachable configuration has a faulting step**, for threads whose
specifications hold with agreeing declarations at `c0`, on executables whose
non-data cells are fault-free (`DirsNoFaultCode`): every thread of every
reachable configuration satisfies its specification (`inv_reachableD`), so
it is at its end address (no tree) or takes an instruction step, whose cell
is fault-free (`noFault_of_exec_stepD`). -/
theorem faultFree_of_threadSpecD {A : Arch} {fuel : Nat} {S : SharedEnv.Layout} {G : Loc → Val → Prop}
    (hS : Le16 S) (sp : Nat → ThreadSpec S G) (ds : Nat → Decls) {c0 : Config isa} (hm0 : MemInv G c0.mem)
    (h0 : ∀ tid t, c0.threads[tid]? = some t → (sp tid).HoldsD (ds tid) t.st)
    (hnf : ∀ tid, EnvG.DirsNoFaultCode (sp tid).e) : Config.FaultFree A fuel c0 := by
  intro c hc tid m hf
  obtain ⟨outs, hs, -⟩ := id hf
  obtain ⟨t, ht, -⟩ := stepThread_eq_some hs
  refine Config.not_faultStep_of_noFaultRun A ht (fun tree htree => EvTree.NoFault.run A _ _ ?_ _) m hf
  obtain ⟨he, hend, hds, hcells, -, hinv⟩ := (inv_reachableD hS sp ds hm0 h0 hc).2 tid t ht
  have hv := (sp tid).valid
  rcases (sp tid).closed _ hinv with hP | ⟨R, hT, -⟩
  · have hpc : t.st.st.2 = (sp tid).endPc := (sp tid).post_end _ hP
    have hex : isa.exec t.st = none := by
      show exec t.st = none
      simp [exec, hpc, hend]
    rw [hex] at htree; cases htree
  · exact noFault_of_exec_stepD he (hds ▸ hcells) (hnf tid) hT tree htree

end Kraken.Promising.X64

#print axioms Kraken.Promising.X64.exec_declsAgree
#print axioms Kraken.Promising.X64.exec_treeJ_of_instrStepEnvD
#print axioms Kraken.Promising.X64.exec_treeJLive_of_instrStepEnvD
#print axioms Kraken.Promising.X64.exec_treeJLive_of_instrStepEnvWD
#print axioms Kraken.Promising.X64.noFault_of_exec_stepD
#print axioms Kraken.Promising.X64.inv_reachableD
#print axioms Kraken.Promising.X64.inv_reachable_postD
#print axioms Kraken.Promising.X64.faultFree_of_threadSpecD
