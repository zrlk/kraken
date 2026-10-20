/-
**Declarations as fault restriction: the `decls = {}` links for threads with
strict sized declarations, at any address**. Generic,
x64.

`X64VecDecls.exec_declsAgree` reads a thread with declarations `ds` as the
thread with none, *provided* every access of the code agrees
(`CellsDeclsAgree`), a syntactic condition on fixed addresses. It does not
cover code that accesses memory at register-valued addresses which the proof
cannot pin down (an EnvG load on an unclean path returns an arbitrary value).
This file needs nothing of the code:

- `EvTree.underDecls ds t` re-resolves every event of `t` against `ds`
  (`EvTree.access`): an event at a location `ds` resolves keeps it (at the
  resolved location), any other becomes `ds`'s mixed-size fault;
- `toEv_underDecls`: `toEv ds eff = (toEv {} eff).underDecls ds` for every
  effect tree, so `exec_underDecls`:
  `isa.exec st = (isa.exec st.noDecls).map (·.underDecls st.decls |>.map (withDecls st.decls))`,
  for every thread state;
- for *strict sized* declarations (`Decls.Sized`: `unsizedDefault = false`,
  no unsized declaration) a resolved location is the access's own footprint
  (`Decls.resolve_ok_of_sized`), so `underDecls` only turns events into
  faults. A tree judgment has `W (.fault _)` as a law, hence
  `TreeJLive.underDecls` / `TreeJ.underDecls`: a judgment of the
  `decls = {}` tree for `J.underDecls` is one of the restricted tree for `J`;
- the run bridges `exec_treeJLive_of_underDecls`, `exec_treeJ_of_underDecls`:
  any `decls = {}` run lemma, applied to `(J.comap (withDecls ds)).underDecls`,
  gives the run at `decls = ds`.

This is the only use of declarations in a safety proof: the restriction says
nothing about faults (a fault is a `W` law), so the no-fault side of a
program with mixed-size accesses is not covered here.

The ISA-neutral half (`Decls.Sized`, `Decls.resolve_ok_of_sized`,
`EvTree.underDecls`, `EvTree.map_access`, `EvTree.map_underDecls`,
`TreeJLive.underDecls`, `TreeJ.underDecls`) is now the instance of
the AArch64 declarations proofs' neutral copy in `EnvG/A64DeclsCommon.lean` (`Decls.StrictSized`,
`EvTree.reresolve`, …): same names and statements; the definitions stay
plain `def`s (default reducibility, unchanged) whose bodies are the neutral
ones.
-/
import Kraken.Promising.SLR.EnvG.X64VecDecls
import Kraken.Promising.SLR.EnvG.A64DeclsCommon

namespace Kraken.Promising

/-- **Strict sized declarations**: strict mode (`unsizedDefault = false`) and
no unsized declaration. The `.kl` runner's declarations of a header with
sized types only. -/
def Decls.Sized (ds : Decls) : Prop := ds.StrictSized

/-- **Under strict sized declarations an access that resolves resolves to
its own footprint.** -/
theorem Decls.resolve_ok_of_sized {ds : Decls} (hs : ds.Sized) {a : BitVec 64} {n : Nat} {l : Loc}
    (h : ds.resolve a n = .ok l) : l = ⟨a, n⟩ :=
  Decls.resolve_ok_of_strictSized hs h

namespace EvTree

/-- **Re-resolve every event against `ds`**: an event at `l` becomes the
event at the location `ds` resolves `l`'s access to, or `ds`'s fault. -/
def underDecls {σ : Type} (ds : Decls) (t : EvTree σ) : EvTree σ :=
  t.reresolve ds

theorem map_access {σ τ : Type} (f : σ → τ) (ds : Decls) (a : BitVec 64) (n : Nat) (k : Loc → EvTree σ) :
    (EvTree.access ds a n k).map f = EvTree.access ds a n fun l => (k l).map f :=
  EvTree.map_access_reresolve f ds a n k

/-- `underDecls` commutes with `map`. -/
theorem map_underDecls {σ τ : Type} (f : σ → τ) (ds : Decls) :
    ∀ t : EvTree σ, (t.underDecls ds).map f = (t.map f).underDecls ds :=
  EvTree.map_reresolve f ds

end EvTree

end Kraken.Promising

namespace Kraken.Promising.X64

open Kraken Kraken.Promising

theorem loadPieces_underDecls {σ : Type} (ds : Decls) (dmem : DataMem) :
    ∀ (addr : BitVec 64) (n : Nat) (k : List UInt8 → EvTree σ),
      (loadPieces {} dmem addr n k).underDecls ds = loadPieces ds dmem addr n fun bs => (k bs).underDecls ds
  | _, 0, _ => rfl
  | addr, n + 1, k => by
    simp only [loadPieces]
    have ih : ∀ k' : List UInt8 → EvTree σ,
        (loadPieces {} dmem (addr + 8) n k').underDecls ds =
          loadPieces ds dmem (addr + 8) n fun bs => (k' bs).underDecls ds :=
      fun k' => loadPieces_underDecls ds dmem (addr + 8) n k'
    split
    · exact ih _
    · split
      · rfl
      · simp only [EvTree.underDecls] at ih ⊢; simp only [EvTree.access_empty, EvTree.reresolve, ih]

theorem storePieces_underDecls {σ : Type} (ds : Decls) :
    ∀ (addr : BitVec 64) (n : Nat) (bs : List UInt8) (dmem : DataMem) (k : DataMem → EvTree σ),
      (storePieces {} addr n bs dmem k).underDecls ds = storePieces ds addr n bs dmem fun d => (k d).underDecls ds
  | _, 0, _, _, _ => rfl
  | addr, n + 1, bs, dmem, k => by
    simp only [storePieces]
    have ih : ∀ bs' dmem', (storePieces {} (addr + 8) n bs' dmem' k).underDecls ds =
        storePieces ds (addr + 8) n bs' dmem' fun d => (k d).underDecls ds :=
      fun bs' dmem' => storePieces_underDecls ds (addr + 8) n bs' dmem' k
    split
    · exact ih _ _
    · split
      · rfl
      · simp only [EvTree.underDecls] at ih ⊢; simp only [EvTree.access_empty, EvTree.reresolve, ih]

/-- **Every effect tree translates under `ds` as its translation under no
declarations, re-resolved against `ds`.** -/
theorem toEv_underDecls (ds : Decls) : ∀ eff : Effects, (toEv {} eff).underDecls ds = toEv ds eff := by
  intro eff
  induction eff with
  | done _ => rfl
  | unimplemented _ => rfl
  | gp_unaligned _ _ => rfl
  | nonmem_load dmem addr w ret ih =>
    simp only [EvTree.underDecls] at ih ⊢; simp only [toEv, EvTree.access_empty, EvTree.reresolve, ih]
  | nonmem_store dmem addr v ret ih =>
    simp only [EvTree.underDecls] at ih ⊢; simp only [toEv, EvTree.access_empty, EvTree.reresolve, ih]
  | undefined ret ih =>
    rename_i inst
    cases inst <;> (simp only [EvTree.underDecls] at ih ⊢; simp only [toEv, EvTree.reresolve, ih])
  | require_read_access _ _ ok ih => exact ih ()
  | require_write_access _ _ ok ih => exact ih ()
  | require_exec_access _ ok ih => exact ih ()
  | sync_load k xcl dmem addr w ret ih =>
    simp only [EvTree.underDecls] at ih ⊢; simp only [toEv, EvTree.access_empty, EvTree.reresolve, ih]
  | sync_store k xcl dmem addr v ret ih =>
    simp only [EvTree.underDecls] at ih ⊢; simp only [toEv, EvTree.access_empty, EvTree.reresolve, ih]
  | rmw k dmem addr w op ret ih =>
    simp only [EvTree.underDecls] at ih ⊢; simp only [toEv, EvTree.access_empty, EvTree.reresolve, ih]
  | fence k ok ih =>
    simp only [EvTree.underDecls] at ih ⊢; simp only [toEv, EvTree.reresolve, ih]
  | require_read_access_avx _ _ _ ok ih => exact ih ()
  | require_write_access_avx _ _ _ ok ih => exact ih ()
  | nonmem_load_avx atomic dmem addr w ret ih =>
    simp only [toEv]
    split
    · simp only [EvTree.underDecls] at ih ⊢; simp only [EvTree.access_empty, EvTree.reresolve, ih]
    · simp only [loadPieces_underDecls]; congr 1; funext bs; exact ih _ _
  | nonmem_store_avx atomic dmem addr v ret ih =>
    simp only [toEv]
    split
    · simp only [EvTree.underDecls] at ih ⊢; simp only [EvTree.access_empty, EvTree.reresolve, ih]
    · simp only [storePieces_underDecls]; congr 1; funext d; exact ih _
  | rmw16 k dmem addr op ret ih =>
    simp only [EvTree.underDecls] at ih ⊢; simp only [toEv, EvTree.access_empty, EvTree.reresolve, ih]

/-- **The bridge, for every thread state**: the tree is the tree of the
state with no declarations, re-resolved against the declarations, with the
declarations put back in the leaves. -/
theorem exec_underDecls (st : State) :
    isa.exec st = (isa.exec st.noDecls).map
      (fun t => (t.underDecls st.decls).map (State.withDecls st.decls)) := by
  show exec st = (exec st.noDecls).map _
  have hdir : st.noDecls.directive = st.directive := rfl
  unfold exec
  rw [hdir]
  split
  · rfl
  · rw [← toEv_underDecls st.decls]
    show some _ = some _
    congr 1
    show _ = EvTree.map (State.withDecls st.decls) (EvTree.underDecls st.decls
      (EvTree.map (fun m => ({ st with st := m, decls := {} } : State))
        (toEv {} (_root_.Executable.step st.exe st.st fun s' => .done s'))))
    rw [EvTree.map_underDecls (σ := State) (State.withDecls st.decls), evTree_map_map_vec,
      EvTree.map_underDecls]
    rfl

end Kraken.Promising.X64

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvSpike (TreeJ)

/-- **A live tree judgment of the re-resolved tree**, for strict sized
declarations: an event `ds` resolves is unchanged, any other is a fault. -/
def TreeJLive.underDecls {E : SharedEnv} {σ : Type} (J : TreeJLive E σ) (ds : Decls) (hs : ds.Sized) :
    TreeJLive E σ :=
  J.reresolve ds hs

/-- **A tree judgment of the re-resolved tree** (`TreeJLive.underDecls` for
`TreeJ`). -/
def _root_.Kraken.Promising.SLR.EnvSpike.TreeJ.underDecls {E : SharedEnv} {σ : Type} (J : TreeJ E σ)
    (ds : Decls) (hs : ds.Sized) : TreeJ E σ :=
  J.reresolve ds hs

open Kraken.Promising.X64 in
/-- **A `decls = {}` live run gives the run with strict sized
declarations**: apply the run lemma at `st.noDecls` to
`(J.comap (withDecls st.decls)).underDecls st.decls`. -/
theorem exec_treeJLive_of_underDecls {E : SharedEnv} (J : TreeJLive E X64.State) {st : X64.State} {g : E.State}
    (hs : st.decls.Sized)
    (h₀ : ∀ tree₀, isa.exec st.noDecls = some tree₀ →
      ((J.comap (State.withDecls st.decls)).underDecls st.decls hs).W tree₀ g) :
    ∀ tree, isa.exec st = some tree → J.W tree g := by
  intro tree htree
  rw [exec_underDecls] at htree
  obtain ⟨tree₀, h, rfl⟩ := Option.map_eq_some_iff.mp htree
  exact h₀ tree₀ h

open Kraken.Promising.X64 in
/-- **A `decls = {}` run gives the run with strict sized declarations**
(`exec_treeJLive_of_underDecls` for `TreeJ`). -/
theorem exec_treeJ_of_underDecls {E : SharedEnv} (J : TreeJ E X64.State) {st : X64.State} {g : E.State}
    (hs : st.decls.Sized)
    (h₀ : ∀ tree₀, isa.exec st.noDecls = some tree₀ →
      ((J.comap (State.withDecls st.decls)).underDecls st.decls hs).W tree₀ g) :
    ∀ tree, isa.exec st = some tree → J.W tree g := by
  intro tree htree
  rw [exec_underDecls] at htree
  obtain ⟨tree₀, h, rfl⟩ := Option.map_eq_some_iff.mp htree
  exact h₀ tree₀ h

/-- The `Post` of the re-resolved comapped judgment is `J.Post` at the
leaf with the declarations put back. -/
theorem underDecls_comap_post {E : SharedEnv} (J : TreeJLive E X64.State) (ds : Decls) (hs : ds.Sized)
    (s : X64.State) (g : E.State) :
    ((J.comap (X64.State.withDecls ds)).underDecls ds hs).Post s g = J.Post (X64.State.withDecls ds s) g := rfl

end Kraken.Promising.SLR.EnvG

/-! ## Tests -/

namespace Kraken.Promising

-- The `treiber_aba_tagged.kl` header's declarations: a 16-byte `head`, two
-- 8-byte nodes. Accesses at a declared footprint or an undeclared address
-- keep their event; a mixed-size one faults.
/--
info: ["load 0x0000000000001000/16 = 0x00000000000000000000000000000000", "done",
  "load 0x0000000000002000/8 = 0x00000000000000000000000000000000", "done",
  "fault: mixed-size access: 8 bytes at 0x0000000000001000, declared 16 bytes",
  "fault: mixed-size access: 8 bytes at 0x0000000000001008 overlaps the location of 16 bytes at 0x0000000000001000",
  "load 0x0000000000005000/8 = 0x00000000000000000000000000000000", "done"]
-/
#guard_msgs in
#eval
  let ds : Decls := { locs := [⟨0x1000, 16⟩, ⟨0x2000, 8⟩, ⟨0x2008, 8⟩] }
  let ld (a : BitVec 64) (n : Nat) : EvTree Unit := .load .plain false ⟨a, n⟩ fun _ => .done ()
  [ld 0x1000 16, ld 0x2000 8, ld 0x1000 8, ld 0x1008 8, ld 0x5000 8].flatMap fun t =>
    X64.showRun [] (t.underDecls ds)

end Kraken.Promising
