/-
**Declarations as a fault restriction: the ISA-neutral part**. ISA-neutral
(imports neither `Syntax`).

The AArch64 declarations bridge (`EnvG/A64DeclsBridge.lean`) needs the
ISA-neutral half of the x64 vector proofs' `EnvG/X64VecDeclsFault.lean`, which that file
keeps beside x64 code (it imports `X64VecDecls`, so an AArch64 file cannot
import it). The statements are the x64 vector proofs' verbatim, under neutral names:

| here | `X64VecDeclsFault` |
|---|---|
| `Decls.StrictSized` | `Decls.Sized` |
| `Decls.resolve_ok_of_strictSized` | `Decls.resolve_ok_of_sized` |
| `EvTree.reresolve` | `EvTree.underDecls` |
| `EvTree.map_access_reresolve` | `EvTree.map_access` |
| `EvTree.map_reresolve` | `EvTree.map_underDecls` |
| `TreeJLive.reresolve` | `TreeJLive.underDecls` |
| `TreeJ.reresolve` | `TreeJ.underDecls` |
| `reresolve_access_cases` | `X64DeclsLink.underDecls_access_cases` |
| `accessFree_reresolve`, `detAccess_reresolve`, `singleAccessS2_reresolve`, `phase1ShapeF_reresolve` | `X64VecDeclsLinkAdj.*_underDecls` |
| `singleAccessS_reresolveS`, `singleAccessS2_reresolveS`, `phase1Shape_reresolve`, `phase1ShapeR_reresolve` | `X64DeclsLink.*_underDeclsD` |

Done. `X64VecDeclsFault` imports this file; the x64 names are now
the instances of these (the definitions plain `def`s unfolding to these, the theorems
re-proved from these, every statement unchanged), and so are the twin shape
lemmas of `X64VecDeclsLinkAdj` and `X64DeclsLink`.

- **Strict sized declarations** (`Decls.StrictSized`): strict mode
  (`unsizedDefault = false`) and no unsized declaration — the `.kl` runner's
  declarations of a typed header. Under them an access that resolves
  resolves to its own footprint (`Decls.resolve_ok_of_strictSized`).
- `EvTree.reresolve ds t` re-resolves every event of `t` against `ds`
  (`EvTree.access`): an event `ds` resolves keeps its location, any other
  becomes `ds`'s mixed-size fault. It commutes with `map`.
- `TreeJLive.reresolve` / `TreeJ.reresolve`: a tree judgment of the
  re-resolved tree, for strict sized declarations (a fault is a `W` law).
- The phase-1 shapes are kept by `reresolve` under strict sized
  declarations (`phase1Shape_reresolve`, `phase1ShapeR_reresolve`,
  `phase1ShapeF_reresolve`).
-/
import Kraken.Promising.SLR.EnvG.Live
import Kraken.Promising.SLR.EnvG.Phase1
import Kraken.Promising.SLR.EnvG.RmwFailRuleLink
import Kraken.Promising.SLR.EnvG.TreeMap

namespace Kraken.Promising

/-- **Strict sized declarations**: strict mode (`unsizedDefault = false`) and
no unsized declaration. The `.kl` runner's declarations of a header with
sized types only (`X64VecDeclsFault.Decls.Sized`). -/
def Decls.StrictSized (ds : Decls) : Prop := ds.unsizedDefault = false ∧ ∀ l ∈ ds.locs, l.bytes ≠ 0

/-- **Under strict sized declarations an access that resolves resolves to
its own footprint.** -/
theorem Decls.resolve_ok_of_strictSized {ds : Decls} (hs : ds.StrictSized) {a : BitVec 64} {n : Nat} {l : Loc}
    (h : ds.resolve a n = .ok l) : l = ⟨a, n⟩ := by
  unfold Decls.resolve at h
  split at h
  · next l₀ hf =>
    have ha : l₀.addr = a := by simpa using List.find?_some hf
    have hb : l₀.bytes ≠ 0 := hs.2 _ (List.mem_of_find?_eq_some hf)
    by_cases hn : l₀.bytes = n
    · simp only [hn, beq_self_eq_true, ↓reduceIte, Except.ok.injEq] at h
      subst h; cases l₀; simp_all
    · have hn' : (l₀.bytes == n) = false := by simpa using hn
      have hb' : (l₀.bytes == 0) = false := by simpa using hb
      simp only [hn', hb', Bool.false_eq_true, ↓reduceIte] at h
      cases h
  · split at h
    · cases h
    · simp only [hs.1, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
      exact h.symm

namespace EvTree

/-- **Re-resolve every event against `ds`**: an event at `l` becomes the
event at the location `ds` resolves `l`'s access to, or `ds`'s fault
(`X64VecDeclsFault.EvTree.underDecls`). -/
def reresolve {σ : Type} (ds : Decls) : EvTree σ → EvTree σ
  | .done s => .done s
  | .fault m => .fault m
  | .choose n k => .choose n fun i => reresolve ds (k i)
  | .load k x l ret => .access ds l.addr l.bytes fun l' => .load k x l' fun v => reresolve ds (ret v)
  | .store k x l v ret => .access ds l.addr l.bytes fun l' => .store k x l' v fun b => reresolve ds (ret b)
  | .rmw k nr l op ret => .access ds l.addr l.bytes fun l' => .rmw k nr l' op fun v => reresolve ds (ret v)
  | .fence k ret => .fence k fun u => reresolve ds (ret u)

theorem map_access_reresolve {σ τ : Type} (f : σ → τ) (ds : Decls) (a : BitVec 64) (n : Nat)
    (k : Loc → EvTree σ) : (EvTree.access ds a n k).map f = EvTree.access ds a n fun l => (k l).map f := by
  unfold EvTree.access; split <;> rfl

/-- `reresolve` commutes with `map`. -/
theorem map_reresolve {σ τ : Type} (f : σ → τ) (ds : Decls) :
    ∀ t : EvTree σ, (t.reresolve ds).map f = (t.map f).reresolve ds
  | .done _ => rfl
  | .fault _ => rfl
  | .choose _ k => by
    simp only [reresolve, map]; congr 1; funext i; exact map_reresolve f ds (k i)
  | .load _ _ _ ret => by
    simp only [reresolve, map, map_access_reresolve]; congr 1; funext l; congr 1; funext v
    exact map_reresolve f ds (ret v)
  | .store _ _ _ _ ret => by
    simp only [reresolve, map, map_access_reresolve]; congr 1; funext l; congr 1; funext v
    exact map_reresolve f ds (ret v)
  | .rmw _ _ _ _ ret => by
    simp only [reresolve, map, map_access_reresolve]; congr 1; funext l; congr 1; funext v
    exact map_reresolve f ds (ret v)
  | .fence _ ret => by
    simp only [reresolve, map]; congr 1; funext u; exact map_reresolve f ds (ret u)

end EvTree

end Kraken.Promising

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvSpike (TreeJ)

/-! ## Tree judgments of the re-resolved tree -/

/-- **A live tree judgment of the re-resolved tree**, for strict sized
declarations: an event `ds` resolves is unchanged, any other is a fault
(`X64VecDeclsFault.TreeJLive.underDecls`). -/
def TreeJLive.reresolve {E : SharedEnv} {σ : Type} (J : TreeJLive E σ) (ds : Decls) (hs : ds.StrictSized) :
    TreeJLive E σ where
  W t g := J.W (t.reresolve ds) g
  Post := J.Post
  done h := J.done h
  fault := J.fault
  choose h := J.choose h
  load {k xcl addr n ret g} h₁ h₂ := by
    show J.W (EvTree.access ds addr n _) g
    unfold EvTree.access
    split
    · next l hl => obtain rfl := Decls.resolve_ok_of_strictSized hs hl; exact J.load h₁ h₂
    · exact J.fault
  store {k xcl addr n v ret g} h₁ h₂ := by
    show J.W (EvTree.access ds addr n _) g
    unfold EvTree.access
    split
    · next l hl => obtain rfl := Decls.resolve_ok_of_strictSized hs hl; exact J.store h₁ h₂
    · exact J.fault
  rmw {k addr n op ret g} h₁ h₂ := by
    show J.W (EvTree.access ds addr n _) g
    unfold EvTree.access
    split
    · next l hl => obtain rfl := Decls.resolve_ok_of_strictSized hs hl; exact J.rmw h₁ h₂
    · exact J.fault
  fence h₁ h₂ := J.fence h₁ h₂

/-- **A tree judgment of the re-resolved tree** (`TreeJLive.reresolve` for
`TreeJ`; `X64VecDeclsFault.TreeJ.underDecls`). -/
def _root_.Kraken.Promising.SLR.EnvSpike.TreeJ.reresolve {E : SharedEnv} {σ : Type} (J : TreeJ E σ)
    (ds : Decls) (hs : ds.StrictSized) : TreeJ E σ where
  W t g := J.W (t.reresolve ds) g
  Post := J.Post
  done h := J.done h
  fault := J.fault
  choose h := J.choose h
  load {k xcl addr n ret g} h₁ h₂ := by
    show J.W (EvTree.access ds addr n _) g
    unfold EvTree.access
    split
    · next l hl => obtain rfl := Decls.resolve_ok_of_strictSized hs hl; exact J.load h₁ h₂
    · exact J.fault
  store {k xcl addr n v ret g} h₁ h₂ := by
    show J.W (EvTree.access ds addr n _) g
    unfold EvTree.access
    split
    · next l hl => obtain rfl := Decls.resolve_ok_of_strictSized hs hl; exact J.store h₁ h₂
    · exact J.fault
  rmw {k nr addr n op ret g} h₁ h₂ := by
    show J.W (EvTree.access ds addr n _) g
    unfold EvTree.access
    split
    · next l hl => obtain rfl := Decls.resolve_ok_of_strictSized hs hl; exact J.rmw h₁ h₂
    · exact J.fault
  fence h₁ h₂ := J.fence h₁ h₂

/-! ## Tree shapes under `reresolve` -/

section Shapes

variable {σ : Type} {ds : Decls}

/-- `reresolve` keeps an access-free tree access-free. -/
theorem accessFree_reresolve (ds : Decls) : ∀ t : EvTree σ, AccessFree t → AccessFree (t.reresolve ds)
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => accessFree_reresolve ds (k i) (h i)
  | .fence _ ret, h => accessFree_reresolve ds (ret ()) h
  | .load .., h => h.elim
  | .store .., h => h.elim
  | .rmw .., h => h.elim

/-- `reresolve` keeps deterministic access. -/
theorem detAccess_reresolve (ds : Decls) : ∀ t : EvTree σ, DetAccess t → DetAccess (t.reresolve ds)
  | .done _, h => h
  | .fault _, h => h
  | .choose _ k, h => fun i => accessFree_reresolve ds (k i) (h i)
  | .fence _ ret, h => detAccess_reresolve ds (ret ()) h
  | .load _ _ l _, _ => by
    show DetAccess (EvTree.access ds l.addr l.bytes _)
    unfold EvTree.access; split <;> trivial
  | .store _ _ l _ _, _ => by
    show DetAccess (EvTree.access ds l.addr l.bytes _)
    unfold EvTree.access; split <;> trivial
  | .rmw _ _ l _ _, _ => by
    show DetAccess (EvTree.access ds l.addr l.bytes _)
    unfold EvTree.access; split <;> trivial

/-- `reresolve` keeps the unconstrained single-access shape (any
declarations). -/
theorem singleAccessS2_reresolve (ds : Decls) :
    ∀ t : EvTree σ, SingleAccessS2 True (fun _ _ => True) (fun _ _ _ => True) True t →
      SingleAccessS2 True (fun _ _ => True) (fun _ _ _ => True) True (t.reresolve ds)
  | .done _, h => h
  | .fault _, h => h
  | .choose _ k, h => fun i => singleAccessS2_reresolve ds (k i) (h i)
  | .fence _ ret, h => singleAccessS2_reresolve ds (ret ()) h
  | .load _ _ l ret, h => by
    show SingleAccessS2 _ _ _ _ (EvTree.access ds l.addr l.bytes _)
    unfold EvTree.access; split
    · exact ⟨trivial, fun v => accessFree_reresolve ds (ret v) (h.2 v)⟩
    · trivial
  | .store _ _ l _ ret, h => by
    show SingleAccessS2 _ _ _ _ (EvTree.access ds l.addr l.bytes _)
    unfold EvTree.access; split
    · exact ⟨trivial, fun b => accessFree_reresolve ds (ret b) (h.2 b)⟩
    · trivial
  | .rmw _ _ l _ ret, h => by
    show SingleAccessS2 _ _ _ _ (EvTree.access ds l.addr l.bytes _)
    unfold EvTree.access; split
    · exact ⟨trivial, fun v => accessFree_reresolve ds (ret v) (h.2 v)⟩
    · trivial

/-- `reresolve` keeps the `F` phase-1 shape (any declarations). -/
theorem phase1ShapeF_reresolve (ds : Decls) (t : EvTree σ) (h : Phase1ShapeF t) :
    Phase1ShapeF (t.reresolve ds) :=
  ⟨detAccess_reresolve ds t h.1, singleAccessS2_reresolve ds t h.2⟩

/-- Under strict sized declarations, re-resolving an event keeps it or makes
it a fault. -/
theorem reresolve_access_cases (hs : ds.StrictSized) (l : Loc) (k : Loc → EvTree σ) :
    EvTree.access ds l.addr l.bytes k = k l ∨ ∃ m, EvTree.access ds l.addr l.bytes k = .fault m := by
  unfold EvTree.access
  split
  · next l' hl =>
    obtain rfl := Decls.resolve_ok_of_strictSized hs hl
    exact .inl (by cases l; rfl)
  · exact .inr ⟨_, rfl⟩

theorem singleAccessS_reresolveS (hs : ds.StrictSized) {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop}
    {D : Prop} : ∀ {t : EvTree σ}, SingleAccessS Lok Sok Rok D t → SingleAccessS Lok Sok Rok D (t.reresolve ds)
  | .done _, h => h
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => singleAccessS_reresolveS hs (t := k i) (h i)
  | .fence _ ret, h => singleAccessS_reresolveS hs (t := ret ()) h
  | .load k x l ret, h => by
    show SingleAccessS Lok Sok Rok D (EvTree.access ds l.addr l.bytes _)
    rcases reresolve_access_cases hs l (fun l' => .load k x l' fun v => (ret v).reresolve ds) with h' | ⟨m, h'⟩ <;>
      rw [h']
    · exact ⟨h.1, fun v => accessFree_reresolve ds _ (h.2 v)⟩
    · trivial
  | .store k x l v ret, h => by
    show SingleAccessS Lok Sok Rok D (EvTree.access ds l.addr l.bytes _)
    rcases reresolve_access_cases hs l (fun l' => .store k x l' v fun b => (ret b).reresolve ds) with h' | ⟨m, h'⟩ <;>
      rw [h']
    · exact ⟨h.1, fun b => accessFree_reresolve ds _ (h.2 b)⟩
    · trivial
  | .rmw k nr l op ret, h => by
    show SingleAccessS Lok Sok Rok D (EvTree.access ds l.addr l.bytes _)
    rcases reresolve_access_cases hs l (fun l' => .rmw k nr l' op fun v => (ret v).reresolve ds) with h' | ⟨m, h'⟩ <;>
      rw [h']
    · exact ⟨h.1, fun v => accessFree_reresolve ds _ (h.2 v)⟩
    · trivial

theorem singleAccessS2_reresolveS (hs : ds.StrictSized) {Lok : Prop} {Sok : Loc → Val → Prop}
    {Rok : RmwKind → Loc → (Val → Option Val) → Prop} {D : Prop} :
    ∀ {t : EvTree σ}, SingleAccessS2 Lok Sok Rok D t → SingleAccessS2 Lok Sok Rok D (t.reresolve ds)
  | .done _, h => h
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => singleAccessS2_reresolveS hs (t := k i) (h i)
  | .fence _ ret, h => singleAccessS2_reresolveS hs (t := ret ()) h
  | .load k x l ret, h => by
    show SingleAccessS2 Lok Sok Rok D (EvTree.access ds l.addr l.bytes _)
    rcases reresolve_access_cases hs l (fun l' => .load k x l' fun v => (ret v).reresolve ds) with h' | ⟨m, h'⟩ <;>
      rw [h']
    · exact ⟨h.1, fun v => accessFree_reresolve ds _ (h.2 v)⟩
    · trivial
  | .store k x l v ret, h => by
    show SingleAccessS2 Lok Sok Rok D (EvTree.access ds l.addr l.bytes _)
    rcases reresolve_access_cases hs l (fun l' => .store k x l' v fun b => (ret b).reresolve ds) with h' | ⟨m, h'⟩ <;>
      rw [h']
    · exact ⟨h.1, fun b => accessFree_reresolve ds _ (h.2 b)⟩
    · trivial
  | .rmw k nr l op ret, h => by
    show SingleAccessS2 Lok Sok Rok D (EvTree.access ds l.addr l.bytes _)
    rcases reresolve_access_cases hs l (fun l' => .rmw k nr l' op fun v => (ret v).reresolve ds) with h' | ⟨m, h'⟩ <;>
      rw [h']
    · exact ⟨h.1, fun v => accessFree_reresolve ds _ (h.2 v)⟩
    · trivial

theorem phase1Shape_reresolve (hs : ds.StrictSized) {A : Arch} {t : EvTree σ} (h : Phase1Shape A t) :
    Phase1Shape A (t.reresolve ds) :=
  ⟨detAccess_reresolve ds _ h.1, singleAccessS_reresolveS hs h.2⟩

theorem phase1ShapeR_reresolve (hs : ds.StrictSized) {A : Arch} {t : EvTree σ} (h : Phase1ShapeR A t) :
    Phase1ShapeR A (t.reresolve ds) :=
  ⟨detAccess_reresolve ds _ h.1, singleAccessS2_reresolveS hs h.2⟩

end Shapes

end Kraken.Promising.SLR.EnvG

/-! ## Tests -/

namespace Kraken.Promising

-- Declarations of a typed header: an 8-byte `top`, a 4-byte node word.
-- Accesses at a declared footprint or an undeclared address keep their
-- event; a mixed-size one faults.
/--
info: ["load 0x0000000000001000#64/8", "load 0x0000000000001100#64/4",
  "fault: mixed-size access: 4 bytes at 0x0000000000001000, declared 8 bytes", "load 0x0000000000001108#64/8"]
-/
#guard_msgs in
#eval
  let ds : Decls := { locs := [⟨0x1000, 8⟩, ⟨0x1100, 4⟩], unsizedDefault := false }
  let ld (a : BitVec 64) (n : Nat) : EvTree Unit := .load .plain false ⟨a, n⟩ fun _ => .done ()
  let show1 : EvTree Unit → String
    | .load _ _ l _ => s!"load {l.addr}/{l.bytes}"
    | .fault m => s!"fault: {m}"
    | _ => "other"
  [ld 0x1000 8, ld 0x1100 4, ld 0x1000 4, ld 0x1108 8].map fun t => show1 (t.reresolve ds)

end Kraken.Promising
