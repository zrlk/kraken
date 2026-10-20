/-
**No fault at the runner's declarations: the ISA-neutral core**.
ISA-neutral (imports neither `Syntax`); imported by `EnvG/X64VecDecls.lean`,
`EnvG/X64NoFaultD.lean` and `EnvG/A64NoFaultDCommon.lean`.

The no-fault-at-declarations proofs (x64) and the AArch64
no-fault-at-declarations proofs (AArch64) proved the same tree facts twice,
because the no-fault-at-declarations proofs' file imports x64 code. The originals moved here, same
names and statements:

- from `X64VecDecls`: `Decls.AgreesAt`, `Decls.agreesAt_empty`,
  `EvTree.access_of_agreesAt`;
- from `X64NoFaultD`: `Decls.AgreesOn`, `EvTree.RootInS`, `EvTree.RootOnlyD`,
  `accessFree_mapD`, `rootOnlyD_map`, `rootOnlyD_of_singleAccessS(2)`,
  `atLocD_of_accessFree`, `rootSameD_of_rootOnlyD`;
- from `A64NoFaultDCommon`: `noFault_reresolve_accessFree`.

New, generic over `EvTree.reresolve` (the AArch64 declarations proofs' re-resolution, of which
x64's `EvTree.underDecls` is the instance): `noFault_reresolve_atLocD` and
`noFault_reresolve_rootSameD`. `X64NoFaultD`'s `noFault_underDecls_*` lemmas
and `A64NoFaultDCommon`'s `noFault_reresolve_rootD` are their instances, and
`A64NoFaultDCommon`'s twins (`Decls.AgreesAtA`, `Decls.AgreesOnA`,
`EvTree.RootInSA`, `EvTree.RootOnlyDA`, …) are now defined from the
originals here.
-/
import Kraken.Promising.SLR.EnvG.A64DeclsCommon
import Kraken.Promising.SLR.EnvG.X64NoFaultDSame

namespace Kraken.Promising

/-- **`ds` resolves an `n`-byte access at `a` to its own footprint**, as no
declarations do (`Decls.resolve_empty`). -/
def Decls.AgreesAt (ds : Decls) (a : BitVec 64) (n : Nat) : Prop := ds.resolve a n = .ok ⟨a, n⟩

/-- No declarations agree everywhere. -/
theorem Decls.agreesAt_empty (a : BitVec 64) (n : Nat) : Decls.AgreesAt {} a n := rfl

/-- At an agreeing address an access builds the same event under `ds` as
under `{}`. -/
theorem EvTree.access_of_agreesAt {σ : Type} {ds : Decls} {a : BitVec 64} {n : Nat} (h : ds.AgreesAt a n)
    (k : Loc → EvTree σ) : EvTree.access ds a n k = EvTree.access {} a n k := by
  rw [EvTree.access_empty]
  unfold EvTree.access
  rw [show ds.resolve a n = .ok ⟨a, n⟩ from h]

/-- **`ds` resolves every location of `S` to itself.** -/
def Decls.AgreesOn (ds : Decls) (S : SharedEnv.Layout) : Prop := ∀ p ∈ S, ds.AgreesAt p.1 p.2

namespace EvTree

/-- **The root accesses are `S`-locations**: every access reached through
`choose` and fences only. -/
def RootInS (S : SharedEnv.Layout) {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, RootInS S (k i)
  | .fence _ ret => RootInS S (ret ())
  | .load _ _ l _ => (l.addr, l.bytes) ∈ S
  | .store _ _ l _ _ => (l.addr, l.bytes) ∈ S
  | .rmw _ _ l _ _ => (l.addr, l.bytes) ∈ S

/-- **Single access**: no access after an access. -/
def RootOnlyD {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, RootOnlyD (k i)
  | .fence _ ret => RootOnlyD (ret ())
  | .load _ _ _ ret => ∀ v, SLR.EnvG.AccessFree (ret v)
  | .store _ _ _ _ ret => ∀ b, SLR.EnvG.AccessFree (ret b)
  | .rmw _ _ _ _ ret => ∀ v, SLR.EnvG.AccessFree (ret v)

end EvTree

end Kraken.Promising


namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {σ : Type}

theorem accessFree_mapD {τ : Type} (f : σ → τ) : ∀ t : EvTree σ, AccessFree t → AccessFree (t.map f)
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => accessFree_mapD f (k i) (h i)
  | .fence _ ret, h => accessFree_mapD f (ret ()) h
  | .load .., h => h.elim
  | .store .., h => h.elim
  | .rmw .., h => h.elim

theorem rootOnlyD_map {τ : Type} (f : σ → τ) : ∀ t : EvTree σ, t.RootOnlyD → (t.map f).RootOnlyD
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => rootOnlyD_map f (k i) (h i)
  | .fence _ ret, h => rootOnlyD_map f (ret ()) h
  | .load _ _ _ ret, h => fun v => accessFree_mapD f (ret v) (h v)
  | .store _ _ _ _ ret, h => fun b => accessFree_mapD f (ret b) (h b)
  | .rmw _ _ _ _ ret, h => fun v => accessFree_mapD f (ret v) (h v)

theorem rootOnlyD_of_singleAccessS {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop} {D : Prop} :
    ∀ t : EvTree σ, SingleAccessS Lok Sok Rok D t → t.RootOnlyD
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => rootOnlyD_of_singleAccessS (k i) (h i)
  | .fence _ ret, h => rootOnlyD_of_singleAccessS (ret ()) h
  | .load .., h => h.2
  | .store .., h => h.2
  | .rmw .., h => h.2

theorem rootOnlyD_of_singleAccessS2 {Lok : Prop} {Sok : Loc → Val → Prop}
    {Rok : RmwKind → Loc → (Val → Option Val) → Prop} {D : Prop} :
    ∀ t : EvTree σ, SingleAccessS2 Lok Sok Rok D t → t.RootOnlyD
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => rootOnlyD_of_singleAccessS2 (k i) (h i)
  | .fence _ ret, h => rootOnlyD_of_singleAccessS2 (ret ()) h
  | .load .., h => h.2
  | .store .., h => h.2
  | .rmw .., h => h.2

theorem atLocD_of_accessFree (l : Loc) : ∀ t : EvTree σ, AccessFree t → t.AtLocD l
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => atLocD_of_accessFree l (k i) (h i)
  | .fence _ ret, h => atLocD_of_accessFree l (ret ()) h
  | .load .., h => h.elim
  | .store .., h => h.elim
  | .rmw .., h => h.elim

/-- A single-access tree repeats its root's location (vacuously). -/
theorem rootSameD_of_rootOnlyD : ∀ t : EvTree σ, t.RootOnlyD → t.RootSameD
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => rootSameD_of_rootOnlyD (k i) (h i)
  | .fence _ ret, h => rootSameD_of_rootOnlyD (ret ()) h
  | .load _ _ l ret, h => fun v => atLocD_of_accessFree l (ret v) (h v)
  | .store _ _ l _ ret, h => fun b => atLocD_of_accessFree l (ret b) (h b)
  | .rmw _ _ l _ ret, h => fun v => atLocD_of_accessFree l (ret v) (h v)

/-- An access-free fault-free tree stays fault-free re-resolved
(generic form of `X64NoFaultD.noFault_underDecls_accessFreeD`). -/
theorem noFault_reresolve_accessFree (ds : Decls) :
    ∀ t : EvTree σ, AccessFree t → t.NoFault → (t.reresolve ds).NoFault
  | .done _, _, _ => trivial
  | .fault _, _, h => h.elim
  | .choose _ k, ha, h => ⟨h.1, fun i => noFault_reresolve_accessFree ds (k i) (ha i) (h.2 i)⟩
  | .fence _ ret, ha, h => noFault_reresolve_accessFree ds (ret ()) ha h
  | .load .., ha, _ => ha.elim
  | .store .., ha, _ => ha.elim
  | .rmw .., ha, _ => ha.elim

/-- **A fault-free tree all of whose accesses are at an agreeing location
stays fault-free re-resolved** (the generic form of
`X64NoFaultD.noFault_underDecls_atLocD`). -/
theorem noFault_reresolve_atLocD {ds : Decls} {l : Loc} (hl : ds.AgreesAt l.addr l.bytes) :
    ∀ t : EvTree σ, t.AtLocD l → t.NoFault → (t.reresolve ds).NoFault
  | .done _, _, _ => trivial
  | .fault _, _, h => h.elim
  | .choose _ k, ha, h => ⟨h.1, fun i => noFault_reresolve_atLocD hl (k i) (ha i) (h.2 i)⟩
  | .fence _ ret, ha, h => noFault_reresolve_atLocD hl (ret ()) ha h
  | .load _ _ l' ret, ha, h => by
    obtain ⟨rfl, ha⟩ := ha
    show (EvTree.access ds l'.addr l'.bytes _).NoFault
    rw [EvTree.access_of_agreesAt hl, EvTree.access_empty]
    exact fun v => noFault_reresolve_atLocD hl (ret v) (ha v) (h v)
  | .store _ _ l' _ ret, ha, h => by
    obtain ⟨rfl, ha⟩ := ha
    show (EvTree.access ds l'.addr l'.bytes _).NoFault
    rw [EvTree.access_of_agreesAt hl, EvTree.access_empty]
    exact fun b => noFault_reresolve_atLocD hl (ret b) (ha b) (h b)
  | .rmw _ _ l' _ ret, ha, h => by
    obtain ⟨rfl, ha⟩ := ha
    show (EvTree.access ds l'.addr l'.bytes _).NoFault
    rw [EvTree.access_of_agreesAt hl, EvTree.access_empty]
    exact fun v => noFault_reresolve_atLocD hl (ret v) (ha v) (h v)

/-- **A fault-free tree whose root accesses are `S`-locations and whose later
accesses repeat the root's location stays fault-free re-resolved against
declarations agreeing on `S`** (the generic form of
`X64NoFaultD.noFault_underDecls_rootSameD` and of
`A64NoFaultDCommon.noFault_reresolve_rootD`). -/
theorem noFault_reresolve_rootSameD {ds : Decls} {S : SharedEnv.Layout} (hag : ds.AgreesOn S) :
    ∀ t : EvTree σ, t.RootInS S → t.RootSameD → t.NoFault → (t.reresolve ds).NoFault
  | .done _, _, _, _ => trivial
  | .fault _, _, _, h => h.elim
  | .choose _ k, hi, ho, h => ⟨h.1, fun i => noFault_reresolve_rootSameD hag (k i) (hi i) (ho i) (h.2 i)⟩
  | .fence _ ret, hi, ho, h => noFault_reresolve_rootSameD hag (ret ()) hi ho h
  | .load _ _ l ret, hi, ho, h => by
    show (EvTree.access ds l.addr l.bytes _).NoFault
    rw [EvTree.access_of_agreesAt (hag _ hi), EvTree.access_empty]
    exact fun v => noFault_reresolve_atLocD (hag _ hi) (ret v) (ho v) (h v)
  | .store _ _ l _ ret, hi, ho, h => by
    show (EvTree.access ds l.addr l.bytes _).NoFault
    rw [EvTree.access_of_agreesAt (hag _ hi), EvTree.access_empty]
    exact fun b => noFault_reresolve_atLocD (hag _ hi) (ret b) (ho b) (h b)
  | .rmw _ _ l _ ret, hi, ho, h => by
    show (EvTree.access ds l.addr l.bytes _).NoFault
    rw [EvTree.access_of_agreesAt (hag _ hi), EvTree.access_empty]
    exact fun v => noFault_reresolve_atLocD (hag _ hi) (ret v) (ho v) (h v)

end Kraken.Promising.SLR.EnvG
