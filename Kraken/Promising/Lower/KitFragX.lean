/-
**The x64 kit's `main` and `pure` straight from
fragment specifications** (the `Arch.tso` twin of the fragment kit's
`Lower/KitFrag.lean` and the purity kit's `Lower/FragKitPure.lean`). Generic (no
pilot-specific names). ISA: x64; machine: the
executable machine's per-thread environment semantics
(`Executable.instrStepEnv`), partial correctness (`Safely`).

The x64 kit (`Lower/KitX64.lean`) takes per thread `Safely` judgments of the
laid-out image `e` from an entry address `entry` to a counted post holding
only at the end address `endPc` (`LowerThreadX.main`, `LowerCoreX.pure`), not
whole-text partial triples. A placement-independent x64 spec
`FragSpecEnvL env frags l FPre FPost` (`Lower/FragSpecCallsX64.lean`) of the
thread's entry function gives that form at every image that

- places a text `q` (`Program.Placed q m₀` in the image's `CodeEnv`; for a
  laid-out closed text `Program.placed_of_layout`, all `by decide`/`rfl`)
  holding every fragment's blocks (`Program.subBlocksOfE`, decidable), and
- has the entry at `l`'s address (`hentry`, `rfl` in practice),

with the **return address read as the end address** `endPc`: `hpre` (the
kit's precondition gives `FPre` at `ra = endPc`; under the stackless
register-link convention, `Lower/KitX64Link.lean`, this is the link register
`r11` holding `endPc`) and `hpost` (`FPost` at `endPc` gives the kit's post at
`endPc`). Unlike the AArch64 bridge, the entry need not be the text's first
label and the end need not be the text's end: one text may hold several
threads' entries (the x64 MS queue pilot's `main_e`/`main_d`).

- `safely_of_fragL`: the bridge, for every environment (so the same lemma
  serves `EnvGCAdjX`, `EnvGCAdjXV` and the relPure environment of `pure`).
- `LowerThreadX.ofFrag`, `LowerThreadXV.ofFrag`: a `LowerCoreX` plus a
  fragment spec of the entry function is a lowered thread.
- `LowerStaticX` (the fields of `LowerCoreX` without the purity judgment)
  and `LowerStaticX.ofFragPure`: the purity judgment from a relPure fragment
  spec of the entry function.
-/
import Kraken.Promising.Lower.KitX64
import Kraken.Promising.Lower.FragSpecCallsX64

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.KitX

/-- **The kit's `Safely` form from a fragment spec of the entry function.**
In an ambient code placing a text `q` that holds the fragments `frags`, the
spec of the function at `l`, with its return address read as `ra`, gives the
run from `l`'s address into `Q` at `ra`. Any environment. -/
theorem safely_of_fragL [CodeEnv] {env : SharedEnv} {frags : List Program} {q : Program} {l m₀ : Label}
    {FPre : Int64 → MachineData → env.State → Prop}
    {FPost : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnvL env frags l FPre FPost) (hq : Program.Placed q m₀)
    (hs : frags.all (fun p => Program.subBlocksOfE p q) = true)
    {ra : Int64} {Pre : MachineData → env.State → Prop} {Q : MachineState × env.State → Prop}
    (hpre : ∀ s g, Pre s g → FPre ra s g)
    (hpost : ∀ s g s' g', Pre s g → FPost ra s g s' g' → Q ((s', ra), g')) :
    ∀ s g, Pre s g → Safely (cenv.instrStepEnv env) Q ((s, (_root_.Executable.labels cenv).label l), g) := by
  intro s g hP
  refine ((h.of_placed hq hs) ra s g (hpre s g hP)).mono fun x ⟨hx, hp⟩ => ?_
  obtain ⟨⟨s', a⟩, g'⟩ := x
  dsimp only at hx hp
  subst hx
  exact hpost s g s' g' hP hp

/-- `safely_of_fragL` at an image `e` with the entry `entry` at `l`'s
address and the return address read as `endPc` (the shape of the kit's
fields). -/
theorem safely_of_fragL_at {e : Kraken.Executable Directive} {env : SharedEnv} {frags : List Program}
    {q : Program} {l m₀ : Label} {FPre : Int64 → MachineData → env.State → Prop}
    {FPost : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnvL env frags l FPre FPost) (hq : @Program.Placed ⟨e⟩ q m₀)
    (hs : frags.all (fun p => Program.subBlocksOfE p q) = true)
    {entry endPc : Int64} (hentry : entry = (_root_.Executable.labels e).label l)
    {Pre : MachineData → env.State → Prop} {Q : MachineState × env.State → Prop}
    (hpre : ∀ s g, Pre s g → FPre endPc s g)
    (hpost : ∀ s g s' g', Pre s g → FPost endPc s g s' g' → Q ((s', endPc), g')) :
    ∀ s g, Pre s g → Safely (e.instrStepEnv env) Q ((s, entry), g) := by
  subst hentry
  exact @safely_of_fragL ⟨e⟩ env frags q l m₀ FPre FPost h hq hs endPc Pre Q hpre hpost

/-! ## `main` from a fragment spec -/

/-- **A frameless lowered x64 thread from a fragment spec of its entry
function**: the `LowerCoreX` `C`, the kit's `Pre`, and the entry function's
spec in `counted (EnvGCAdjX Arch.tso tid C.pl S)` over fragments held by a
text `q` placed in `C.e`, with the entry at `l`'s address and the return
address read as `C.endPc` (`safely_of_fragL_at`). -/
noncomputable def LowerThreadX.ofFrag {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    (C : LowerCoreX tid S B) {frags : List Program} {q : Program} {l m₀ : Label}
    {FPre : Int64 → MachineData → (SharedEnv.counted (EnvGCAdjX Arch.tso tid C.pl S)).State → Prop}
    {FPost : Int64 → MachineData → (SharedEnv.counted (EnvGCAdjX Arch.tso tid C.pl S)).State → MachineData →
      (SharedEnv.counted (EnvGCAdjX Arch.tso tid C.pl S)).State → Prop}
    (h : FragSpecEnvL (SharedEnv.counted (EnvGCAdjX Arch.tso tid C.pl S)) frags l FPre FPost)
    (hq : @Program.Placed ⟨C.e⟩ q m₀) (hs : frags.all (fun p => Program.subBlocksOfE p q) = true)
    (hentry : C.entry = (_root_.Executable.labels C.e).label l)
    (Pre : MachineData → (SharedEnv.counted (EnvGCAdjX Arch.tso tid C.pl S)).State → Prop)
    (hpre : ∀ s g, Pre s g → FPre C.endPc s g)
    (hpost : ∀ s g s' g', Pre s g → FPost C.endPc s g s' g' → C.Q ((s', C.endPc), g')) :
    LowerThreadX tid S B :=
  { C with
    Pre := Pre
    main := safely_of_fragL_at h hq hs hentry hpre hpost }

/-- **The frame + value-bridge variant**: the entry function's spec in the
value-restricted `counted (EnvGCAdjXV Arch.tso tid C.pl S G)`, and the value
judgment. -/
noncomputable def LowerThreadXV.ofFrag {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    {G : Loc → Val → Prop} (C : LowerCoreX tid S B) {frags : List Program} {q : Program} {l m₀ : Label}
    {FPre : Int64 → MachineData → (SharedEnv.counted (Vals.EnvGCAdjXV Arch.tso tid C.pl S G)).State → Prop}
    {FPost : Int64 → MachineData → (SharedEnv.counted (Vals.EnvGCAdjXV Arch.tso tid C.pl S G)).State →
      MachineData → (SharedEnv.counted (Vals.EnvGCAdjXV Arch.tso tid C.pl S G)).State → Prop}
    (h : FragSpecEnvL (SharedEnv.counted (Vals.EnvGCAdjXV Arch.tso tid C.pl S G)) frags l FPre FPost)
    (hq : @Program.Placed ⟨C.e⟩ q m₀) (hs : frags.all (fun p => Program.subBlocksOfE p q) = true)
    (hentry : C.entry = (_root_.Executable.labels C.e).label l)
    (Pre : MachineData → (SharedEnv.counted (Vals.EnvGCAdjXV Arch.tso tid C.pl S G)).State → Prop)
    (hpre : ∀ s g, Pre s g → FPre C.endPc s g)
    (hpost : ∀ s g s' g', Pre s g → FPost C.endPc s g s' g' → C.Q ((s', C.endPc), g'))
    (PreV : MachineData → (SharedEnv.counted (SharedEnv.inv S G)).State → Prop)
    (QV : MachineState × (Unit × Nat) → Prop) (QV_end : ∀ y, QV y → y.1.2 = C.endPc)
    (vals : ∀ s g, PreV s g →
      Safely (C.e.instrStepEnv (SharedEnv.counted (SharedEnv.inv S G))) QV ((s, C.entry), g)) :
    LowerThreadXV tid S B G :=
  { C with
    Pre := Pre
    main := safely_of_fragL_at h hq hs hentry hpre hpost
    PreV := PreV
    QV := QV
    QV_end := QV_end
    vals := vals }

/-! ## `pure` from a fragment spec -/

/-- **The static fields of a lowered x64 thread**: `LowerCoreX` without the
purity judgment (`PreR`, `QR`, `QR_end`, `pure`); same names and types. -/
structure LowerStaticX (tid : Nat) (S : SharedEnv.Layout) (B : Config isa → Res → Ghost → Prop) where
  e : Kraken.Executable Directive
  valid : Kraken.Executable.ValidLayout e
  pl : Plan
  hpl : pl.Valid
  shape : Phase1TreeFX e
  entry : Int64
  endPc : Int64
  stuck : ∀ (env : SharedEnv) x R, x.1.2 = endPc → ¬ e.instrStepEnv env x R
  Q : MachineState × (EStateX × Nat) → Prop
  Q_end : ∀ y, Q y → y.1.2 = endPc
  hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    (∃ n, Q (t.st.st, (σ, n))) → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g

/-- **A `LowerCoreX` from its static fields and a relPure fragment spec of
the entry function** in counted `(relPureQ Arch.tso ⊥).within S`, placed in
the image as for `LowerThreadX.ofFrag`; the purity post `QR` holds at the
end (`QR_end`) and follows from the spec's post at `endPc` (`hpost`). -/
noncomputable def LowerStaticX.ofFragPure {tid : Nat} {S : SharedEnv.Layout}
    {B : Config isa → Res → Ghost → Prop} (L : LowerStaticX tid S B) {frags : List Program} {q : Program}
    {l m₀ : Label}
    {FPre : Int64 → MachineData →
      (SharedEnv.counted ((SharedEnv.relPureQ Arch.tso fun _ _ => False).within S)).State → Prop}
    {FPost : Int64 → MachineData →
      (SharedEnv.counted ((SharedEnv.relPureQ Arch.tso fun _ _ => False).within S)).State → MachineData →
      (SharedEnv.counted ((SharedEnv.relPureQ Arch.tso fun _ _ => False).within S)).State → Prop}
    (h : FragSpecEnvL (SharedEnv.counted ((SharedEnv.relPureQ Arch.tso fun _ _ => False).within S)) frags l
      FPre FPost)
    (hq : @Program.Placed ⟨L.e⟩ q m₀) (hs : frags.all (fun p => Program.subBlocksOfE p q) = true)
    (hentry : L.entry = (_root_.Executable.labels L.e).label l)
    (PreR : MachineData → (SharedEnv.counted ((SharedEnv.relPureQ Arch.tso fun _ _ => False).within S)).State →
      Prop)
    (QR : MachineState × (Unit × Nat) → Prop) (QR_end : ∀ y, QR y → y.1.2 = L.endPc)
    (hpre : ∀ s g, PreR s g → FPre L.endPc s g)
    (hpost : ∀ s g s' g', PreR s g → FPost L.endPc s g s' g' → QR ((s', L.endPc), g')) :
    LowerCoreX tid S B :=
  { L with
    PreR := PreR
    QR := QR
    QR_end := QR_end
    pure := safely_of_fragL_at h hq hs hentry hpre hpost }

end Kraken.Promising.Lower.KitX

#print axioms Kraken.Promising.Lower.KitX.safely_of_fragL
#print axioms Kraken.Promising.Lower.KitX.safely_of_fragL_at
