/-
**Placement-independent fragment specifications,
x64.** Generic. The x64 twin of `Lower/FragSpec.lean`
(the fragment-spec layer), with the same names in `MachineWP` (the two files cannot be
co-imported, like the rest of the two ISAs' `MachineWP` layers).

- `FragSpecEnv env frag l Pre Post`: for every `CodeEnv` in which `frag` is
  `Program.PlacedIn`, the x64 `FunSpecPartialEnv` (`X64/EnvCallsPartial.lean`)
  holds at `l`'s address. `Pre`/`Post` read the return address `ra` (on x64:
  the `dmem` slot at `rsp`, stated by the client, e.g. The x64 pilot's `RetAt`) and
  the entry and exit states, so they do not mention the placement.
- `FragSpecEnv.at`, `.of_placed` (from an image's `Program.Placed` and the
  decidable `Program.subBlocksOfE`), `.of_layout` (at `layout q` directly),
  `.mono`, and the constructor `.of_cfg` (`cfgEnv_partial_fun` once, the
  placement abstract).

As on AArch64, x64's `FunSpecPartialEnv.of_cfg` takes the placement as an
argument `hpl : Program.PlacedIn p`, and its block obligations never inspect
the ambient code (`cfg_cases_env` and `vcgen` read only the fragment's blocks),
so a pilot's proof goes through verbatim with the placement abstract.

Machine: the executable machine's per-thread environment semantics
(`Executable.instrStepEnv`), partial correctness (`Safely`).
-/
import Kraken.X64.EnvCallsPartial

open Kraken
open Std.WP

namespace MachineWP

variable {env : SharedEnv}

/-- **A placement-independent function specification** (x64): in every
ambient code that places the blocks of `frag`, the function entered at `l`'s
address satisfies `FunSpecPartialEnv env _ Pre Post`. -/
structure FragSpecEnv (env : SharedEnv) (frag : Program) (l : Label) (Pre : Int64 → MachineData → env.State → Prop)
    (Post : Int64 → MachineData → env.State → MachineData → env.State → Prop) : Prop where
  /-- The specification in an ambient code that places `frag` (a structure, as
  on AArch64, so that dot notation keeps the `∀ [CodeEnv]` binder). -/
  spec : ∀ [CodeEnv], Program.PlacedIn frag → FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l) Pre Post

/-- **Transport** to an ambient code that places the fragment. -/
theorem FragSpecEnv.at [CodeEnv] {frag : Program} {l : Label} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnv env frag l Pre Post) (hpl : Program.PlacedIn frag) :
    FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l) Pre Post :=
  h.spec hpl

/-- **Transport into an image**: `frag`'s blocks among a placed text's
(`Program.subBlocksOfE`, `by decide` for closed texts). -/
theorem FragSpecEnv.of_placed [CodeEnv] {frag q : Program} {l m₀ : Label}
    {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnv env frag l Pre Post) (hq : Program.Placed q m₀) (hs : Program.subBlocksOfE frag q = true) :
    FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l) Pre Post :=
  h.spec (Program.PlacedIn.of_placedE hq hs)

/-- **Transport into a laid-out program** `layout q`: `q` well formed,
starting with its entry label, not only labels, and holding `frag`'s blocks
(all `by decide` / `rfl` for closed texts). -/
theorem FragSpecEnv.of_layout [layout : _root_.Layout] {frag q q' : Program} [Executable.ValidLayout (layout q)]
    {l m₀ : Label} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnv env frag l Pre Post) (hwf : Program.WF q) (hq : q = Directive.label m₀ :: q')
    (hne : q.any (fun d => !d.isLabel) = true) (hs : Program.subBlocksOfE frag q = true) :
    @FunSpecPartialEnv ⟨layout q⟩ env ((_root_.Executable.labels (layout q)).label l) Pre Post :=
  @FragSpecEnv.of_placed env ⟨layout q⟩ frag q l m₀ Pre Post h (Program.placed_of_layout hwf hq hne) hs

/-- **Weakening**: a stronger precondition, a weaker postcondition. -/
theorem FragSpecEnv.mono {frag : Program} {l : Label} {Pre Pre' : Int64 → MachineData → env.State → Prop}
    {Post Post' : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnv env frag l Pre Post) (hpre : ∀ ra t g, Pre' ra t g → Pre ra t g)
    (hpost : ∀ ra t g t' g', Pre' ra t g → Post ra t g t' g' → Post' ra t g t' g') :
    FragSpecEnv env frag l Pre' Post' := by
  refine ⟨fun hpl ra t g hp => ?_⟩
  exact (h.spec hpl ra t g (hpre ra t g hp)).mono fun x ⟨hra, hq⟩ => ⟨hra, hpost ra t g _ _ hp hq⟩

/-- **The constructor**: `FunSpecPartialEnv.of_cfg` with the placement
abstract. `T ra t g` is the loop table of the run entered with return address
`ra` from `(t, g)`; every block, in every ambient code, keeps the table or
exits to `ra` with `Post` (the `ret`). -/
theorem FragSpecEnv.of_cfg {frag p' : Program} {l₀ : Label} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (T : Int64 → MachineData → env.State → Label → MachineData → env.State → Prop)
    (hp : frag = Directive.label l₀ :: p') (hwf : Program.WF frag)
    (hinit : ∀ ra t g, Pre ra t g → T ra t g l₀ t g)
    (hblocks : ∀ [CodeEnv] (ra : Int64) (t : MachineData) (g : env.State), Pre ra t g →
      ∀ l blk, Program.blockAt frag l = some blk → ∀ (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g' => T ra t g l s g' ∧ s = s₀ ∧ g' = g₀ ⦄ (⟨blk.body⟩ : EnvProgram env)
      ⦃ (match blk.next with
         | some l' => fun _ s g' => T ra t g l' s g'
         | none => fun _ _ _ => False);
        fun a s g' => Table.ofLabelsEnv (fun l' s g' => (Program.blockAt frag l').isSome ∧ T ra t g l' s g'
          ∧ Program.EdgeSafe frag l s₀ g₀ l' s g') a s g' ∨ (a = ra ∧ Post ra t g s g') ⦄) :
    FragSpecEnv env frag l₀ Pre Post :=
  ⟨fun hpl => FunSpecPartialEnv.of_cfg T hp hwf hpl hinit (hblocks)⟩

end MachineWP
