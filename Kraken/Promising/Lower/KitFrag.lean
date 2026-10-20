/-
**The kit's whole-text `main` straight from a
fragment specification.** Generic (no pilot-specific
names). ISA: AArch64; machine: the executable machine's per-thread
environment semantics (`Executable.instrStepEnv`), partial correctness.

The kit (`Lower/Kit.lean`) takes per thread the whole-text partial triple
`main : PartialTripleEnv env Pre p Q (fun _ _ _ => False)` at the laid-out
text `l p`. Every pilot proved it by hand at its own text (`main_body`,
`main_tail`, `main_partialTripleEnv` at `<prog>_placed` and the end address
`(l p).addrOf p.length`), so a second text with the same `main` re-proved it.
Here a placement-independent spec `FragSpecEnvL env frags lm FPre FPost` of
`main` (over `main`'s fragment and its callees', `Lower/FragSpecCalls.lean`)
gives the triple at every laid-out text that

- starts with `main`'s label (`p = .label lm :: p'`), is well formed and not
  only labels (the three side conditions of `Program.placed_of_layout`), and
- holds every fragment's blocks (`Program.subBlocksOfE`, decidable),

with the runtime's return address `ra` read as the end of the text:
`hpre` (the kit's `Pre` gives `FPre` at `ra = (l p).addrOf p.length`) and
`hpost` (`FPost` at that `ra` gives `Q`). All side conditions are `by decide`
/ `rfl` / `Iff.rfl`-style for closed texts.

- `partialTripleEnv_of_fragL`: the bridge, for every environment (so the
  same lemma serves `EnvGCAdjA`, `EnvGCAdjV` and the relPure twins).
- `LowerThread.ofFrag`, `LowerThreadV.ofFrag`: a `LowerCore` plus a
  fragment spec of `main` is a lowered thread.
- `LowerThread.withMain`: replace a thread's `main` proof (same `Pre`, `Q`);
  its `Start` is the old thread's (`withMain_start`, by `Iff.rfl`).

The kit's remaining per-text facts are not placement facts: `stuck` is
`not_instrStepEnv_of_end_labels env k` (one line, `rfl` side conditions on
the text's trailing labels), `hB` reads the program's own `Q`.
-/
import Kraken.Promising.Lower.Kit
import Kraken.Promising.Lower.FragSpecCalls

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Kit

/-- **The whole-text triple from a fragment spec of `main`.** At the
laid-out text `layout p` starting with `main`'s label `lm` and holding the
fragments `frags`, the spec of `main` with the runtime's return address read
as the end of the text gives the partial triple of the whole text, no other
exit (the form of the kit's `main` field). Any environment. -/
theorem partialTripleEnv_of_fragL [layout : _root_.Layout] {p p' : Program} [Executable.ValidLayout (layout p)]
    {env : SharedEnv} {frags : List Program} {lm : Label} {FPre : Int64 → MachineData → env.State → Prop}
    {FPost : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnvL env frags lm FPre FPost)
    (hwf : Program.WF p) (hp : p = Directive.label lm :: p') (hne : p.any (fun d => !d.isLabel) = true)
    (hs : frags.all (fun q => Program.subBlocksOfE q p) = true)
    {Pre Q : MachineData → env.State → Prop}
    (hpre : ∀ s g, Pre s g → FPre ((layout p).addrOf p.length) s g)
    (hpost : ∀ s g s' g', Pre s g → FPost ((layout p).addrOf p.length) s g s' g' → Q s' g') :
    @PartialTripleEnv ⟨layout p⟩ env Pre p Q (fun _ _ _ => False) := by
  letI : CodeEnv := ⟨layout p⟩
  have hpl := Program.placed_of_layout hwf hp hne
  intro s g hP pc hpc
  obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := p) p [] 0 (by simp)
  have he : pc = (layout p).addrOf 0 := (hpl.entry pc hpc).symm.trans (hpl.entry _ hs0)
  subst he
  rw [← hpl.entry _ hs0]
  refine ((h.of_placed hpl hs) _ s g (hpre s g hP)).mono fun x ⟨hx, hq⟩ => Or.inl ⟨?_, hpost s g _ _ hP hq⟩
  rw [hx, hpl.entry _ hs0]
  exact (haf.trans (by rw [Nat.zero_add])).symm

/-- **A frameless lowered thread from a fragment spec of `main`**: the
`LowerCore` `C`, the kit's `Pre`, and `main`'s spec in
`counted (EnvGCAdjA A tid C.pl)` over fragments held by `C.p`, which starts
with `main`'s label (`partialTripleEnv_of_fragL`). -/
noncomputable def LowerThread.ofFrag {A : Arch} {tid : Nat} {rel : Loc → Pred}
    {B : Config isa → Res → Ghost → Prop} (C : LowerCore A tid rel B) {p' : Program} {frags : List Program}
    {lm : Label} {FPre : Int64 → MachineData → (SharedEnv.counted (EnvGCAdjA A tid C.pl)).State → Prop}
    {FPost : Int64 → MachineData → (SharedEnv.counted (EnvGCAdjA A tid C.pl)).State → MachineData →
      (SharedEnv.counted (EnvGCAdjA A tid C.pl)).State → Prop}
    (h : FragSpecEnvL (SharedEnv.counted (EnvGCAdjA A tid C.pl)) frags lm FPre FPost)
    (hwf : Program.WF C.p) (hp : C.p = Directive.label lm :: p') (hne : C.p.any (fun d => !d.isLabel) = true)
    (hs : frags.all (fun q => Program.subBlocksOfE q C.p) = true)
    (Pre : MachineData → (SharedEnv.counted (EnvGCAdjA A tid C.pl)).State → Prop)
    (hpre : ∀ s g, Pre s g → FPre ((C.l C.p).addrOf C.p.length) s g)
    (hpost : ∀ s g s' g', Pre s g → FPost ((C.l C.p).addrOf C.p.length) s g s' g' → C.Q s' g') :
    LowerThread A tid rel B :=
  { C with
    Pre := Pre
    main := @partialTripleEnv_of_fragL C.l C.p p' C.valid _ frags lm FPre FPost h hwf hp hne hs Pre C.Q hpre hpost }

/-- **The frame + value-bridge variant**: `main`'s spec in the
value-restricted `counted (EnvGCAdjV A tid C.pl G)`, and the value triple. -/
noncomputable def LowerThreadV.ofFrag {A : Arch} {tid : Nat} {rel : Loc → Pred}
    {B : Config isa → Res → Ghost → Prop} {S : SharedEnv.Layout} {G : Loc → Val → Prop}
    (C : LowerCore A tid rel B) {p' : Program} {frags : List Program}
    {lm : Label} {FPre : Int64 → MachineData → (SharedEnv.counted (Vals.EnvGCAdjV A tid C.pl G)).State → Prop}
    {FPost : Int64 → MachineData → (SharedEnv.counted (Vals.EnvGCAdjV A tid C.pl G)).State → MachineData →
      (SharedEnv.counted (Vals.EnvGCAdjV A tid C.pl G)).State → Prop}
    (h : FragSpecEnvL (SharedEnv.counted (Vals.EnvGCAdjV A tid C.pl G)) frags lm FPre FPost)
    (hwf : Program.WF C.p) (hp : C.p = Directive.label lm :: p') (hne : C.p.any (fun d => !d.isLabel) = true)
    (hs : frags.all (fun q => Program.subBlocksOfE q C.p) = true)
    (Pre : MachineData → (SharedEnv.counted (Vals.EnvGCAdjV A tid C.pl G)).State → Prop)
    (hpre : ∀ s g, Pre s g → FPre ((C.l C.p).addrOf C.p.length) s g)
    (hpost : ∀ s g s' g', Pre s g → FPost ((C.l C.p).addrOf C.p.length) s g s' g' → C.Q s' g')
    (PreV QV : MachineData → (SharedEnv.counted (SharedEnv.inv S G)).State → Prop)
    (vals : @PartialTripleEnv ⟨C.l C.p⟩ (SharedEnv.counted (SharedEnv.inv S G)) PreV C.p QV (fun _ _ _ => False)) :
    LowerThreadV A tid rel B S G :=
  { C with
    Pre := Pre
    main := @partialTripleEnv_of_fragL C.l C.p p' C.valid _ frags lm FPre FPost h hwf hp hne hs Pre C.Q hpre hpost
    PreV := PreV
    QV := QV
    vals := vals }

/-- **Replace a thread's `main` proof** (same `Pre`, same `Q`), e.g. by one
from `partialTripleEnv_of_fragL`. -/
def LowerThread.withMain {A : Arch} {tid : Nat} {rel : Loc → Pred} {B : Config isa → Res → Ghost → Prop}
    (T : LowerThread A tid rel B)
    (main : @PartialTripleEnv ⟨T.l T.p⟩ (SharedEnv.counted (EnvGCAdjA A tid T.pl)) T.Pre T.p T.Q
      (fun _ _ _ => False)) : LowerThread A tid rel B :=
  { T with main := main }

/-- `withMain` keeps the start state. -/
theorem LowerThread.withMain_start {A : Arch} {tid : Nat} {rel : Loc → Pred}
    {B : Config isa → Res → Ghost → Prop} (T : LowerThread A tid rel B) {main} {σ : EStateA} {s : isa.State} :
    (T.withMain main).Start σ s ↔ T.Start σ s :=
  Iff.rfl

end Kraken.Promising.Lower.Kit
