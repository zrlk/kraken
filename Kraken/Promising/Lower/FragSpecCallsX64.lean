/-
**The non-leaf call rules for fragment specs, x64.**
Generic. The x64 twin of `Lower/FragSpecCalls.lean`
(the non-leaf call rules), over the x64 `FragSpecEnv` (`Lower/FragSpecX64.lean`), with the
same names in `MachineWP` (the AArch64 and x64 layers cannot be co-imported).

- `Program.PlacedIn.of_sub` and `FragSpecEnvL` (a spec placed by a *list* of
  fragments, each `PlacedIn` on its own), with `FragSpecEnv.toL`,
  `FragSpecEnvL.toFrag`/`of_placed`/`at_sub`/`mono`, statements as on AArch64.
- `FragSpecEnvL.tail`: `f: A; jmp g` (or a conditional jump to `g`): the
  entry block is one `vcgen` triple whose exit at `g`'s address meets `g`'s
  `Pre` at `f`'s own return address `ra` (with the stack convention, `jmp`
  leaves `rsp` and the return slot alone).
- `FragSpecEnvL.callLink`: a call in the register-link convention
  (`Lower/KitX64Link.lean`): `f: A; leaq ret_k(%rip), %r11; jmp g` as the
  block at `lf`, `ret_k: B` as the block at `lk`. The first block's exit at
  `g`'s address meets `g`'s `Pre` at `ra := &ret_k`; `g`'s return lands at the
  label `lk` (`FunSpecPartialEnv.jcallLink`), and the block there returns to
  `f`'s `ra` with `Post`. No stack side condition. The callee `g` sees its
  link register in its `Pre`; the caller keeps its own `ra` across the call
  in a register `g` keeps.

Scope: as the non-leaf call rules's phase 1 (no loop around the call; `callLink`'s two
blocks run once each). The stack-convention `call` (`PartialWpEnv.call`, a
slot side condition) and calls inside loops on x64 are not covered here.

Machine: the executable machine's per-thread environment semantics
(`Executable.instrStepEnv`), partial correctness (`Safely`), as
`FunSpecPartialEnv`/`FragSpecEnvL`.
-/
import Kraken.Promising.Lower.FragSpecX64
import Kraken.Promising.Lower.KitX64Link

open Kraken
open Std.WP

namespace MachineWP

variable {env : SharedEnv}

/-- **A fragment whose blocks are among a placed fragment's is placed** (x64;
the AArch64 statement). -/
theorem _root_.Program.PlacedIn.of_sub [CodeEnv] {p q : Program} (hq : Program.PlacedIn q)
    (h : Program.subBlocksOfE p q = true) : Program.PlacedIn p := by
  have key : ∀ l blk, Program.blockAt p l = some blk →
      (blk.body = [] ∧ blk.next = none) ∨
      ∃ blk', Program.blockAt q l = some blk' ∧ blk'.body = blk.body
        ∧ (blk.next.isNone = true ∨ blk'.next = blk.next) := by
    intro l blk hb
    have hmem : l ∈ (Program.view p).2.map (·.1) := by
      rw [← Program.labels_view]
      exact Program.blockAt_mem_labels hb
    obtain ⟨lb, hlb, rfl⟩ := List.mem_map.mp hmem
    have hall := List.all_eq_true.mp h lb hlb
    simp only [hb] at hall
    rcases Bool.or_eq_true_iff.mp hall with he | hall
    · left
      simp only [Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at he
      exact he
    · right
      cases hb' : Program.blockAt q lb.1 with
      | none => rw [hb'] at hall; cases hall
      | some blk' =>
        rw [hb'] at hall
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hall
        exact ⟨blk', rfl, hall.1, hall.2⟩
  refine ⟨?_, ?_⟩
  · intro l blk hb
    rcases key l blk hb with ⟨he, -⟩ | ⟨blk', hb', hbody, -⟩
    · rw [he]; trivial
    · rw [← hbody]
      exact hq.block l blk' hb'
  · intro l blk l' hb hn
    rcases key l blk hb with ⟨-, he⟩ | ⟨blk', hb', hbody, hnext⟩
    · rw [hn] at he; cases he
    · rw [hn] at hnext
      simp only [Option.isNone_some, Bool.false_eq_true, false_or] at hnext
      rw [← hbody]
      exact hq.next l blk' l' hb' hnext

/-- **A placement-independent function specification over several
fragments** (x64): in every ambient code that places each fragment of
`frags`, the function entered at `l`'s address satisfies `FunSpecPartialEnv`. -/
structure FragSpecEnvL (env : SharedEnv) (frags : List Program) (l : Label)
    (Pre : Int64 → MachineData → env.State → Prop)
    (Post : Int64 → MachineData → env.State → MachineData → env.State → Prop) : Prop where
  /-- The specification in an ambient code that places every fragment. -/
  spec : ∀ [CodeEnv], (∀ p ∈ frags, Program.PlacedIn p) →
    FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l) Pre Post

section L

variable {Pre Pre' : Int64 → MachineData → env.State → Prop}
  {Post Post' : Int64 → MachineData → env.State → MachineData → env.State → Prop}

/-- A one-fragment spec is a spec over the singleton list. -/
theorem FragSpecEnv.toL {frag : Program} {l : Label} (h : FragSpecEnv env frag l Pre Post) :
    FragSpecEnvL env [frag] l Pre Post :=
  ⟨fun hpl => h.spec (hpl frag (List.mem_singleton_self _))⟩

/-- **Back to one fragment**: every fragment of the list among `q`'s blocks. -/
theorem FragSpecEnvL.toFrag {frags : List Program} {q : Program} {l : Label}
    (h : FragSpecEnvL env frags l Pre Post) (hs : frags.all (fun p => Program.subBlocksOfE p q) = true) :
    FragSpecEnv env q l Pre Post :=
  ⟨fun hpl => h.spec fun p hp => hpl.of_sub (List.all_eq_true.mp hs p hp)⟩

/-- **Transport into an image** (`FragSpecEnv.of_placed` for a list). -/
theorem FragSpecEnvL.of_placed [CodeEnv] {frags : List Program} {q : Program} {l m₀ : Label}
    (h : FragSpecEnvL env frags l Pre Post) (hq : Program.Placed q m₀)
    (hs : frags.all (fun p => Program.subBlocksOfE p q) = true) :
    FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l) Pre Post :=
  (h.toFrag hs).at hq.toPlacedIn

/-- **The callee's spec in the caller's placement.** -/
theorem FragSpecEnvL.at_sub [CodeEnv] {Gs Fs : List Program} {l : Label}
    (h : FragSpecEnvL env Gs l Pre Post) (hpl : ∀ p ∈ Fs, Program.PlacedIn p) (hs : ∀ p ∈ Gs, p ∈ Fs) :
    FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l) Pre Post :=
  h.spec fun p hp => hpl p (hs p hp)

/-- **Weakening**: a stronger precondition, a weaker postcondition. -/
theorem FragSpecEnvL.mono {frags : List Program} {l : Label}
    (h : FragSpecEnvL env frags l Pre Post) (hpre : ∀ ra t g, Pre' ra t g → Pre ra t g)
    (hpost : ∀ ra t g t' g', Pre' ra t g → Post ra t g t' g' → Post' ra t g t' g') :
    FragSpecEnvL env frags l Pre' Post' := by
  refine ⟨fun hpl ra t g hp => ?_⟩
  exact (h.spec hpl ra t g (hpre ra t g hp)).mono fun x ⟨hra, hq⟩ => ⟨hra, hpost ra t g _ _ hp hq⟩

end L

/-- A block of a placed fragment, run from its label by a `vcgen` triple that
never falls through: `Eventually` into the triple's exits. -/
private theorem block_run [CodeEnv] {p : Program} {l : Label} {blk : Program.Block}
    (hpl : Program.PlacedIn p) (hb : Program.blockAt p l = some blk)
    {P : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    {s : MachineData} {g : env.State}
    (h : ⦃ P ⦄ (⟨blk.body⟩ : EnvProgram env) ⦃ (fun _ _ _ => False); E ⦄) (hp : P s g) :
    Eventually (cenv.instrStepEnv env) (fun x => E x.1.2 x.1.1 x.2)
      ((s, (_root_.Executable.labels cenv).label l), g) := by
  have hw := h.le_wp s g hp
  rw [wpEnv_eq] at hw
  exact eventually_weaken _ _ _ _ (fun _ hx => hx.elim (fun h => h.2.elim) id) (hw _ (hpl.block l blk hb))

/-- **A tail call** `f: A; jmp g` (x64): `f`'s entry block is one `vcgen`
triple whose exits are either at `g`'s address, meeting `g`'s `Pre` **at
`f`'s own return address `ra`** with `g`'s `Post` giving `f`'s, or `f`'s own
`ret` to `ra`. -/
theorem FragSpecEnvL.tail {fragF : Program} {Gs : List Program} {lf lg : Label} {blk : Program.Block}
    {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    {PreG : Int64 → MachineData → env.State → Prop}
    {PostG : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (hg : FragSpecEnvL env Gs lg PreG PostG) (hb : Program.blockAt fragF lf = some blk)
    (hbody : ∀ [CodeEnv] (ra : Int64) (t : MachineData) (g : env.State),
      ⦃ fun s g' => Pre ra t g ∧ s = t ∧ g' = g ⦄ (⟨blk.body⟩ : EnvProgram env)
      ⦃ (fun _ _ _ => False);
        fun a s g' => (a = (_root_.Executable.labels cenv).label lg ∧ PreG ra s g' ∧
          ∀ s' g'', PostG ra s g' s' g'' → Post ra t g s' g'') ∨ (a = ra ∧ Post ra t g s g') ⦄) :
    FragSpecEnvL env (fragF :: Gs) lf Pre Post := by
  refine ⟨fun hpl ra t g hp => ?_⟩
  have hgS := hg.at_sub hpl fun p hp => List.mem_cons_of_mem _ hp
  refine Safely.of_eventually_safely (block_run (hpl fragF List.mem_cons_self) hb (hbody ra t g)
    ⟨hp, rfl, rfl⟩) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, hpre, hk⟩ | ⟨ha, hpost⟩)
  · dsimp only at ha hpre hk
    subst ha
    exact hgS.jcallLink hpre fun s'' g'' h => Safely.fold (.inl ⟨rfl, hk s'' g'' h⟩)
  · exact Safely.fold (.inl ⟨ha, hpost⟩)

/-- **A call in the register-link convention** (x64): the block at `lf`
(`A; leaq ret_k(%rip), %r11; jmp g`) exits at `g`'s address meeting `g`'s
`Pre` at the return address `&lk` (the label `ret_k`; `g` reads its link
register in `Pre`), with `g`'s `Post` giving `Mid2`; the block at `lk`
(`ret_k: B`) returns from `Mid2` to `f`'s `ra` with `Post`. `f` keeps its own
`ra` across the call in a register that `g`'s `Post` keeps. -/
theorem FragSpecEnvL.callLink {fragF : Program} {Gs : List Program} {lf lk lg : Label}
    {blkF blkK : Program.Block} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    {PreG : Int64 → MachineData → env.State → Prop}
    {PostG : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (Mid2 : Int64 → MachineData → env.State → MachineData → env.State → Prop)
    (hg : FragSpecEnvL env Gs lg PreG PostG)
    (hbF : Program.blockAt fragF lf = some blkF) (hbK : Program.blockAt fragF lk = some blkK)
    (hA : ∀ [CodeEnv] (ra : Int64) (t : MachineData) (g : env.State),
      ⦃ fun s g' => Pre ra t g ∧ s = t ∧ g' = g ⦄ (⟨blkF.body⟩ : EnvProgram env)
      ⦃ (fun _ _ _ => False);
        fun a s g' => a = (_root_.Executable.labels cenv).label lg ∧
          PreG ((_root_.Executable.labels cenv).label lk) s g' ∧
          ∀ s' g'', PostG ((_root_.Executable.labels cenv).label lk) s g' s' g'' → Mid2 ra t g s' g'' ⦄)
    (hB : ∀ [CodeEnv] (ra : Int64) (t : MachineData) (g : env.State) (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g' => Pre ra t g ∧ Mid2 ra t g s g' ∧ s = s₀ ∧ g' = g₀ ⦄ (⟨blkK.body⟩ : EnvProgram env)
      ⦃ (fun _ _ _ => False); fun a s g' => a = ra ∧ Post ra t g s g' ⦄) :
    FragSpecEnvL env (fragF :: Gs) lf Pre Post := by
  refine ⟨fun hpl ra t g hp => ?_⟩
  have hgS := hg.at_sub hpl fun p hp => List.mem_cons_of_mem _ hp
  have hF := hpl fragF List.mem_cons_self
  refine Safely.of_eventually_safely (block_run hF hbF (hA ra t g) ⟨hp, rfl, rfl⟩) ?_
  rintro ⟨⟨s', a⟩, g'⟩ ⟨ha, hpre, hk⟩
  dsimp only at ha hpre hk
  subst ha
  refine hgS.jcallLink hpre fun s'' g'' hpost => ?_
  exact Safely.of_eventually (block_run hF hbK (hB ra t g s'' g'') ⟨hp, hk s'' g'' hpost, rfl, rfl⟩)

end MachineWP
