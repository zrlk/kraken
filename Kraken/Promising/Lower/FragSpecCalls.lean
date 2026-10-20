/-
**Calls between fragment specifications, AArch64.**
Generic (no pilot-specific names).

`FragSpecEnv` (`Lower/FragSpec.lean`) covers a *leaf* fragment: its blocks
are total `vcgen` triples (`FragSpecEnv.of_cfg`), and a callee's spec is
partial (`Safely`, a CAS retry loop may spin forever), so a block that calls
cannot be one of them. This file composes fragment specs across calls, from
the callee's `FragSpecEnv`, **without re-proving the callee**:

- **Placement of both fragments.** A caller and its callee are separate
  fragments laid out anywhere: `FragSpecEnvL env frags l Pre Post` is
  `FragSpecEnv` over a *list* of fragments, each `PlacedIn` on its own
  (`FragSpecEnv.toL`, `FragSpecEnvL.toFrag`/`of_placed`/`at_sub`/`mono`). One
  concatenated fragment `fragF ++ fragG` would force `g` right behind `f`.
  Sub-fragment placement: `Program.PlacedIn.of_sub`, `FragSpecEnv.sub`,
  `FragSpecEnv.at_sub`.
- **Partial rules** (beside `PartialWpEnv.call` for `bl l`):
  `PartialWpEnv.blr` (an indirect call `blr xN` through a
  `FunSpecPartialEnv` at the address `xN` holds) and `PartialWpEnv.exit_call`
  (any *exit* of a fragment to a function's entry, with the caller's own
  return address: a tail call `b g`, `b.cond g`, `cbz … g`, or an indirect
  tail call `br xN`).
- **Fragment constructors** (the result placed by `fragF :: Gs`, `Gs` the
  callee's list): `FragSpecEnvL.of_block` (the entry block's run as a
  `PartialWpEnv`, the general form), and the three emitter shapes:
  - `FragSpecEnvL.call`: `f: A; bl g; B` with `A`, `B` straight-line `vcgen`
    triples (the non-leaf function; `A` saves `x30` in a callee-saved
    register, `B` restores it before `ret`);
  - `FragSpecEnvL.callr`: `f: A; blr xN; B` with `xN = &g` after `A`;
  - `FragSpecEnvL.tail`: `f: A; b g` (or `br xN` with `xN = &g`): one `vcgen`
    triple whose exit at `g`'s address meets `g`'s `Pre` with `f`'s own `ra`.

Scope (phase 1 of calls): the caller's entry block is one block (no label
inside `f` before its last call returns; loops around a call are not
covered: a loop belongs in the callee, or in a tail-called helper). A
self tail call (`b f` to `f`'s own entry) is a jump to an own label and is
already a loop of `FragSpecEnv.of_cfg`; mutual recursion between fragments
is not covered.

Machine: the executable machine's per-thread environment semantics
(`Executable.instrStepEnv`), partial correctness (`Safely`), as
`FunSpecPartialEnv`/`FragSpecEnv`.
-/
import Kraken.Promising.Lower.FragSpec

open Kraken
open Std.WP

namespace MachineWP

variable {env : SharedEnv}

/-! ## Placement of a sub-fragment -/

/-- **A fragment whose blocks are among a placed fragment's is placed**
(`Program.PlacedIn.of_placedE` with a `PlacedIn` fragment in place of a
`Placed` text). -/
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

/-- **Transport to a larger fragment**: a spec of `p` holds of every fragment
`q` holding `p`'s blocks (e.g. `q = p ++ r` or `r ++ p`, by `decide`). -/
theorem FragSpecEnv.sub {p q : Program} {l : Label} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnv env p l Pre Post) (hs : Program.subBlocksOfE p q = true) :
    FragSpecEnv env q l Pre Post :=
  ⟨fun hpl => h.spec (hpl.of_sub hs)⟩

/-- **The callee's spec in the caller's placement**: a code placing `q`
places the callee's fragment `p` among it. -/
theorem FragSpecEnv.at_sub [CodeEnv] {p q : Program} {l : Label}
    {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnv env p l Pre Post) (hpl : Program.PlacedIn q) (hs : Program.subBlocksOfE p q = true) :
    FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l) Pre Post :=
  h.spec (hpl.of_sub hs)

/-! ## Partial rules for indirect calls and tail calls -/

/-- **The partial indirect-call rule**: `blr r` through the callee's
`FunSpecPartialEnv` at the address `f` that `r` holds (read before `x30` is
written); the callee's return continues with the rest of the caller.
(`PartialWpEnv.call` with `blr_cellEnv` in place of `bl_cellEnv`.) -/
theorem PartialWpEnv.blr [CodeEnv] {r : RegOrZr .W64} {f : Int64} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (hf : FunSpecPartialEnv env f Pre Post) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    {s : MachineData} {g : env.State} (hr : Int64.ofBitVec (s.regs.getRegOrZr r) = f)
    (h : ∀ ra, Pre ra (s.setLr ra) g ∧ ∀ s' g', Post ra (s.setLr ra) g s' g' → PartialWpEnv env p Q E s' g') :
    PartialWpEnv env (Directive.instr ⟨.W64, .BLR r⟩ :: p) Q E s g := by
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  have hafter : cenv.after pc (Directive.instr ⟨.W64, .BLR r⟩ :: p) = cenv.after (pc + .ofNat z) p := by
    simp only [Executable.after, hseg]
  refine Safely.fold (.inr ⟨_, ⟨_, _, _, hseg, Or.inr ?_⟩, fun _ h => h⟩)
  rw [blr_cellEnv, hr]
  obtain ⟨hpre, hk⟩ := h (pc + .ofNat z)
  refine Safely.bind (hf _ _ _ hpre) ?_
  rintro ⟨⟨s', a⟩, g'⟩ ⟨rfl, hpost⟩
  rw [hafter]
  exact hk s' g' hpost _ hpl'

/-- **The tail-call rule** (partial): an exit of `q` to the entry `f` of a
function with a `FunSpecPartialEnv` continues as that function's run, which
returns to the return address `ra` chosen at the exit (the caller's own: a
tail call leaves `x30` alone), where the caller's exit `E ra` must hold.
Covers `b g`, `b.cond g`, `cbz … g` (exit at `g`'s label) and `br xN` (exit at
the address `xN` holds). -/
theorem PartialWpEnv.exit_call [CodeEnv] {f : Int64} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (hf : FunSpecPartialEnv env f Pre Post) {q : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    {s : MachineData} {g : env.State}
    (h : PartialWpEnv env q Q (fun a s' g' => (a = f ∧ ∃ ra, Pre ra s' g' ∧
      ∀ s'' g'', Post ra s' g' s'' g'' → E ra s'' g'') ∨ E a s' g') s g) :
    PartialWpEnv env q Q E s g := by
  intro pc hpl
  refine Safely.bind (h pc hpl) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (hq | ⟨ha, ra, hpre, hk⟩ | he)
  · exact Safely.fold (.inl (.inl hq))
  · dsimp only at ha hpre hk
    subst ha
    exact (hf ra s' g' hpre).mono fun x ⟨hx, hpost⟩ => .inr (hx ▸ hk _ _ hpost)
  · exact Safely.fold (.inl (.inr he))

/-! ## Specs over several fragments

A caller and its callee are separate fragments, laid out anywhere in the
image; one fragment `fragF ++ fragG` would force `g`'s text right behind
`f`'s (its `PlacedIn` links `f`'s last block to `g`'s label). So a spec with
calls is placed by a **list** of fragments, each placed on its own. -/

/-- **A placement-independent function specification over several
fragments**: in every ambient code that places each fragment of `frags`, the
function entered at `l`'s address satisfies `FunSpecPartialEnv env _ Pre Post`.
`FragSpecEnv` is the one-fragment case (`FragSpecEnv.toL`, `FragSpecEnvL.toFrag`). -/
structure FragSpecEnvL (env : SharedEnv) (frags : List Program) (l : Label)
    (Pre : Int64 → MachineData → env.State → Prop)
    (Post : Int64 → MachineData → env.State → MachineData → env.State → Prop) : Prop where
  /-- The specification in an ambient code that places every fragment. -/
  spec : ∀ [CodeEnv], (∀ p ∈ frags, Program.PlacedIn p) →
    FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l) Pre Post

/-- A one-fragment spec is a spec over the singleton list. -/
theorem FragSpecEnv.toL {frag : Program} {l : Label} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnv env frag l Pre Post) : FragSpecEnvL env [frag] l Pre Post :=
  ⟨fun hpl => h.spec (hpl frag (List.mem_singleton_self _))⟩

/-- **Back to one fragment**: every fragment of the list among `q`'s blocks
(decidable; `q` may be the whole image). -/
theorem FragSpecEnvL.toFrag {frags : List Program} {q : Program} {l : Label}
    {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnvL env frags l Pre Post) (hs : frags.all (fun p => Program.subBlocksOfE p q) = true) :
    FragSpecEnv env q l Pre Post :=
  ⟨fun hpl => h.spec fun p hp => hpl.of_sub (List.all_eq_true.mp hs p hp)⟩

/-- **Transport into an image** (`FragSpecEnv.of_placed` for a list). -/
theorem FragSpecEnvL.of_placed [CodeEnv] {frags : List Program} {q : Program} {l m₀ : Label}
    {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnvL env frags l Pre Post) (hq : Program.Placed q m₀)
    (hs : frags.all (fun p => Program.subBlocksOfE p q) = true) :
    FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l) Pre Post :=
  (h.toFrag hs).at hq.toPlacedIn

/-- **The callee's spec in the caller's placement**: the callee's fragments
are among the caller's. -/
theorem FragSpecEnvL.at_sub [CodeEnv] {Gs Fs : List Program} {l : Label}
    {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnvL env Gs l Pre Post) (hpl : ∀ p ∈ Fs, Program.PlacedIn p) (hs : ∀ p ∈ Gs, p ∈ Fs) :
    FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l) Pre Post :=
  h.spec fun p hp => hpl p (hs p hp)

/-- **Weakening**: a stronger precondition, a weaker postcondition. -/
theorem FragSpecEnvL.mono {frags : List Program} {l : Label} {Pre Pre' : Int64 → MachineData → env.State → Prop}
    {Post Post' : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnvL env frags l Pre Post) (hpre : ∀ ra t g, Pre' ra t g → Pre ra t g)
    (hpost : ∀ ra t g t' g', Pre' ra t g → Post ra t g t' g' → Post' ra t g t' g') :
    FragSpecEnvL env frags l Pre' Post' := by
  refine ⟨fun hpl ra t g hp => ?_⟩
  exact (h.spec hpl ra t g (hpre ra t g hp)).mono fun x ⟨hra, hq⟩ => ⟨hra, hpost ra t g _ _ hp hq⟩

/-! ## Fragment constructors -/

/-- **The general constructor**: the run of `fragF`'s block at `l`, from
every `Pre` state, as a `PartialWpEnv` in every code placing `fragF` and the
callees' fragments `Gs`: it never falls through, and exits only by returning
to `ra` with `Post`. The proof may use the placement (callee specs by
`FragSpecEnvL.at_sub`). -/
theorem FragSpecEnvL.of_block {fragF : Program} {Gs : List Program} {l : Label} {blk : Program.Block}
    {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (hb : Program.blockAt fragF l = some blk)
    (h : ∀ [CodeEnv], (∀ p ∈ fragF :: Gs, Program.PlacedIn p) → ∀ ra t g, Pre ra t g →
      PartialWpEnv env blk.body (fun _ _ => False) (fun a s g' => a = ra ∧ Post ra t g s g') t g) :
    FragSpecEnvL env (fragF :: Gs) l Pre Post := by
  refine ⟨fun hpl ra t g hp => ?_⟩
  exact (h hpl ra t g hp _ ((hpl fragF List.mem_cons_self).block l blk hb)).mono
    fun x hx => hx.elim (fun h => h.2.elim) id

/-- A straight-line `vcgen` triple that never falls through and exits with
`E`, as a `PartialWpEnv` (`PartialWpEnv.of_wpEnv` with an empty rest). -/
theorem PartialWpEnv.of_triple_exit [CodeEnv] {q : Program} {P : MachineData → env.State → Prop}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    {s : MachineData} {g : env.State}
    (h : ⦃ P ⦄ (⟨q⟩ : EnvProgram env) ⦃ (fun _ _ _ => False); E ⦄) (hp : P s g) :
    PartialWpEnv env q Q E s g := by
  have hw := h.le_wp s g hp
  rw [wpEnv_eq] at hw
  have h' : PartialWpEnv env (q ++ []) Q E s g :=
    PartialWpEnv.of_wpEnv (Executable.wpEnv_mono (fun _ _ h => h.elim) (fun _ _ _ h => h) hw)
  simpa using h'

/-- **A non-leaf function** `f: A; bl g; B` (the entry block of `fragF`),
from `g`'s spec over its fragments `Gs` (`hg.toL` for a one-fragment
`FragSpecEnv`); the result is placed by `fragF :: Gs`:
- `hA`: the prefix (argument set-up; save `x30` in a callee-saved register)
  reaches `Mid1`;
- `hcall`: `Mid1` meets `g`'s `Pre` for every return address `bl` may write,
  and `g`'s `Post` gives `Mid2` (here the frame composes: what `g` keeps
  callee-saved, `f` still holds);
- `hB`: the suffix (restore `x30`, `ret`) returns to `ra` with `Post`. -/
theorem FragSpecEnvL.call {fragF A B : Program} {Gs : List Program} {lf lg : Label} {blk : Program.Block}
    {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    {PreG : Int64 → MachineData → env.State → Prop}
    {PostG : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (Mid1 Mid2 : Int64 → MachineData → env.State → MachineData → env.State → Prop)
    (hg : FragSpecEnvL env Gs lg PreG PostG) (hb : Program.blockAt fragF lf = some blk)
    (hbody : blk.body = A ++ Directive.instr ⟨.W64, .BL (.label lg)⟩ :: B)
    (hA : ∀ [CodeEnv] (ra : Int64) (t : MachineData) (g : env.State),
      ⦃ fun s g' => Pre ra t g ∧ s = t ∧ g' = g ⦄ (⟨A⟩ : EnvProgram env)
      ⦃ (fun _ s g' => Mid1 ra t g s g'); fun _ _ _ => False ⦄)
    (hcall : ∀ ra t g s g', Pre ra t g → Mid1 ra t g s g' → ∀ ra',
      PreG ra' (s.setLr ra') g' ∧ ∀ s' g'', PostG ra' (s.setLr ra') g' s' g'' → Mid2 ra t g s' g'')
    (hB : ∀ [CodeEnv] (ra : Int64) (t : MachineData) (g : env.State) (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g' => Pre ra t g ∧ Mid2 ra t g s g' ∧ s = s₀ ∧ g' = g₀ ⦄ (⟨B⟩ : EnvProgram env)
      ⦃ (fun _ _ _ => False); fun a s g' => a = ra ∧ Post ra t g s g' ⦄) :
    FragSpecEnvL env (fragF :: Gs) lf Pre Post := by
  refine FragSpecEnvL.of_block hb fun hpl ra t g hp => ?_
  have hgS := hg.at_sub hpl fun p hp => List.mem_cons_of_mem _ hp
  rw [hbody]
  have h1 := (hA ra t g).le_wp t g ⟨hp, rfl, rfl⟩
  rw [wpEnv_eq] at h1
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h1)
  intro s1 g1 hm
  refine PartialWpEnv.call hgS fun ra' => ⟨(hcall ra t g s1 g1 hp hm ra').1, fun s' g' hpost => ?_⟩
  exact PartialWpEnv.of_triple_exit (hB ra t g s' g') ⟨hp, (hcall ra t g s1 g1 hp hm ra').2 s' g' hpost, rfl, rfl⟩

/-- **An indirect call** `f: A; blr r; B`: `FragSpecEnvL.call` where `A`
leaves `g`'s address in `r` (e.g. `adr x16, g`). A function pointer passed in
by the caller cannot be stated in a placement-independent `Pre` (the address
is the placement's); for it use `PartialWpEnv.blr` at a placed program. -/
theorem FragSpecEnvL.callr {fragF A B : Program} {Gs : List Program} {lf lg : Label} {blk : Program.Block}
    {r : RegOrZr .W64} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    {PreG : Int64 → MachineData → env.State → Prop}
    {PostG : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (Mid1 Mid2 : Int64 → MachineData → env.State → MachineData → env.State → Prop)
    (hg : FragSpecEnvL env Gs lg PreG PostG) (hb : Program.blockAt fragF lf = some blk)
    (hbody : blk.body = A ++ Directive.instr ⟨.W64, .BLR r⟩ :: B)
    (hA : ∀ [CodeEnv] (ra : Int64) (t : MachineData) (g : env.State),
      ⦃ fun s g' => Pre ra t g ∧ s = t ∧ g' = g ⦄ (⟨A⟩ : EnvProgram env)
      ⦃ (fun _ s g' => Mid1 ra t g s g' ∧
          Int64.ofBitVec (s.regs.getRegOrZr r) = (_root_.Executable.labels cenv).label lg);
        fun _ _ _ => False ⦄)
    (hcall : ∀ ra t g s g', Pre ra t g → Mid1 ra t g s g' → ∀ ra',
      PreG ra' (s.setLr ra') g' ∧ ∀ s' g'', PostG ra' (s.setLr ra') g' s' g'' → Mid2 ra t g s' g'')
    (hB : ∀ [CodeEnv] (ra : Int64) (t : MachineData) (g : env.State) (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g' => Pre ra t g ∧ Mid2 ra t g s g' ∧ s = s₀ ∧ g' = g₀ ⦄ (⟨B⟩ : EnvProgram env)
      ⦃ (fun _ _ _ => False); fun a s g' => a = ra ∧ Post ra t g s g' ⦄) :
    FragSpecEnvL env (fragF :: Gs) lf Pre Post := by
  refine FragSpecEnvL.of_block hb fun hpl ra t g hp => ?_
  have hgS := hg.at_sub hpl fun p hp => List.mem_cons_of_mem _ hp
  rw [hbody]
  have h1 := (hA ra t g).le_wp t g ⟨hp, rfl, rfl⟩
  rw [wpEnv_eq] at h1
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h1)
  rintro s1 g1 ⟨hm, hr⟩
  refine PartialWpEnv.blr hgS hr fun ra' => ⟨(hcall ra t g s1 g1 hp hm ra').1, fun s' g' hpost => ?_⟩
  exact PartialWpEnv.of_triple_exit (hB ra t g s' g') ⟨hp, (hcall ra t g s1 g1 hp hm ra').2 s' g' hpost, rfl, rfl⟩

/-- **A tail call** `f: A; b g` (or `br xN` with `xN = &g`, or a conditional
branch to `g`): `f`'s entry block is one `vcgen` triple whose exits are
either at `g`'s address, meeting `g`'s `Pre` **at `f`'s own return address
`ra`** with `g`'s `Post` giving `f`'s, or `f`'s own `ret` to `ra`. -/
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
  refine FragSpecEnvL.of_block hb fun hpl ra t g hp => ?_
  have h := PartialWpEnv.of_triple_exit (Q := fun _ _ => False) (hbody ra t g) ⟨hp, rfl, rfl⟩
  refine PartialWpEnv.exit_call (hg.at_sub hpl fun p hp => List.mem_cons_of_mem _ hp) fun pc hpc => ?_
  refine (h pc hpc).mono ?_
  rintro x (⟨-, hF⟩ | ⟨ha, hpre, hk⟩ | ⟨ha, hpost⟩)
  · exact hF.elim
  · exact .inr (.inl ⟨ha, ra, hpre, fun s' g' h => ⟨rfl, hk s' g' h⟩⟩)
  · exact .inr (.inr ⟨ha, hpost⟩)

end MachineWP
