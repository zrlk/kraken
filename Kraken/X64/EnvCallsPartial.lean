/-
**Calls under partial correctness, x64**. Generic. The x64 twin of
`Kraken/AArch64/EnvCallsPartial.lean`, with the same names in `MachineWP` (the two files cannot be
co-imported, like the rest of the two ISAs' `MachineWP` layers).

`MachineWP.call_proc_env_spec(_at)` (`Kraken/EnvVCGen.lean`) take the
callee's run as a `ProcSpecEnv`, i.e. *total* correctness (`Eventually`). A
function with a `lock cmpxchg` retry loop that another thread may make fail
forever has only a partial (`Safely`) specification. This file supplies:

- `PartialWpEnv`: the partial wp of a fragment at a state
  (`PartialTripleEnv` at a point); `PartialWpEnv.nil`, `.of_wpEnv` (a total
  prefix, e.g. by `vcgen`, then a partial rest), `.of_tripleEnv`, and
  `PartialTripleEnv.of_partialWpEnv`.
- `FunSpecPartialEnv`: a function's partial specification at its entry
  address, `ProcSpecEnv` with `Safely` in place of `Eventually` (and no
  logical variable; put it in `Pre`/`Post`): from every return address `ra`
  and entry state satisfying `Pre`, every run reaches `ra` with `Post` or
  runs forever.
- `PartialWpEnv.call`: **the partial call rule** for `call l` through a
  `FunSpecPartialEnv` at the label's address, **when the return-address
  slot is in `dmem`**: the push writes the slot `rsp - 8` of private memory
  and makes no shared event (`pushRA`). The rule's only stack side condition
  is that the slot is mapped (`hslot`). What the callee must preserve so
  that its `ret` comes back (the slot holding `ra` and `rsp` pointing at it
  when it returns) is the callee's own business: its `FunSpecPartialEnv`
  promises a return to `ra`, and the caller's continuation receives exactly
  the callee's `Post`, so stack facts the caller needs afterwards (`rsp`
  restored, the slot or other `dmem` kept) must be stated in `Post`. A shared
  (non-`dmem`) slot, the other half of `call_proc_env_spec`, is not covered;
  neither is the invariant that makes a non-empty `dmem` sound for the
  environment proofs (the private-stack invariant): every statement here is for an
  abstract `dmem` with the side conditions explicit.
- `cfgEnv_partial_fun`: `cfgEnv_partial_at` for a *function* fragment whose
  blocks may also leave by an arbitrary exit `E` (the `ret`, through
  `ret_env_spec`), and never fall through their last block.

`Safely` sequencing is `safely_bind` (private here; the root
`Safely.bind` lives in the AArch64 file).
-/
import Kraken.EnvCfgAbs

open Kraken
open Std.WP
open MachineWP

/-- Sequencing of `Safely` (`Safely.bind` of the AArch64 file, local copy). -/
private theorem safely_bind {State : Type} {trans : State → (State → Prop) → Prop} {P Q : State → Prop}
    {x : State} (h : Safely trans P x) (hk : ∀ y, P y → Safely trans Q y) : Safely trans Q x := by
  obtain ⟨Inv, hx, hInv⟩ := h
  refine ⟨fun z => Inv z ∨ Safely trans Q z, .inl hx, ?_⟩
  rintro z (hz | hz)
  · rcases hInv z hz with hp | ⟨R, hT, hR⟩
    · rcases (hk z hp).unfold with hq | ⟨R, hT, hR⟩
      · exact .inl hq
      · exact .inr ⟨R, hT, fun w hw => .inr (hR w hw)⟩
    · exact .inr ⟨R, hT, fun w hw => .inl (hR w hw)⟩
  · rcases hz.unfold with hq | ⟨R, hT, hR⟩
    · exact .inl hq
    · exact .inr ⟨R, hT, fun w hw => .inr (hR w hw)⟩

/-- **Placement of a concatenation**: `q ++ p` at `pc` is `q` at `pc` and `p`
behind it. -/
theorem _root_.Kraken.Executable.sits_append (e : Kraken.Executable Directive) :
    ∀ (q p : Program) (pc : Int64), e.sits pc (q ++ p) →
      e.sits pc q ∧ e.sits (e.after pc q) p ∧ e.after pc (q ++ p) = e.after (e.after pc q) p
  | [], _, _, h => ⟨trivial, h, rfl⟩
  | .label _ :: q, p, pc, h => Executable.sits_append e q p pc h
  | .instr i :: q, p, pc, h => by
    obtain ⟨z, rest, hc, hs⟩ := h
    obtain ⟨h1, h2, h3⟩ := Executable.sits_append e q p _ hs
    refine ⟨⟨z, rest, hc, h1⟩, ?_, ?_⟩ <;> simp only [Executable.after, hc, List.cons_append, h2, h3]
  | .byteArray b :: q, p, pc, h => by
    obtain ⟨z, rest, hc, hs⟩ := h
    obtain ⟨h1, h2, h3⟩ := Executable.sits_append e q p _ hs
    refine ⟨⟨z, rest, hc, h1⟩, ?_, ?_⟩ <;> simp only [Executable.after, hc, List.cons_append, h2, h3]

namespace MachineWP

variable [CodeEnv] {env : SharedEnv}

/-- **The partial wp** of the fragment `q` at `(s, g)`: placed anywhere, every
run falls through with `Q`, exits with `E`, or runs forever. -/
def PartialWpEnv (env : SharedEnv) (q : Program) (Q : MachineData → env.State → Prop)
    (E : Int64 → MachineData → env.State → Prop) (s : MachineData) (g : env.State) : Prop :=
  ∀ pc, cenv.sits pc q →
    Safely (cenv.instrStepEnv env) (fun x => (x.1.2 = cenv.after pc q ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2)
      ((s, pc), g)

theorem PartialWpEnv.nil {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    {s : MachineData} {g : env.State} (h : Q s g) : PartialWpEnv env [] Q E s g :=
  fun _ _ => Safely.fold (.inl (.inl ⟨rfl, h⟩))

/-- A total triple gives the partial wp at every state of its precondition. -/
theorem PartialWpEnv.of_tripleEnv {P : MachineData → env.State → Prop} {q : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    (h : TripleEnv env P q Q E) {s : MachineData} {g : env.State} (hp : P s g) : PartialWpEnv env q Q E s g :=
  fun pc hpl => Safely.of_eventually (h s g hp pc hpl)

/-- A partial wp at every state of `P` is a `PartialTripleEnv`. -/
theorem PartialTripleEnv.of_partialWpEnv {P : MachineData → env.State → Prop} {q : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    (h : ∀ s g, P s g → PartialWpEnv env q Q E s g) : PartialTripleEnv env P q Q E :=
  h

/-- **A total prefix, then a partial rest**: the prefix's `wpEnv` with the
rest's `PartialWpEnv` as its fall-through postcondition. -/
theorem PartialWpEnv.of_wpEnv {q p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} {s : MachineData} {g : env.State}
    (h : cenv.wpEnv env q (PartialWpEnv env p Q E) E s g) : PartialWpEnv env (q ++ p) Q E s g := by
  intro pc hpl
  obtain ⟨h1, h2, h3⟩ := Executable.sits_append cenv q p pc hpl
  refine Safely.of_eventually_safely (h pc h1) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, hk⟩ | he)
  · dsimp only at ha hk
    subst ha
    rw [h3]
    exact hk _ h2
  · exact Safely.fold (.inl (.inr he))

/-- **A function's partial specification** at its entry address: `Pre`
reads the return address `ra` and the entry state (behind the caller's
`call`: `rsp` at the slot holding `ra`); every run returns to `ra` with
`Post` or runs forever. -/
def FunSpecPartialEnv (env : SharedEnv) (entry : Int64) (Pre : Int64 → MachineData → env.State → Prop)
    (Post : Int64 → MachineData → env.State → MachineData → env.State → Prop) : Prop :=
  ∀ ra t g, Pre ra t g →
    Safely (cenv.instrStepEnv env) (fun x => x.1.2 = ra ∧ Post ra t g x.1.1 x.2) ((t, entry), g)

/-- A total procedure specification is a partial one. -/
theorem FunSpecPartialEnv.of_procSpecEnv {entry : Int64} {Pre : Unit → Int64 → MachineData → env.State → Prop}
    {Post : Unit → Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : cenv.ProcSpecEnv env entry Pre Post) : FunSpecPartialEnv env entry (Pre ()) (Post ()) :=
  fun ra t g hp => Safely.of_eventually (h () ra t g hp)

/-- The state behind `call`'s push into a `dmem` slot: `rsp` lowered by 8,
the return address `ra` in the 8 bytes at the new `rsp`. -/
abbrev pushRA (s : MachineData) (ra : Int64) : MachineData :=
  { s with
    regs := s.regs.set64 .rsp (s.regs.get64 .rsp - Width.W64.bytesv)
    dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv) 8 ra.toBitVec.toInt }

/-- **The partial call rule** (`call l`, return-address slot in `dmem`):
through the callee's `FunSpecPartialEnv` at the label's address; the push
writes the mapped slot `rsp - 8` (`hslot`), the callee's return continues
with the rest of the caller from every `Post` state. For every return
address `ra` (the address behind the `call`), `Pre` must hold of the pushed
state `pushRA s ra`. -/
theorem PartialWpEnv.call {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop} (asz osz : Width) (l : Label)
    (hf : FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l) Pre Post) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    {s : MachineData} {g : env.State}
    (hslot : (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true)
    (h : ∀ ra, Pre ra (pushRA s ra) g ∧ ∀ s' g', Post ra (pushRA s ra) g s' g' → PartialWpEnv env p Q E s' g') :
    PartialWpEnv env (Directive.instr (.regular asz osz
      (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p) Q E s g := by
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  have hcancel : Int64.ofBitVec
      (pc + Int64.ofNat z +
        ((_root_.Executable.labels cenv).label l - (pc + Int64.ofNat z))).toBitVec
      = (_root_.Executable.labels cenv).label l := by
    rw [Int64.ofBitVec_toBitVec]
    apply Int64.toBitVec_inj.mp
    simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  have hafter : cenv.after pc (Directive.instr (.regular asz osz
      (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p) = cenv.after (pc + .ofNat z) p := by
    simp only [Executable.after, hseg]
  obtain ⟨w, hl⟩ := Option.isSome_iff_exists.mp hslot
  refine Safely.fold (.inr ⟨_, ⟨_, z, rest, hseg, Or.inr ?_⟩, fun _ h => h⟩)
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, Width.bytes, hl, Effects.AllEnv, hcancel]
  obtain ⟨hpre, hk⟩ := h (pc + .ofNat z)
  refine safely_bind (hf _ _ _ hpre) ?_
  rintro ⟨⟨s', a⟩, g'⟩ ⟨rfl, hpost⟩
  rw [hafter]
  exact hk s' g' hpost _ hpl'

/-- **The control-flow rule for a function fragment**, partial correctness:
`cfgEnv_partial_at` where each block may also exit by `E` (a `ret`, whose
target is read from the stack), and the last block never falls through. The
conclusion is the run from the entry label's address into `E`. -/
theorem cfgEnv_partial_fun {p p' : Program} {E : Int64 → MachineData → env.State → Prop} {l₀ : Label}
    (T : Label → MachineData → env.State → Prop)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g => T l s g ∧ s = s₀ ∧ g = g₀ ⦄ (⟨blk.body⟩ : EnvProgram env)
      ⦃ (match blk.next with
         | some l' => fun _ s g => T l' s g
         | none => fun _ _ _ => False);
        fun a s g => Table.ofLabelsEnv (fun l' s g => (Program.blockAt p l').isSome ∧ T l' s g
          ∧ Program.EdgeSafe p l s₀ g₀ l' s g) a s g ∨ E a s g ⦄)
    (hp : p = Directive.label l₀ :: p') (hwf : Program.WF p) (hpl : Program.PlacedIn p) :
    ∀ s g, T l₀ s g → Safely (cenv.instrStepEnv env) (fun x => E x.1.2 x.1.1 x.2)
      ((s, (_root_.Executable.labels cenv).label l₀), g) := by
  have hnd := hwf.nodup
  intro s g hT
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length := Program.blockIdx_le p
  let μ : Label → Nat := fun l => (Program.view p).2.length - Program.blockIdx p l
  have key := Program.linkEnv_partial (env := env)
    (post := fun x => E x.1.2 x.1.1 x.2)
    (fun l => (Program.blockAt p l).elim [] (·.body))
    (fun l => (_root_.Executable.labels cenv).label l)
    (fun l s g => (Program.blockAt p l).isSome ∧ T l s g)
    (fun j i => μ j < μ i) (measure μ).wf ?_ ?_
  · exact key l₀ s g ⟨Program.blockAt_entry' hp, hT⟩
  · intro l
    cases hb : Program.blockAt p l with
    | none => exact trivial
    | some blk => simpa using hpl.block l blk hb
  · intro l s₀ g₀
    cases hb : Program.blockAt p l with
    | none => exact fun s g hpre => absurd hpre.1.1 (by simp)
    | some blk =>
      simp only [Option.elim]
      rintro s g ⟨⟨-, hTl⟩, rfl, rfl⟩
      have hidx : Program.blockIdx p l < (Program.view p).2.length := Program.blockIdx_lt hnd hb
      have hw := (hblocks l blk hb s g).le_wp s g ⟨hTl, rfl, rfl⟩
      rw [wpEnv_eq] at hw
      refine Executable.wpEnv_mono ?_ ?_ hw
      · intro s' g' hq
        cases hnx : blk.next with
        | some l' =>
          rw [hnx] at hq
          obtain ⟨hsome', hidx'⟩ := Program.blockAt_next hnd hb hnx
          refine Or.inr ⟨l', (hpl.next l blk l' hb hnx).symm, ⟨hsome', hq⟩, .inl ?_⟩
          simp only [μ]
          omega
        | none =>
          rw [hnx] at hq
          exact hq.elim
      · rintro a s' g' (⟨l', hlab, hsome', hTl', hedge⟩ | he)
        · refine Or.inr ⟨l', hlab, ⟨hsome', hTl'⟩, ?_⟩
          rcases hedge with hlt | hne
          · have hle' : Program.blockIdx p l' ≤ (Program.view p).2.length := hK l'
            refine .inl ?_
            simp only [μ]
            omega
          · exact .inr fun ⟨_, h1, h2⟩ => hne ⟨h1, h2⟩
        · exact Or.inl he

/-- **A function's partial specification from its control-flow graph**: the
fragment `p` (entry label `l₀`) placed in the ambient code, its table
`T ra t g` (which may read the return address and the entry snapshot) holding
at entry, and its blocks exiting only by `ret` to `ra` with `Post` (or by
jumps to its own labels). -/
theorem FunSpecPartialEnv.of_cfg {p p' : Program} {l₀ : Label} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (T : Int64 → MachineData → env.State → Label → MachineData → env.State → Prop)
    (hp : p = Directive.label l₀ :: p') (hwf : Program.WF p) (hpl : Program.PlacedIn p)
    (hT : ∀ ra t g, Pre ra t g → T ra t g l₀ t g)
    (hblocks : ∀ ra t g, Pre ra t g → ∀ l blk, Program.blockAt p l = some blk →
      ∀ (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g' => T ra t g l s g' ∧ s = s₀ ∧ g' = g₀ ⦄ (⟨blk.body⟩ : EnvProgram env)
      ⦃ (match blk.next with
         | some l' => fun _ s g' => T ra t g l' s g'
         | none => fun _ _ _ => False);
        fun a s g' => Table.ofLabelsEnv (fun l' s g' => (Program.blockAt p l').isSome ∧ T ra t g l' s g'
          ∧ Program.EdgeSafe p l s₀ g₀ l' s g') a s g' ∨ (a = ra ∧ Post ra t g s g') ⦄) :
    FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l₀) Pre Post :=
  fun ra t g hpre =>
    cfgEnv_partial_fun (E := fun a s g' => a = ra ∧ Post ra t g s g') (T ra t g) (hblocks ra t g hpre) hp hwf
      hpl t g (hT ra t g hpre)

end MachineWP
