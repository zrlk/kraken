/-
**Calls inside loops for fragment specifications,
x64.** Generic. The x64 twin of
`Lower/FragSpecLoopCalls.lean` (the loop-call rules), over the x64 `FragSpecEnvL`
(`Lower/FragSpecCallsX64.lean`), with the same names in `MachineWP` (the
AArch64 and x64 layers cannot be co-imported).

- `Program.linkEnv_partialS`: `Program.linkEnv_partial` with `Safely`
  premises; each fragment's run is a `Safely` run into `Program.ContSafe`
  (the zero-step guard), or **takes a step first** and then runs `Safely` to
  any fragment entry (no guard).
- `PartialWpEnvS` (the step-first partial wp), `.toPartial`, `.of_wpEnv` (a
  total exit-free prefix, then a stepping rest), and `PartialWpEnv.of_triple`
  (a plain `vcgen` block).
- **The register-link call** (`Lower/KitX64Link.lean`): `leaq ret_k(%rip),
  %r11; jmp g; ret_k:`. On x64 the callee returns to a *label*, so the call
  ends its block and `ret_k: B` is the next block.
  - `PartialWpEnvS.jmpCall`: `jmp g` into a `FunSpecPartialEnv` at `g`'s
    address takes a step; from every `Post` state at the return address the
    run continues (into the block's exits).
  - `PartialWpEnvS.callLink`: `leaq ret_k(%rip), %r11; jmp g` (takes a
    step: the `leaq`), the callee's `Pre` at `ra := &ret_k` with `r11 = &ret_k`.
  - `PartialWpEnvS.call_triples`: the block `A; jmp g` (`A` a `vcgen` triple
    ending in the `leaq`) **together with** the return block `ret_k: B` (a
    `vcgen` triple at its label in the placed caller): the block's exits are
    `B`'s. So `B`'s back edges (a retry loop's) need no `EdgeSafe`, and the
    return block's own table entry may be `False` (it is entered only from
    the callee's return).
- `cfgEnv_partial_funS`: `cfgEnv_partial_fun` with each block a guarded
  `PartialWpEnv` (exits under `Program.EdgeSafe`) or an unguarded
  `PartialWpEnvS`.
- `FragSpecEnvL.of_cfgP`: the constructor over `fragF :: Gs`; the block
  obligations get the placement (callee specs by `FragSpecEnvL.at_sub`; the
  return block by `Program.PlacedIn`).

Scope: mutual recursion between fragments is not covered (a callee's spec is
an input, not a table entry). The return block `B` never falls through (it
ends in a jump: the retry's `jcc` plus `jmp *%r`).

Machine: the executable machine's per-thread environment semantics
(`Executable.instrStepEnv`), partial correctness (`Safely`), as
`FunSpecPartialEnv`/`FragSpecEnvL`.
-/
import Kraken.Promising.Lower.FragSpecCallsX64

open Kraken
open Std.WP

/-! ## The link with `Safely` premises -/

open MachineWP in
/-- **Partial-correctness link with partial premises** (x64; the AArch64
statement). Each fragment's run from its table entry is either a `Safely` run
into `Program.ContSafe` (the zero-step guard), or takes a step and then runs
`Safely` into `post` or to any fragment's entry with its table entry. -/
theorem Program.linkEnv_partialS [CodeEnv] {env : SharedEnv} {ι : Type}
    {post : MachineState × env.State → Prop}
    (entry : ι → Int64) (T : ι → MachineData → env.State → Prop)
    (r : ι → ι → Prop) (hwf : WellFounded r)
    (hfrag : ∀ i s g, T i s g →
      Safely (cenv.instrStepEnv env) (fun x => Program.ContSafe post entry T r i s g x.1.2 x.1.1 x.2)
        ((s, entry i), g) ∨
      ∃ R, cenv.instrStepEnv env ((s, entry i), g) R ∧ ∀ z, R z →
        Safely (cenv.instrStepEnv env) (fun x => post x ∨ ∃ j, entry j = x.1.2 ∧ T j x.1.1 x.2) z) :
    ∀ i s g, T i s g → Safely (cenv.instrStepEnv env) post ((s, entry i), g) := by
  let C : MachineState × env.State → Prop := fun x => post x ∨ ∃ j, entry j = x.1.2 ∧ T j x.1.1 x.2
  have hA : ∀ j s g, T j s g → post ((s, entry j), g) ∨
      ∃ R, cenv.instrStepEnv env ((s, entry j), g) R ∧ ∀ z, R z → Safely (cenv.instrStepEnv env) C z := by
    intro j
    induction j using hwf.induction with
    | _ j ih =>
      intro s g hT
      rcases hfrag j s g hT with hS | hS
      · rcases hS.unfold with hc | ⟨R, hR, hk⟩
        · rcases hc with hp | ⟨k, hk, hTk, hr | hne⟩
          · exact .inl hp
          · dsimp only at hk hTk
            rw [← hk]
            exact ih k hr s g hTk
          · exact absurd ⟨rfl, rfl, rfl⟩ hne
        · refine .inr ⟨R, hR, fun z hz => (hk z hz).mono ?_⟩
          rintro x (hp | ⟨k, hk, hTk, -⟩)
          · exact .inl hp
          · exact .inr ⟨k, hk, hTk⟩
      · exact .inr hS
  intro i s g hT
  refine ⟨Safely (cenv.instrStepEnv env) C, Safely.fold (.inl (.inr ⟨i, rfl, hT⟩)), ?_⟩
  intro y hy
  rcases hy.unfold with hc | ⟨R, hR, hk⟩
  · rcases hc with hp | ⟨j, hj, hTj⟩
    · exact .inl hp
    · obtain ⟨⟨s', pc⟩, g'⟩ := y
      dsimp only at hj hTj
      subst hj
      exact hA j s' g' hTj
  · exact .inr ⟨R, hR, hk⟩

namespace MachineWP

variable {env : SharedEnv}

/-! ## The step-first partial wp -/

section Step

variable [CodeEnv]

/-- **The step-first partial wp** of `q` at `(s, g)` (x64): placed anywhere,
the run takes a step, and then every run falls through with `Q`, exits with
`E`, or runs forever. A block ending in a register-link call is one. -/
def PartialWpEnvS (env : SharedEnv) (q : Program) (Q : MachineData → env.State → Prop)
    (E : Int64 → MachineData → env.State → Prop) (s : MachineData) (g : env.State) : Prop :=
  ∀ pc, cenv.sits pc q → ∃ R, cenv.instrStepEnv env ((s, pc), g) R ∧ ∀ z, R z →
    Safely (cenv.instrStepEnv env) (fun x => (x.1.2 = cenv.after pc q ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2) z

theorem PartialWpEnvS.toPartial {q : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} {s : MachineData} {g : env.State}
    (h : PartialWpEnvS env q Q E s g) : PartialWpEnv env q Q E s g :=
  fun pc hpl => Safely.fold (.inr (h pc hpl))

/-- **A jump into a callee, stepping** (the second half of a register-link
call): `jmp g` to a `FunSpecPartialEnv` at `g`'s address, with `Pre` at the
return address `ra` (the link register's value, in `Pre`), takes a step; from
every `Post` state at `ra` the run continues into the block's exits. -/
theorem PartialWpEnvS.jmpCall {asz osz : Width} {lg : Label} {ra : Int64}
    {PreG : Int64 → MachineData → env.State → Prop}
    {PostG : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (hf : FunSpecPartialEnv env ((_root_.Executable.labels cenv).label lg) PreG PostG) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    {s : MachineData} {g : env.State} (hpre : PreG ra s g)
    (hk : ∀ s' g', PostG ra s g s' g' →
      Safely (cenv.instrStepEnv env) (fun x => E x.1.2 x.1.1 x.2) ((s', ra), g')) :
    PartialWpEnvS env (Directive.instr (.regular asz osz
      (.jmp (.rel (.sub (.label lg) .after_current_instruction)))) :: p) Q E s g := by
  intro pc hpl
  obtain ⟨z, rest, hseg, -⟩ := hpl
  have hcancel : pc + .ofNat z + ((_root_.Executable.labels cenv).label lg - (pc + .ofNat z))
      = (_root_.Executable.labels cenv).label lg := by
    apply Int64.toBitVec_inj.mp
    simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  refine ⟨_, ⟨_, z, rest, hseg, Or.inr ?_⟩, fun _ h => h⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, Effects.AllEnv, hcancel]
  exact hf.jcallLink hpre fun s' g' h => (hk s' g' h).mono fun _ h => .inr h

/-- **The register-link call, stepping** (x64): `leaq ret_k(%rip), %r11;
jmp g` takes a step (the `leaq`); `g`'s `Pre` at `ra := &ret_k` of the state
with `r11 = &ret_k`, and from every `Post` state at `&ret_k` the run
continues into the block's exits. -/
theorem PartialWpEnvS.callLink {asz osz : Width} {lg lk : Label}
    {PreG : Int64 → MachineData → env.State → Prop}
    {PostG : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (hf : FunSpecPartialEnv env ((_root_.Executable.labels cenv).label lg) PreG PostG) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    {s : MachineData} {g : env.State}
    (h : let s₁ := { s with regs := s.regs.set64 .r11 ((_root_.Executable.labels cenv).label lk).toBitVec }
      PreG ((_root_.Executable.labels cenv).label lk) s₁ g ∧
      ∀ s' g', PostG ((_root_.Executable.labels cenv).label lk) s₁ g s' g' →
        Safely (cenv.instrStepEnv env) (fun x => E x.1.2 x.1.1 x.2)
          ((s', (_root_.Executable.labels cenv).label lk), g')) :
    PartialWpEnvS env (Directive.instr (.regular .W64 .W64
        (.lea (.low .r11 .W64) ⟨some .rip, none, .sub (.label lk) .after_current_instruction⟩)) ::
      Directive.instr (.regular asz osz
        (.jmp (.rel (.sub (.label lg) .after_current_instruction)))) :: p) Q E s g := by
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  have hafter : cenv.after pc (Directive.instr (.regular .W64 .W64
        (.lea (.low .r11 .W64) ⟨some .rip, none, .sub (.label lk) .after_current_instruction⟩)) ::
      Directive.instr (.regular asz osz
        (.jmp (.rel (.sub (.label lg) .after_current_instruction)))) :: p) =
      cenv.after (pc + .ofNat z) (Directive.instr (.regular asz osz
        (.jmp (.rel (.sub (.label lg) .after_current_instruction)))) :: p) := by
    simp only [Executable.after, hseg]
  refine ⟨_, ⟨_, z, rest, hseg, Or.inl ?_⟩, fun _ h => h⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg, Reg64s.set_low64,
    Effects.AllEnv, AddrExpr.zeroExtend_interp_rip_label]
  rw [hafter]
  exact (PartialWpEnvS.jmpCall hf h.1 h.2).toPartial _ hpl'

/-- **A total exit-free prefix, then a stepping rest**: the prefix either
steps, or (in zero steps) leaves the state at the rest, which steps. -/
theorem PartialWpEnvS.of_wpEnv {q p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} {s : MachineData} {g : env.State}
    (h : cenv.wpEnv env q (PartialWpEnvS env p Q E) (fun _ _ _ => False) s g) :
    PartialWpEnvS env (q ++ p) Q E s g := by
  intro pc hpl
  obtain ⟨h1, h2, h3⟩ := Executable.sits_append cenv q p pc hpl
  have hfix : ∀ x : MachineState × env.State,
      ((x.1.2 = cenv.after (cenv.after pc q) p ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2) →
      (x.1.2 = cenv.after pc (q ++ p) ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2 := by
    rw [h3]; exact fun _ h => h
  cases h pc h1 with
  | done _ hc =>
    rcases hc with ⟨ha, hk⟩ | hf
    · dsimp only at ha hk
      obtain ⟨R, hR, hk'⟩ := hk _ h2
      rw [← ha] at hR
      exact ⟨R, hR, fun z hz => (hk' z hz).mono hfix⟩
    · exact hf.elim
  | step _ mid hT hmid =>
    refine ⟨mid, hT, fun z hz => Safely.of_eventually_safely (hmid z hz) ?_⟩
    rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, hk⟩ | hf)
    · dsimp only at ha hk
      subst ha
      obtain ⟨R, hR, hk'⟩ := hk _ h2
      exact Safely.fold (.inr ⟨R, hR, fun z hz => (hk' z hz).mono hfix⟩)
    · exact hf.elim

/-- A straight-line `vcgen` triple as a `PartialWpEnv` (a plain block of a
cfg table; x64). -/
theorem PartialWpEnv.of_triple {q : Program} {P : MachineData → env.State → Prop}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    {s : MachineData} {g : env.State}
    (h : ⦃ P ⦄ (⟨q⟩ : EnvProgram env) ⦃ (fun _ s g => Q s g); E ⦄) (hp : P s g) :
    PartialWpEnv env q Q E s g := by
  have hw := h.le_wp s g hp
  rw [wpEnv_eq] at hw
  have h' : PartialWpEnv env (q ++ []) Q E s g :=
    PartialWpEnv.of_wpEnv (Executable.wpEnv_mono (fun _ _ h => PartialWpEnv.nil h) (fun _ _ _ h => h) hw)
  simpa using h'

/-- **A register-link call inside a loop** (x64): the block
`A; leaq ret_k(%rip), %r11; jmp g` of the placed caller `fragF`, together
with the return block `ret_k: B` at the label `lk`. `A` is a total exit-free
`vcgen` triple into `Mid1`; `hcall` gives `g`'s `Pre` at `ra := &ret_k` (with
`r11 = &ret_k`) and its `Post` into `Mid2`; `B` is a `vcgen` triple from
`Mid2` at its label that never falls through, with the block's exits `E`.
The block takes a step (`PartialWpEnvS`), so `B`'s exits (a retry's back
edge) need no `EdgeSafe`. -/
theorem PartialWpEnvS.call_triples {fragF A : Program} {asz osz : Width} {lg lk : Label}
    {blkK : Program.Block} (hpl : Program.PlacedIn fragF) (hbK : Program.blockAt fragF lk = some blkK)
    {PreG : Int64 → MachineData → env.State → Prop}
    {PostG : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (hg : FunSpecPartialEnv env ((_root_.Executable.labels cenv).label lg) PreG PostG)
    {P Mid1 Mid2 Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    {s : MachineData} {g : env.State}
    (hA : ⦃ P ⦄ (⟨A⟩ : EnvProgram env) ⦃ (fun _ s g' => Mid1 s g'); fun _ _ _ => False ⦄) (hp : P s g)
    (hcall : ∀ s g', Mid1 s g' →
      let s₁ := { s with regs := s.regs.set64 .r11 ((_root_.Executable.labels cenv).label lk).toBitVec }
      PreG ((_root_.Executable.labels cenv).label lk) s₁ g' ∧
      ∀ s' g'', PostG ((_root_.Executable.labels cenv).label lk) s₁ g' s' g'' → Mid2 s' g'')
    (hB : ∀ s₀ g₀, ⦃ fun s g' => Mid2 s g' ∧ s = s₀ ∧ g' = g₀ ⦄ (⟨blkK.body⟩ : EnvProgram env)
      ⦃ (fun _ _ _ => False); E ⦄) :
    PartialWpEnvS env (A ++ [Directive.instr (.regular .W64 .W64
        (.lea (.low .r11 .W64) ⟨some .rip, none, .sub (.label lk) .after_current_instruction⟩)),
      Directive.instr (.regular asz osz
        (.jmp (.rel (.sub (.label lg) .after_current_instruction))))]) Q E s g := by
  have h1 := hA.le_wp s g hp
  rw [wpEnv_eq] at h1
  refine PartialWpEnvS.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h1)
  intro s1 g1 hm
  refine PartialWpEnvS.callLink hg ⟨(hcall s1 g1 hm).1, fun s' g' hpost => ?_⟩
  have hw := (hB s' g').le_wp s' g' ⟨(hcall s1 g1 hm).2 s' g' hpost, rfl, rfl⟩
  rw [wpEnv_eq] at hw
  exact Safely.of_eventually (eventually_weaken _ _ _ _ (fun _ hx => hx.elim (fun h => h.2.elim) id)
    (hw _ (hpl.block lk blkK hbK)))

/-! ## The function cfg rule with partial blocks -/

/-- **The control-flow rule for a function fragment with partial blocks**
(x64): `cfgEnv_partial_fun` where each block's run from its table entry is a
`PartialWpEnv` (exits to the fragment's labels under the zero-step guard
`Program.EdgeSafe`), or a `PartialWpEnvS` (the block takes a step first, so
its exits need no guard). -/
theorem cfgEnv_partial_funS {p p' : Program} {E : Int64 → MachineData → env.State → Prop} {l₀ : Label}
    (T : Label → MachineData → env.State → Prop)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ (s₀ : MachineData) (g₀ : env.State), T l s₀ g₀ →
      PartialWpEnv env blk.body
        (match blk.next with
         | some l' => fun s g => T l' s g
         | none => fun _ _ => False)
        (fun a s g => Table.ofLabelsEnv (fun l' s g => (Program.blockAt p l').isSome ∧ T l' s g
          ∧ Program.EdgeSafe p l s₀ g₀ l' s g) a s g ∨ E a s g) s₀ g₀ ∨
      PartialWpEnvS env blk.body
        (match blk.next with
         | some l' => fun s g => T l' s g
         | none => fun _ _ => False)
        (fun a s g => Table.ofLabelsEnv (fun l' s g => (Program.blockAt p l').isSome ∧ T l' s g) a s g
          ∨ E a s g) s₀ g₀)
    (hp : p = Directive.label l₀ :: p') (hwf : Program.WF p) (hpl : Program.PlacedIn p) :
    ∀ s g, T l₀ s g → Safely (cenv.instrStepEnv env) (fun x => E x.1.2 x.1.1 x.2)
      ((s, (_root_.Executable.labels cenv).label l₀), g) := by
  have hnd := hwf.nodup
  intro s g hT
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length := Program.blockIdx_le p
  let μ : Label → Nat := fun l => (Program.view p).2.length - Program.blockIdx p l
  refine Program.linkEnv_partialS (env := env) (post := fun x => E x.1.2 x.1.1 x.2)
    (fun l => (_root_.Executable.labels cenv).label l)
    (fun l s g => (Program.blockAt p l).isSome ∧ T l s g)
    (fun j i => μ j < μ i) (measure μ).wf ?_ l₀ s g ⟨Program.blockAt_entry' hp, hT⟩
  rintro l s₀ g₀ ⟨hsome, hTl⟩
  cases hb : Program.blockAt p l with
  | none => rw [hb] at hsome; cases hsome
  | some blk =>
    have hidx : Program.blockIdx p l < (Program.view p).2.length := Program.blockIdx_lt hnd hb
    have hsits := hpl.block l blk hb
    rcases hblocks l blk hb s₀ g₀ hTl with h | h
    · refine .inl ((h _ hsits).mono ?_)
      rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, hq⟩ | ⟨l', hlab, hsome', hTl', hedge⟩ | he)
      · dsimp only at ha hq
        cases hnx : blk.next with
        | some l' =>
          rw [hnx] at hq
          obtain ⟨hsome', -⟩ := Program.blockAt_next hnd hb hnx
          obtain ⟨-, hidx'⟩ := Program.blockAt_next hnd hb hnx
          refine Or.inr ⟨l', ha ▸ (hpl.next l blk l' hb hnx).symm, ⟨hsome', hq⟩, .inl ?_⟩
          simp only [μ]
          omega
        | none =>
          rw [hnx] at hq
          exact hq.elim
      · refine Or.inr ⟨l', hlab, ⟨hsome', hTl'⟩, ?_⟩
        rcases hedge with hlt | hne
        · have hle' : Program.blockIdx p l' ≤ (Program.view p).2.length := hK l'
          refine .inl ?_
          simp only [μ]
          omega
        · exact .inr fun ⟨_, h1, h2⟩ => hne ⟨h1, h2⟩
      · exact Or.inl he
    · obtain ⟨R, hR, hk⟩ := h _ hsits
      refine .inr ⟨R, hR, fun z hz => (hk z hz).mono ?_⟩
      rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, hq⟩ | ⟨l', hlab, hsome', hTl'⟩ | he)
      · dsimp only at ha hq
        cases hnx : blk.next with
        | some l' =>
          rw [hnx] at hq
          obtain ⟨hsome', -⟩ := Program.blockAt_next hnd hb hnx
          exact Or.inr ⟨l', ha ▸ (hpl.next l blk l' hb hnx).symm, hsome', hq⟩
        | none =>
          rw [hnx] at hq
          exact hq.elim
      · exact Or.inr ⟨l', hlab, hsome', hTl'⟩
      · exact Or.inl he

end Step

/-! ## The fragment constructor -/

/-- **The cfg-table constructor with calls in any block** (x64). `T ra t g`
is the table of the run entered with return address `ra` from `(t, g)`; it
holds at the entry label; in every code placing `fragF` and the callees'
fragments `Gs`, every block's run from its table entry is a guarded
`PartialWpEnv` or a stepping `PartialWpEnvS` (`cfgEnv_partial_funS`) that
keeps the table or returns to `ra` with `Post`. A register-link call inside a
block: `PartialWpEnvS.call_triples` with the callee's spec by
`FragSpecEnvL.at_sub`; the return block's table entry may be `False`. -/
theorem FragSpecEnvL.of_cfgP {fragF p' : Program} {Gs : List Program} {l₀ : Label}
    {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (T : Int64 → MachineData → env.State → Label → MachineData → env.State → Prop)
    (hp : fragF = Directive.label l₀ :: p') (hwf : Program.WF fragF)
    (hinit : ∀ ra t g, Pre ra t g → T ra t g l₀ t g)
    (hblocks : ∀ [CodeEnv], (∀ q ∈ fragF :: Gs, Program.PlacedIn q) → ∀ (ra : Int64) (t : MachineData)
      (g : env.State), Pre ra t g →
      ∀ l blk, Program.blockAt fragF l = some blk → ∀ (s₀ : MachineData) (g₀ : env.State), T ra t g l s₀ g₀ →
      PartialWpEnv env blk.body
        (match blk.next with
         | some l' => fun s g' => T ra t g l' s g'
         | none => fun _ _ => False)
        (fun a s g' => Table.ofLabelsEnv (fun l' s g' => (Program.blockAt fragF l').isSome ∧ T ra t g l' s g'
          ∧ Program.EdgeSafe fragF l s₀ g₀ l' s g') a s g' ∨ (a = ra ∧ Post ra t g s g')) s₀ g₀ ∨
      PartialWpEnvS env blk.body
        (match blk.next with
         | some l' => fun s g' => T ra t g l' s g'
         | none => fun _ _ => False)
        (fun a s g' => Table.ofLabelsEnv (fun l' s g' => (Program.blockAt fragF l').isSome ∧ T ra t g l' s g')
          a s g' ∨ (a = ra ∧ Post ra t g s g')) s₀ g₀) :
    FragSpecEnvL env (fragF :: Gs) l₀ Pre Post := by
  refine ⟨fun hpl ra t g hpre => ?_⟩
  exact cfgEnv_partial_funS (T ra t g) (E := fun a s g' => a = ra ∧ Post ra t g s g')
    (hblocks hpl ra t g hpre) hp hwf (hpl fragF List.mem_cons_self) t g (hinit ra t g hpre)

end MachineWP
