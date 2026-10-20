/-
The environment-aware machine wp for x64.

`Effects.All` is `False` at every access outside `dmem`. Here those accesses
are answered by a `SharedEnv`: a read returns any value the environment allows
(its *rely*), and an access is permitted only if the environment says so (its
*guarantee*, which also carries the access discipline: exactly a shared
location at its width). The design note is `Kraken/Promising/EnvWP.md`.

- `SharedAccess`, `SharedEnv`: the interface. Values are 128-bit payloads with
  an explicit byte count (1, 2, 4, 8 or 16), so the interface does not depend on the
  Promising machine's `Loc`/`Val`. They are ISA-free and live in
  `Kraken.SharedEnv` (with `FenceInv`/`FencesSkip`, the pieces of a
  non-atomic access, `SharedEnv.none` and `SharedEnv.lastWrite`), which
  AArch64's `Kraken/AArch64/EnvWP.lean` imports as well.
- `Effects.AllEnv`: `All` with every off-`dmem` access consulting the
  environment. Atomic accesses are one event (16-byte vector moves,
  `lock cmpxchg16b`); a non-atomic vector access is 8-byte pieces in address
  order.
- `Executable.stepAtEnv`, `instrStepEnv`, `wpEnv`, `ProcSpecEnv`: `Kraken.Step`
  and the `MachineWP` core over `MachineState × env.State`.
- The lifting theorem: `Effects.allEnv_of_all`,
  `Executable.eventually_instrStepEnv_of_instrStep`, `Executable.wpEnv_of_wp`,
  `MachineWP.wpEnv_of_triple`, `Executable.ProcSpec.env`. Every existing
  `MachineWP` rule and judgment carries over unchanged, with any
  fence-stable invariant `I` of the environment state framed on.
- `SharedEnv.none` (no shared locations, `allEnv_none_iff`) and
  `SharedEnv.lastWrite` (the one-thread instance, shape (i)).

This file imports the x64 stack and nothing from `Kraken.Promising`; the
statements that mention the Promising machine are in
`Kraken.Promising.EnvWPX64`.
-/
import Kraken.SharedEnv
import Kraken.MachineWP

open Kraken

namespace Kraken

/-- An `rmw`'s operation on a `w`-wide location, on 128-bit payloads. -/
def rmwOp128 (w : Width) (op : w.type → Option w.type) : BitVec 128 → Option (BitVec 128) :=
  fun x => (op (x.setWidth w.bits)).map (·.setWidth 128)

end Kraken

/-! ## `AllEnv` -/

/-- `Effects.All`, with every access outside `dmem` answered by `env`: the
access must be permitted (`env.ok`) and the run continues from every outcome
`env.step` allows, in the environment state it leaves. `post` sees the final
machine state and environment state. `unimplemented` and `gp_unaligned` stay
`False`; the access checks pass through, as in `All` (the access discipline
is `env.ok`'s, at the access itself). A thread's `dmem` passes through the
environment unchanged. -/
def Effects.AllEnv (env : SharedEnv) (g : env.State) (post : MachineState → env.State → Prop) :
    Effects → Prop
  | .done a => post a g
  | .unimplemented _ => False
  | .gp_unaligned .. => False
  | .nonmem_load dmem addr w ret =>
    env.ok (.load .plain false addr w.bytes) g ∧
      ∀ v g', env.step (.load .plain false addr w.bytes) g v g' →
        (ret (v.setWidth w.bits) dmem).AllEnv env g' post
  | .nonmem_store dmem addr (w := w) v ret =>
    env.ok (.store .plain false addr w.bytes (v.setWidth 128)) g ∧
      ∀ b g', env.step (.store .plain false addr w.bytes (v.setWidth 128)) g b g' →
        (ret dmem).AllEnv env g' post
  | @Effects.undefined α _ ret => ∀ v : α, (ret v).AllEnv env g post
  | .require_read_access _ _ ok => (ok ()).AllEnv env g post
  | .require_write_access _ _ ok => (ok ()).AllEnv env g post
  | .require_exec_access _ ok => (ok ()).AllEnv env g post
  | .sync_load k xcl dmem addr w ret =>
    env.ok (.load k xcl addr w.bytes) g ∧
      ∀ v g', env.step (.load k xcl addr w.bytes) g v g' →
        (ret (v.setWidth w.bits) dmem).AllEnv env g' post
  | .sync_store k xcl dmem addr (w := w) v ret =>
    env.ok (.store k xcl addr w.bytes (v.setWidth 128)) g ∧
      ∀ b g', env.step (.store k xcl addr w.bytes (v.setWidth 128)) g b g' →
        (ret b dmem).AllEnv env g' post
  | .rmw k dmem addr w op ret =>
    env.ok (.rmw k addr w.bytes (rmwOp128 w op)) g ∧
      ∀ old g', env.step (.rmw k addr w.bytes (rmwOp128 w op)) g old g' →
        (ret (old.setWidth w.bits) dmem).AllEnv env g' post
  | .fence k ok =>
    env.ok (.fence k) g ∧ ∀ g', env.step (.fence k) g () g' → (ok ()).AllEnv env g' post
  | .require_read_access_avx _ _ _ ok => (ok ()).AllEnv env g post
  | .require_write_access_avx _ _ _ ok => (ok ()).AllEnv env g post
  -- A guaranteed-atomic vector access (the aligned 16-byte moves) is one event.
  | .nonmem_load_avx true dmem addr w ret =>
    env.ok (.load .plain false addr w.bytes) g ∧
      ∀ v g', env.step (.load .plain false addr w.bytes) g v g' →
        (ret (v.setWidth w.bits) dmem).AllEnv env g' post
  -- Any other vector access is 8-byte pieces in address order (`SharedEnv.LoadPieces`).
  | .nonmem_load_avx false dmem addr w ret =>
    env.LoadPieces addr (w.bytes / 8) g
      (fun vs g' => (ret (ofPieces w.bits vs) dmem).AllEnv env g' post)
  | .nonmem_store_avx true dmem addr (w := w) v ret =>
    env.ok (.store .plain false addr w.bytes (v.setWidth 128)) g ∧
      ∀ b g', env.step (.store .plain false addr w.bytes (v.setWidth 128)) g b g' →
        (ret dmem).AllEnv env g' post
  | .nonmem_store_avx false dmem addr (w := w) v ret =>
    env.StorePieces addr (toPieces v (w.bytes / 8)) g (fun g' => (ret dmem).AllEnv env g' post)
  -- `lock cmpxchg16b`: one atomic 16-byte event.
  | .rmw16 k dmem addr op ret =>
    env.ok (.rmw k addr 16 op) g ∧
      ∀ old g', env.step (.rmw k addr 16 op) g old g' → (ret old dmem).AllEnv env g' post

/-! ## The lifting theorem, for one tree -/

/-- **Lifting, one tree.** An `All` judgment is an `AllEnv` judgment for every
environment, with any fence-stable invariant of the environment state framed
on: `All` is `False` exactly where `AllEnv` consults the environment, except
at fences. -/
theorem Effects.allEnv_of_all {env : SharedEnv} {I : env.State → Prop} (hI : env.FenceInv I)
    {post : MachineState → Prop} (e : Effects) :
    e.All post → ∀ g, I g → e.AllEnv env g (fun s g' => post s ∧ I g') := by
  induction e with
  | done a => exact fun h g hg => ⟨h, hg⟩
  | fence k ok ih =>
    intro h g hg
    exact ⟨(hI k g hg).1, fun g' hs => ih () h g' ((hI k g hg).2 g' hs)⟩
  | undefined ret ih => exact fun h g hg v => ih v (h v) g hg
  | require_read_access _ _ ok ih => exact fun h g hg => ih () h g hg
  | require_write_access _ _ ok ih => exact fun h g hg => ih () h g hg
  | require_exec_access _ ok ih => exact fun h g hg => ih () h g hg
  | require_read_access_avx _ _ _ ok ih => exact fun h g hg => ih () h g hg
  | require_write_access_avx _ _ _ ok ih => exact fun h g hg => ih () h g hg
  | nonmem_load_avx atomic => cases atomic <;> exact fun h => h.elim
  | nonmem_store_avx atomic => cases atomic <;> exact fun h => h.elim
  | _ => exact fun h => h.elim

/-- `AllEnv` is monotone in the postcondition. -/
theorem Effects.AllEnv.mono {env : SharedEnv} {post₁ post₂ : MachineState → env.State → Prop}
    (hp : ∀ s g, post₁ s g → post₂ s g) (e : Effects) :
    ∀ g, e.AllEnv env g post₁ → e.AllEnv env g post₂ := by
  have pieces_load : ∀ (addr : BitVec 64) n g (k₁ k₂ : List (BitVec 64) → env.State → Prop),
      (∀ vs g, k₁ vs g → k₂ vs g) → env.LoadPieces addr n g k₁ → env.LoadPieces addr n g k₂ := by
    intro addr n
    induction n generalizing addr with
    | zero => exact fun g k₁ k₂ hk h => hk _ _ h
    | succ n ih =>
      exact fun g k₁ k₂ hk h => ⟨h.1, fun v g' hs =>
        ih (addr + 8) g' _ _ (fun vs g'' => hk _ g'') (h.2 v g' hs)⟩
  have pieces_store : ∀ (ps : List (BitVec 64)) (addr : BitVec 64) g (k₁ k₂ : env.State → Prop),
      (∀ g, k₁ g → k₂ g) → env.StorePieces addr ps g k₁ → env.StorePieces addr ps g k₂ := by
    intro ps
    induction ps with
    | nil => exact fun addr g k₁ k₂ hk h => hk _ h
    | cons p ps ih =>
      exact fun addr g k₁ k₂ hk h => ⟨h.1, fun b g' hs => ih (addr + 8) g' _ _ hk (h.2 b g' hs)⟩
  induction e with
  | done a => exact fun g h => hp _ _ h
  | unimplemented => exact fun _ h => h
  | gp_unaligned => exact fun _ h => h
  | nonmem_load dmem addr w ret ih => exact fun g h => ⟨h.1, fun v g' hs => ih _ _ g' (h.2 v g' hs)⟩
  | nonmem_store dmem addr v ret ih => exact fun g h => ⟨h.1, fun b g' hs => ih _ g' (h.2 b g' hs)⟩
  | undefined ret ih => exact fun g h v => ih v g (h v)
  | require_read_access _ _ ok ih => exact fun g h => ih () g h
  | require_write_access _ _ ok ih => exact fun g h => ih () g h
  | require_exec_access _ ok ih => exact fun g h => ih () g h
  | sync_load k xcl dmem addr w ret ih => exact fun g h => ⟨h.1, fun v g' hs => ih _ _ g' (h.2 v g' hs)⟩
  | sync_store k xcl dmem addr v ret ih => exact fun g h => ⟨h.1, fun b g' hs => ih _ _ g' (h.2 b g' hs)⟩
  | rmw k dmem addr w op ret ih => exact fun g h => ⟨h.1, fun v g' hs => ih _ _ g' (h.2 v g' hs)⟩
  | fence k ok ih => exact fun g h => ⟨h.1, fun g' hs => ih () g' (h.2 g' hs)⟩
  | require_read_access_avx _ _ _ ok ih => exact fun g h => ih () g h
  | require_write_access_avx _ _ _ ok ih => exact fun g h => ih () g h
  | nonmem_load_avx atomic dmem addr w ret ih =>
    cases atomic
    · exact fun g h => pieces_load _ _ g _ _ (fun vs g' => ih _ _ g') h
    · exact fun g h => ⟨h.1, fun v g' hs => ih _ _ g' (h.2 v g' hs)⟩
  | nonmem_store_avx atomic dmem addr v ret ih =>
    cases atomic
    · exact fun g h => pieces_store _ _ g _ _ (fun g' => ih _ g') h
    · exact fun g h => ⟨h.1, fun b g' hs => ih _ g' (h.2 b g' hs)⟩
  | rmw16 k dmem addr op ret ih => exact fun g h => ⟨h.1, fun v g' hs => ih _ _ g' (h.2 v g' hs)⟩

/-- With no shared locations, `AllEnv` is `All`. -/
theorem Effects.allEnv_none_iff {post : MachineState → Prop} (e : Effects) :
    e.AllEnv SharedEnv.none () (fun s _ => post s) ↔ e.All post := by
  induction e with
  | done a => exact Iff.rfl
  | unimplemented => exact Iff.rfl
  | gp_unaligned => exact Iff.rfl
  | fence k ok ih =>
    exact ⟨fun h => (ih ()).mp (h.2 () trivial), fun h => ⟨trivial, fun _ _ => (ih ()).mpr h⟩⟩
  | undefined ret ih => exact forall_congr' ih
  | require_read_access _ _ ok ih => exact ih ()
  | require_write_access _ _ ok ih => exact ih ()
  | require_exec_access _ ok ih => exact ih ()
  | require_read_access_avx _ _ _ ok ih => exact ih ()
  | require_write_access_avx _ _ _ ok ih => exact ih ()
  | nonmem_load_avx atomic dmem addr w ret =>
    cases atomic
    · cases w <;> exact ⟨fun h => h.1.elim, fun h => h.elim⟩
    · exact ⟨fun h => h.1.elim, fun h => h.elim⟩
  | @nonmem_store_avx atomic dmem addr w v ret =>
    cases atomic
    · cases w <;> exact ⟨fun h => h.1.elim, fun h => h.elim⟩
    · exact ⟨fun h => h.1.elim, fun h => h.elim⟩
  | _ => exact ⟨fun h => h.1.elim, fun h => h.elim⟩

/-! ## The step relation -/

/-- `Executable.stepAt` with the environment: running the cell `(d, z)` at
`st`, every resolution falls through or every resolution jumps, the accesses
outside `dmem` answered by `env`. -/
def Kraken.Executable.stepAtEnv (e : Kraken.Executable Directive) (env : SharedEnv) (d : Directive)
    (z : Nat) (st : MachineState × env.State) (post : MachineState × env.State → Prop) : Prop :=
  (@Directive.interp (_root_.Executable.labels e) d st.1.1 (.mk st.1.2 (st.1.2 + .ofNat z))
      (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).AllEnv env st.2
    (fun m g => post ((m.1, st.1.2 + .ofNat z), g))
  ∨ (@Directive.interp (_root_.Executable.labels e) d st.1.1 (.mk st.1.2 (st.1.2 + .ofNat z))
      (fun _ => .unimplemented "fallthrough") (fun pc' s' => .done (s', pc'))).AllEnv env st.2
    (fun m g => post (m, g))

/-- `Executable.instrStep` with the environment: one instruction of the
ambient code, its environment state threaded through. -/
def Kraken.Executable.instrStepEnv (e : Kraken.Executable Directive) (env : SharedEnv)
    (st : MachineState × env.State) (post : MachineState × env.State → Prop) : Prop :=
  ∃ d z rest, e.codeAt st.1.2 = (d, z) :: rest ∧ e.stepAtEnv env d z st post

/-! ## The lifting theorem, for runs -/

/-- **Lifting, one instruction.** -/
theorem Kraken.Executable.instrStepEnv_of_instrStep {e : Kraken.Executable Directive}
    {env : SharedEnv} {I : env.State → Prop} (hI : env.FenceInv I) {st : MachineState}
    {post : MachineState → Prop} (h : e.instrStep st post) (g : env.State) (hg : I g) :
    e.instrStepEnv env (st, g) (fun x => post x.1 ∧ I x.2) := by
  obtain ⟨d, z, rest, hcode, hstep⟩ := h
  refine ⟨d, z, rest, hcode, ?_⟩
  rcases hstep with h | h
  · exact .inl (Effects.allEnv_of_all hI _ h g hg)
  · exact .inr (Effects.allEnv_of_all hI _ h g hg)

/-- **Lifting, runs.** Every `Eventually e.instrStep` judgment (every `vcgen`
triple, `ProcSpec`, `cfg` conclusion) is an environment judgment for every
environment, from any environment state satisfying a fence-stable `I`, which
also holds at the end. -/
theorem Kraken.Executable.eventually_instrStepEnv_of_instrStep {e : Kraken.Executable Directive}
    {env : SharedEnv} {I : env.State → Prop} (hI : env.FenceInv I) {P : MachineState → Prop}
    {st : MachineState} (h : Eventually e.instrStep P st) :
    ∀ g, I g → Eventually (e.instrStepEnv env) (fun x => P x.1 ∧ I x.2) (st, g) := by
  induction h with
  | done st hP => exact fun g hg => .done _ ⟨hP, hg⟩
  | step st mid hT _ ih =>
    exact fun g hg => .step _ _ (instrStepEnv_of_instrStep hI hT g hg) fun x hx => ih x.1 hx.1 x.2 hx.2

/-! ## The wp -/

/-- `Executable.wp` with the environment: the fragment `q`, placed anywhere in
the ambient code, run from `s` in environment state `g`. -/
def Kraken.Executable.wpEnv (e : Kraken.Executable Directive) (env : SharedEnv) (q : Program)
    (Q : MachineData → env.State → Prop) (E : Int64 → MachineData → env.State → Prop)
    (s : MachineData) (g : env.State) : Prop :=
  ∀ (pc : Int64), e.sits pc q →
    Eventually (e.instrStepEnv env)
      (fun x => (x.1.2 = e.after pc q ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2) ((s, pc), g)

theorem Kraken.Executable.wpEnv_mono {e : Kraken.Executable Directive} {env : SharedEnv} {q : Program}
    {Q₁ Q₂ : MachineData → env.State → Prop} {E₁ E₂ : Int64 → MachineData → env.State → Prop}
    (hQ : ∀ s g, Q₁ s g → Q₂ s g) (hE : ∀ a s g, E₁ a s g → E₂ a s g)
    {s : MachineData} {g : env.State} (h : e.wpEnv env q Q₁ E₁ s g) : e.wpEnv env q Q₂ E₂ s g :=
  fun pc hpl => eventually_weaken _ _ _ _
    (fun _ hst => hst.imp (fun ⟨ha, hq⟩ => ⟨ha, hQ _ _ hq⟩) (hE _ _ _)) (h pc hpl)

/-- `wp_cons` with the environment. -/
theorem Kraken.Executable.wpEnv_cons {e : Kraken.Executable Directive} {env : SharedEnv}
    {d : Directive} {q : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} {s : MachineData} {g : env.State}
    (h : e.wpEnv env [d] (fun s' g' => e.wpEnv env q Q E s' g') E s g) :
    e.wpEnv env (d :: q) Q E s g := by
  intro pc hpl
  have hcont : ∀ pc', e.sits pc' q → ∀ x : MachineState × env.State,
      (x.1.2 = pc' ∧ e.wpEnv env q Q E x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2 →
      Eventually (e.instrStepEnv env)
        (fun x => (x.1.2 = e.after pc' q ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2) x := by
    intro pc' hq ⟨⟨sd, spc⟩, sg⟩ hst
    rcases hst with ⟨hpc, hwp⟩ | hE
    · dsimp only at hpc hwp
      subst hpc
      exact hwp _ hq
    · exact .done _ (Or.inr hE)
  cases d with
  | label l =>
    have h1 := h pc trivial
    exact eventually_trans _ _ _ _ h1 (hcont pc hpl)
  | instr i =>
    obtain ⟨z, rest, hcode, hq⟩ := hpl
    have h1 := h pc ⟨z, rest, hcode, trivial⟩
    simp only [Executable.after, hcode] at h1 ⊢
    exact eventually_trans _ _ _ _ h1 (hcont _ hq)
  | byteArray a =>
    obtain ⟨z, rest, hcode, hq⟩ := hpl
    have h1 := h pc ⟨z, rest, hcode, trivial⟩
    simp only [Executable.after, hcode] at h1 ⊢
    exact eventually_trans _ _ _ _ h1 (hcont _ hq)

/-- **Lifting, wp.** -/
theorem Kraken.Executable.wpEnv_of_wp {e : Kraken.Executable Directive} {env : SharedEnv}
    {I : env.State → Prop} (hI : env.FenceInv I) {q : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData} (h : e.wp q Q E s) (g : env.State) (hg : I g) :
    e.wpEnv env q (fun s' g' => Q s' ∧ I g') (fun a s' g' => E a s' ∧ I g') s g := fun pc hpl =>
  eventually_weaken _ _ _ _
    (fun _ hx => hx.1.imp (fun ⟨ha, hq⟩ => ⟨ha, hq, hx.2⟩) (fun he => ⟨he, hx.2⟩))
    (eventually_instrStepEnv_of_instrStep hI (h pc hpl) g hg)

namespace MachineWP

open Std.WP

/-- A triple with the environment, on the ambient code: from every state and
environment state satisfying `P`, the run of `q` falls through with `Q` or
exits with `E`. -/
def TripleEnv [CodeEnv] (env : SharedEnv) (P : MachineData → env.State → Prop) (q : Program)
    (Q : MachineData → env.State → Prop) (E : Int64 → MachineData → env.State → Prop) : Prop :=
  ∀ s g, P s g → cenv.wpEnv env q Q E s g

/-- **Lifting, triples.** Every `vcgen` triple of the `MachineWP` logic is a
triple with the environment, for every environment, with a fence-stable
invariant of the environment state framed on. -/
theorem wpEnv_of_triple [CodeEnv] {env : SharedEnv} {I : env.State → Prop} (hI : env.FenceInv I)
    {P : MachineData → Prop} {q : Program} {Q : Unit → MachineData → Prop}
    {E : Int64 → MachineData → Prop} (h : ⦃ P ⦄ q ⦃ Q; E ⦄) :
    TripleEnv env (fun s g => P s ∧ I g) q (fun s g => Q () s ∧ I g) (fun a s g => E a s ∧ I g) :=
  fun s g ⟨hp, hg⟩ => Executable.wpEnv_of_wp hI (h.le_wp s hp) g hg

end MachineWP

/-! ## Procedures -/

/-- `ProcSpec` with the environment. -/
def Kraken.Executable.ProcSpecEnv (e : Kraken.Executable Directive) (env : SharedEnv) (entry : Int64)
    {α : Type} (Pre : α → Int64 → MachineData → env.State → Prop)
    (Post : α → Int64 → MachineData → env.State → MachineData → env.State → Prop) : Prop :=
  ∀ (x : α) (ra : Int64) (t : MachineData) (g : env.State), Pre x ra t g →
    Eventually (e.instrStepEnv env) (fun st => st.1.2 = ra ∧ Post x ra t g st.1.1 st.2) ((t, entry), g)

/-- **Lifting, procedure specifications.** -/
theorem Kraken.Executable.ProcSpec.env {e : Kraken.Executable Directive} {entry : Int64} {α : Type}
    {Pre : α → Int64 → MachineData → Prop} {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : e.ProcSpec entry Pre Post) (env : SharedEnv) {I : env.State → Prop} (hI : env.FenceInv I) :
    e.ProcSpecEnv env entry (fun x ra t g => Pre x ra t ∧ I g) (fun x ra t _ t' g' => Post x ra t t' ∧ I g') :=
  fun x ra t g ⟨hp, hg⟩ => eventually_weaken _ _ _ _ (fun _ hst => ⟨hst.1.1, hst.1.2, hst.2⟩)
    (Executable.eventually_instrStepEnv_of_instrStep hI (h x ra t hp) g hg)

/-! ## Targets: the shared-location rules

The typical shape of a shared-location rule, stated for two instructions.
`Kraken/EnvWPRules.lean` proves them (`MachineWP.mov_store_shared`,
`MachineWP.xchg_shared`) and their
siblings (`Kraken/X64/Examples/EnvWP.lean` proved
the load, `mov32_load_shared_env`, as a prototype). Where the `MachineWP` rule
asks for the address to be mapped, the shared rule asks for it to be outside
`dmem`, for the access to be permitted, and for the tail's wp at every outcome
the environment allows. -/

namespace MachineWP

/-- `movq %r, d(%b)` on a location outside `dmem`: a plain 8-byte store; the
tail runs in every environment state the store may leave. -/
def MovStoreSharedRule : Prop :=
  ∀ [CodeEnv] (env : SharedEnv) (b : Reg64) (d : Int64) (r : Reg64) (p : Program)
    (Q : MachineData → env.State → Prop) (E : Int64 → MachineData → env.State → Prop),
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let v := (s.regs.get64 r).setWidth 128
        Mem.loadInt s.dmem a 8 = none ∧ env.ok (.store .plain false a 8 v) g ∧
          ∀ ok g', env.step (.store .plain false a 8 v) g ok g' → cenv.wpEnv env p Q E s g')
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W64))))) :: p)
      Q E

/-- `xchgq %r, d(%b)` on a location outside `dmem`: one atomic `rmw` (x86's
`lock` kind, `acqRel`) that writes `r`; the old value lands in `r`. -/
def XchgSharedRule : Prop :=
  ∀ [CodeEnv] (env : SharedEnv) (r b : Reg64) (d : Int64) (p : Program)
    (Q : MachineData → env.State → Prop) (E : Int64 → MachineData → env.State → Prop),
    TripleEnv env
      (fun s g =>
        let a := s.regs.get64 b + d.toBitVec
        let acc := SharedAccess.rmw .acqRel a 8 (rmwOp128 .W64 (fun _ => some (s.regs.get64 r)))
        Mem.loadInt s.dmem a 8 = none ∧ env.ok acc g ∧
          ∀ old g', env.step acc g old g' →
            cenv.wpEnv env p Q E { s with regs := s.regs.set64 r (old.setWidth 64) } g')
      (Directive.instr (.regular .W64 .W64
          (.xchg (.low r .W64) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p)
      Q E

end MachineWP

