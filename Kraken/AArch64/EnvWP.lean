/-
The environment-aware machine wp for AArch64
(`Kraken/Promising/EnvWP.md` §7). Copied from x64's `Kraken/EnvWP.lean`,
adapted for AArch64's `Effects`.

`Effects.All` is `False` at every access outside `dmem`. Here those accesses
are answered by a `SharedEnv` (`Kraken.SharedEnv`, shared with x64): a read
returns any value the environment allows (its *rely*), and an access is
permitted only if the environment says so (its *guarantee*, which also
carries the access discipline: exactly a shared location at its width).

- `Effects.AllEnv`: `All` with every off-`dmem` access consulting the
  environment. AArch64 has no vector accesses, so there are no piece cases;
  `unaligned_sp` stays `False`, and so do the exclusive pairs (`LDXP`/`STXP`
  with both halves off `dmem`; deferred with LL/SC). A `CASP` with both halves
  off `dmem` is two per-half `rmw`s in either order (`SharedEnv.CaspEnv`), as
  the Promising machine performs it. A store-exclusive's success comes from the
  environment's `step` (the store's `Bool` outcome), which replaces `All`'s
  "always `False` off `dmem`" (the `∀ ok` pattern of the store-exclusive rules). An
  `rmw` drops the effect's `noRet` flag, which `SharedAccess.rmw` cannot
  carry; the environment must then be sound for the weaker `NoRet` reading
  (the note at `Effects.AllEnv`).
- `Executable.stepAtEnv`, `instrStepEnv`, `wpEnv`, `ProcSpecEnv`: AArch64's
  `Kraken.AArch64.WP.Step` and the `MachineWP` core over
  `MachineState × env.State`.
- The lifting theorem: `Effects.allEnv_of_all`,
  `Executable.eventually_instrStepEnv_of_instrStep`, `Executable.wpEnv_of_wp`,
  `MachineWP.wpEnv_of_triple`, `Executable.ProcSpec.env`. Every existing
  AArch64 `MachineWP` rule (W0–W4, mapped memory) carries over unchanged, with
  any fence-stable invariant `I` of the environment state framed on.

This file imports the AArch64 stack and nothing from `Kraken.Promising`; the
statements that mention the Promising machine are in
`Kraken.Promising.EnvWPAArch64`. The shared-location rules are in
`Kraken.AArch64.EnvWPRules`.
-/
import Kraken.SharedEnv
import Kraken.AArch64.WP.MachineWP

open Kraken

/-! ## `AllEnv` -/

/-- The environment reading of a compare-and-swap pair (`CASP`, the effect
`rmw_pair`) of kind `k` on the two `w`-sized halves at `addr` and
`addr + w.bytes`, continuing with `K o₁ o₂ g'` (the old halves and the final
environment state). It is the Promising machine's reading, `caspTree`
(`Kraken/Promising/AArch64.lean`), access for access: the pair is **not** one
atomic access (herd's `casp` combines the halves with `>>|`, not `>>||`), but
two `rmw`s of kind `k`, one per half, each atomic on its own half. The outcome
`succ` is chosen up front: on success each half writes its new value iff it
matches its comparand, on failure neither writes. Both orders of the halves
(`rev`) must be allowed, as the machine explores both. A run whose outcome
does not agree with `succ` (a half mismatched on the success branch, or both
matched on the failure branch) is dead in the machine (`choose 0`), so it
asks nothing here. In `lastWrite` this is one read of both halves and, on a
match, both writes (`SharedEnv.lastWrite_caspEnv_iff`). -/
def Kraken.SharedEnv.CaspEnv (env : SharedEnv) (k : RmwKind) (addr : BitVec 64) (w : MemWidth)
    (cmp1 cmp2 new1 new2 : w.type) (g : env.State) (K : w.type → w.type → env.State → Prop) : Prop :=
  ∀ succ rev : Bool,
    let op (cmp new : w.type) : BitVec 128 → Option (BitVec 128) :=
      rmwOpBits w.bits (fun old => if succ then (if old == cmp then some new else Option.none) else Option.none)
    let a₁ : SharedAccess := .rmw k addr w.bytes (op cmp1 new1)
    let a₂ : SharedAccess := .rmw k (addr + w.bytesv) w.bytes (op cmp2 new2)
    let fin (o₁ o₂ : w.type) (g' : env.State) : Prop := (o₁ == cmp1 && o₂ == cmp2) = succ → K o₁ o₂ g'
    if rev then
      env.ok a₂ g ∧ ∀ (v₂ : BitVec 128) g₁, env.step a₂ g v₂ g₁ →
        env.ok a₁ g₁ ∧ ∀ (v₁ : BitVec 128) g₂, env.step a₁ g₁ v₁ g₂ →
          fin (v₁.setWidth w.bits) (v₂.setWidth w.bits) g₂
    else
      env.ok a₁ g ∧ ∀ (v₁ : BitVec 128) g₁, env.step a₁ g v₁ g₁ →
        env.ok a₂ g₁ ∧ ∀ (v₂ : BitVec 128) g₂, env.step a₂ g₁ v₂ g₂ →
          fin (v₁.setWidth w.bits) (v₂.setWidth w.bits) g₂

/-- `CaspEnv` is monotone in its continuation. -/
theorem Kraken.SharedEnv.CaspEnv.mono {env : SharedEnv} {k : RmwKind} {addr : BitVec 64} {w : MemWidth}
    {cmp1 cmp2 new1 new2 : w.type} {g : env.State} {K₁ K₂ : w.type → w.type → env.State → Prop}
    (hK : ∀ o₁ o₂ g', K₁ o₁ o₂ g' → K₂ o₁ o₂ g') (h : env.CaspEnv k addr w cmp1 cmp2 new1 new2 g K₁) :
    env.CaspEnv k addr w cmp1 cmp2 new1 new2 g K₂ := by
  intro succ rev
  have h := h succ rev
  cases rev <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h ⊢ <;>
    exact ⟨h.1, fun v g₁ hs => ⟨(h.2 v g₁ hs).1, fun v' g₂ hs' hc => hK _ _ _ ((h.2 v g₁ hs).2 v' g₂ hs' hc)⟩⟩

/-- The two halves of a pair start at different addresses. -/
theorem MemWidth.add_bytesv_ne (addr : BitVec 64) (w : MemWidth) : addr + w.bytesv ≠ addr := by
  cases w <;> simp [MemWidth.bytesv] <;> bv_omega

/-- The `lastWrite` state after a `CASP` on the halves at `addr` and
`addr + w.bytes`: both new values written if both halves match their
comparands, otherwise unchanged. A definition over `(lastWrite L).State`
rather than an `if` over functions in place: `vcgen` does not apply a spec
whose environment-state argument needs `(lastWrite L).State` unfolded to type
check (`casp_lastWrite_spec`). -/
def Kraken.SharedEnv.caspLW {L : Layout} (g : (lastWrite L).State) (addr : BitVec 64) (w : MemWidth)
    (cmp1 cmp2 new1 new2 : w.type) : (lastWrite L).State :=
  if ((g addr).setWidth w.bits == cmp1 && (g (addr + w.bytesv)).setWidth w.bits == cmp2) = true
  then upd (upd g addr (new1.setWidth 128)) (addr + w.bytesv) (new2.setWidth 128) else g

/-- `caspLW` read at one address: the `if` over values rather than over
states, which `simp` can decide from hypotheses (an `if` over
`(lastWrite L).State` in place is not rewritten under its applications). -/
theorem Kraken.SharedEnv.caspLW_apply {L : Layout} (g : (lastWrite L).State) (addr : BitVec 64)
    (w : MemWidth) (cmp1 cmp2 new1 new2 : w.type) (k : BitVec 64) :
    caspLW g addr w cmp1 cmp2 new1 new2 k =
      if ((g addr).setWidth w.bits == cmp1 && (g (addr + w.bytesv)).setWidth w.bits == cmp2) = true
      then upd (upd g addr (new1.setWidth 128)) (addr + w.bytesv) (new2.setWidth 128) k else g k := by
  unfold caspLW
  exact apply_ite (fun f : (lastWrite L).State => f k) _ _ _

/-- **`CASP` in `lastWrite`**: both halves must be locations of `L`; the
continuation receives both halves' values and, on a match of both, the state
with both new values written (otherwise the state unchanged). The order of
the halves does not matter here (they are different locations). -/
theorem Kraken.SharedEnv.lastWrite_caspEnv_iff {L : Layout} {k : RmwKind} {addr : BitVec 64}
    {w : MemWidth} {cmp1 cmp2 new1 new2 : w.type} {g : (lastWrite L).State}
    {K : w.type → w.type → (lastWrite L).State → Prop} :
    (lastWrite L).CaspEnv k addr w cmp1 cmp2 new1 new2 g K ↔
      (addr, w.bytes) ∈ L ∧ (addr + w.bytesv, w.bytes) ∈ L ∧
        K ((g addr).setWidth w.bits) ((g (addr + w.bytesv)).setWidth w.bits)
          (caspLW g addr w cmp1 cmp2 new1 new2) := by
  unfold caspLW
  have hne := MemWidth.add_bytesv_ne addr w
  have hcomm : upd (upd g (addr + w.bytesv) (new2.setWidth 128)) addr (new1.setWidth 128) =
      upd (upd g addr (new1.setWidth 128)) (addr + w.bytesv) (new2.setWidth 128) := by
    funext x
    simp only [upd]
    by_cases h1 : x = addr <;> by_cases h2 : x = addr + w.bytesv <;> simp_all
  constructor
  · intro h
    have h' := h ((g addr).setWidth w.bits == cmp1 && (g (addr + w.bytesv)).setWidth w.bits == cmp2) false
    simp only [lastWrite, Bool.false_eq_true, ite_false, rmwOpBits] at h'
    obtain ⟨hok₁, h'⟩ := h'
    refine ⟨hok₁, ?_⟩
    by_cases h1 : (g addr).setWidth w.bits = cmp1 <;> by_cases h2 : (g (addr + w.bytesv)).setWidth w.bits = cmp2 <;>
      simp [h1, h2, hne, -MemWidth.bits, -MemWidth.bytes] at h' ⊢ <;>
      first | exact h' | simpa [h1, h2, -MemWidth.bits, -MemWidth.bytes] using h' _ _ rfl rfl
  · rintro ⟨hok₁, hok₂, hK⟩ succ rev
    cases rev <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · refine ⟨hok₁, ?_⟩
      rintro v₁ g₁ ⟨rfl, rfl⟩
      refine ⟨hok₂, ?_⟩
      rintro v₂ g₂ ⟨rfl, rfl⟩ hc
      by_cases h1 : (g addr).setWidth w.bits = cmp1 <;>
        by_cases h2 : (g (addr + w.bytesv)).setWidth w.bits = cmp2 <;> cases succ <;>
        simp_all [rmwOpBits, -MemWidth.bits, -MemWidth.bytes]
    · refine ⟨hok₂, ?_⟩
      rintro v₂ g₁ ⟨rfl, rfl⟩
      refine ⟨hok₁, ?_⟩
      rintro v₁ g₂ ⟨rfl, rfl⟩ hc
      by_cases h1 : (g addr).setWidth w.bits = cmp1 <;>
        by_cases h2 : (g (addr + w.bytesv)).setWidth w.bits = cmp2 <;> cases succ <;>
        simp_all [rmwOpBits, -MemWidth.bits, -MemWidth.bytes]

/-- `Effects.All`, with every access outside `dmem` answered by `env`: the
access must be permitted (`env.ok`) and the run continues from every outcome
`env.step` allows, in the environment state it leaves. `post` sees the final
machine state and environment state. `unimplemented` and `unaligned_sp` stay
`False`; the access checks pass through, as in `All` (the access discipline
is `env.ok`'s, at the access itself). A thread's `dmem` passes through the
environment unchanged.

A store's success `Bool` is the environment's answer: `sync_store` hands it to
the tree (a store-exclusive's status register), `nonmem_store` ignores it.
An `rmw`'s `noRet` flag (herd's `NoRet`: the destination is the zero
register, so the read is not an acquire and `DMB LD` does not order it) is
not passed on: `SharedAccess.rmw` has no field for it, and the kind `k` is
passed as the instruction states it. This restricts no program. The
obligation falls on the environment: one that cannot see the flag must be
sound for the weaker `NoRet` semantics, i.e. its `step` for an `rmw` of kind
`k` must allow every outcome the hardware allows when the read is `NoRet`
(no acquire, not ordered by `DMB LD`). Such an environment gives weaker
conclusions, never stronger ones. `lastWrite` has no views and meets this
trivially. A view-tracking environment (Stage 2) will need the flag
(`EnvWP.md` §7, open item). -/
def Effects.AllEnv (env : SharedEnv) (g : env.State) (post : MachineState → env.State → Prop) :
    Effects → Prop
  | .done a => post a g
  | .unimplemented _ => False
  | .unaligned_sp .. => False
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
  | .rmw k _ dmem addr w op ret =>
    env.ok (.rmw k addr w.bytes (rmwOpBits w.bits op)) g ∧
      ∀ old g', env.step (.rmw k addr w.bytes (rmwOpBits w.bits op)) g old g' →
        (ret (old.setWidth w.bits) dmem).AllEnv env g' post
  | .fence k ok =>
    env.ok (.fence k) g ∧ ∀ g', env.step (.fence k) g () g' → (ok ()).AllEnv env g' post
  -- A `CASP` both of whose halves are outside `dmem`: two `rmw`s, one per half,
  -- in either order, as the Promising machine performs it (`CaspEnv`).
  | @Effects.rmw_pair k dmem addr w cmp1 cmp2 new1 new2 ret =>
    env.CaspEnv k addr w cmp1 cmp2 new1 new2 g fun o₁ o₂ g' => (ret o₁ o₂ dmem).AllEnv env g' post
  -- `LDXP`/`STXP` (and the FEAT_LSE2 16-byte `LDP`/`STP` of `isaLSE2`, the only
  -- source of a non-exclusive pair) with both halves outside `dmem` are not
  -- supported by the environment logic: `False`, as in `All`. LL/SC is deferred
  -- in the Stage 2/3 logic, and `Executable.step` never
  -- produces a non-exclusive pair (`EnvWP.md`, "Pair effects"); the FEAT_LSE2
  -- pairs are covered by `Effects.AllEnvLSE2` (`Kraken/AArch64/EnvLSE2.lean`).
  -- (A pair with one half in `dmem` is a single access on the other half, above.)
  | .sync_load_pair .. => False
  | .sync_store_pair .. => False

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
  | _ => exact fun h => h.elim

/-- `AllEnv` is monotone in the postcondition. -/
theorem Effects.AllEnv.mono {env : SharedEnv} {post₁ post₂ : MachineState → env.State → Prop}
    (hp : ∀ s g, post₁ s g → post₂ s g) (e : Effects) :
    ∀ g, e.AllEnv env g post₁ → e.AllEnv env g post₂ := by
  induction e with
  | done a => exact fun g h => hp _ _ h
  | unimplemented => exact fun _ h => h
  | unaligned_sp => exact fun _ h => h
  | nonmem_load dmem addr w ret ih => exact fun g h => ⟨h.1, fun v g' hs => ih _ _ g' (h.2 v g' hs)⟩
  | nonmem_store dmem addr v ret ih => exact fun g h => ⟨h.1, fun b g' hs => ih _ g' (h.2 b g' hs)⟩
  | undefined ret ih => exact fun g h v => ih v g (h v)
  | require_read_access _ _ ok ih => exact fun g h => ih () g h
  | require_write_access _ _ ok ih => exact fun g h => ih () g h
  | require_exec_access _ ok ih => exact fun g h => ih () g h
  | sync_load k xcl dmem addr w ret ih => exact fun g h => ⟨h.1, fun v g' hs => ih _ _ g' (h.2 v g' hs)⟩
  | sync_store k xcl dmem addr v ret ih => exact fun g h => ⟨h.1, fun b g' hs => ih _ _ g' (h.2 b g' hs)⟩
  | rmw k nr dmem addr w op ret ih => exact fun g h => ⟨h.1, fun v g' hs => ih _ _ g' (h.2 v g' hs)⟩
  | fence k ok ih => exact fun g h => ⟨h.1, fun g' hs => ih () g' (h.2 g' hs)⟩
  | sync_load_pair => exact fun _ h => h
  | sync_store_pair => exact fun _ h => h
  | rmw_pair k dmem addr cmp1 cmp2 new1 new2 ret ih =>
    exact fun g h => SharedEnv.CaspEnv.mono (fun o₁ o₂ g' => ih o₁ o₂ dmem g') h

/-- With no shared locations, `AllEnv` is `All`. -/
theorem Effects.allEnv_none_iff {post : MachineState → Prop} (e : Effects) :
    e.AllEnv SharedEnv.none () (fun s _ => post s) ↔ e.All post := by
  induction e with
  | done a => exact Iff.rfl
  | unimplemented => exact Iff.rfl
  | unaligned_sp => exact Iff.rfl
  | fence k ok ih =>
    exact ⟨fun h => (ih ()).mp (h.2 () trivial), fun h => ⟨trivial, fun _ _ => (ih ()).mpr h⟩⟩
  | undefined ret ih => exact forall_congr' ih
  | require_read_access _ _ ok ih => exact ih ()
  | require_write_access _ _ ok ih => exact ih ()
  | require_exec_access _ ok ih => exact ih ()
  | sync_load_pair => exact Iff.rfl
  | sync_store_pair => exact Iff.rfl
  | rmw_pair => exact ⟨fun h => (h false false).1.elim, fun h => h.elim⟩
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
