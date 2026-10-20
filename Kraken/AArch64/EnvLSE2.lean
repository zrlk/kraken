/-
FEAT_LSE2 in the environment logic, AArch64 (design note
`Kraken/Promising/EnvWP.md`, "Pair effects").

`Kraken.Promising.AArch64.isaLSE2` performs a 16-byte-aligned `LDP`/`STP` of
two `X` registers as one plain pair access (`Directive.interpLSE2`,
`Kraken/AArch64/LSE2.lean`), which the adapter makes one 16-byte access when
the address is a declared 16-byte location. This file is the matching
judgment:

- `Effects.AllEnvLSE2 D env`: `Effects.AllEnv` with the non-exclusive pair
  effects answered by the environment, relative to a list `D` of the
  locations the machine declares: a pair whose address is a 16-byte location
  of `D` is **one** 16-byte access (the value's low half is the first
  register's, as in `toEv`), any other pair the two accesses of `LDP`/`STP`,
  lower address first. Exclusive pairs (`LDXP`/`STXP`) stay `False`, as in
  `AllEnv`.
- `Executable.stepAtEnvLSE2`, `instrStepEnvLSE2`, `wpEnvLSE2`,
  `MachineWP.TripleEnvLSE2`: `stepAtEnv` and the rest, with each cell read by
  `Directive.interpLSE2`.
- **The embedding** (`instrStepEnvLSE2_of_instrStepEnv`,
  `wpEnvLSE2_of_wpEnv`): every `instrStepEnv` step is an `instrStepEnvLSE2`
  step, in an environment that refuses an 8-byte plain access at the low half
  of a 16-byte location of `D` and never fails a non-exclusive store
  (`SharedEnv.LSE2Disc`; `lastWrite L` with `D = L` whenever no location of
  `L` is the low half of another, `lastWrite_lse2Disc`). So every
  `EnvProgram` rule and `vcgen` spec serves the LSE2 judgment unchanged
  (`MachineWP.env_lse2_lift_spec`).
- The rules `ldp_lse2_shared`/`stp_lse2_shared` and their `vcgen` specs:
  an aligned `LDP`/`STP` of two `X` registers both of whose halves are outside
  `dmem`, at a 16-byte location of `D`: one 16-byte plain access. These are
  the only ordering variants: Kraken has no `LDIAPP`/`STILP`, and the
  acquire/release pairs are the exclusive ones.

The link to `isaLSE2` is `Kraken.Promising.EnvLSE2AArch64`.
-/
import Kraken.AArch64.EnvVCGen
import Kraken.AArch64.LSE2

open Kraken
open Std.WP
open Lean.Order

/-! ## `AllEnvLSE2` -/

/-- `Effects.AllEnv` under FEAT_LSE2, relative to the declared locations `D`.
The cases other than the non-exclusive pairs are `AllEnv`'s. A non-exclusive
load or store pair with both halves outside `dmem` is one access of
`2 * w.bytes` bytes when `(addr, 2 * w.bytes)` is a location of `D`, and
otherwise the two `w`-sized accesses of the pair, lower address first, as the
adapter performs it (`Kraken.Promising.AArch64.toEv`, `pairIsOneLoc`). The
16-byte value of a pair is `v₂ : v₁` (the first register's half low). An
exclusive pair (`LDXP`/`STXP`) is `False`, as in `AllEnv`. -/
def Effects.AllEnvLSE2 (D : SharedEnv.Layout) (env : SharedEnv) (g : env.State)
    (post : MachineState → env.State → Prop) : Effects → Prop
  | .done a => post a g
  | .unimplemented _ => False
  | .unaligned_sp .. => False
  | .nonmem_load dmem addr w ret =>
    env.ok (.load .plain false addr w.bytes) g ∧
      ∀ v g', env.step (.load .plain false addr w.bytes) g v g' →
        (ret (v.setWidth w.bits) dmem).AllEnvLSE2 D env g' post
  | .nonmem_store dmem addr (w := w) v ret =>
    env.ok (.store .plain false addr w.bytes (v.setWidth 128)) g ∧
      ∀ b g', env.step (.store .plain false addr w.bytes (v.setWidth 128)) g b g' →
        (ret dmem).AllEnvLSE2 D env g' post
  | @Effects.undefined α _ ret => ∀ v : α, (ret v).AllEnvLSE2 D env g post
  | .require_read_access _ _ ok => (ok ()).AllEnvLSE2 D env g post
  | .require_write_access _ _ ok => (ok ()).AllEnvLSE2 D env g post
  | .require_exec_access _ ok => (ok ()).AllEnvLSE2 D env g post
  | .sync_load k xcl dmem addr w ret =>
    env.ok (.load k xcl addr w.bytes) g ∧
      ∀ v g', env.step (.load k xcl addr w.bytes) g v g' →
        (ret (v.setWidth w.bits) dmem).AllEnvLSE2 D env g' post
  | .sync_store k xcl dmem addr (w := w) v ret =>
    env.ok (.store k xcl addr w.bytes (v.setWidth 128)) g ∧
      ∀ b g', env.step (.store k xcl addr w.bytes (v.setWidth 128)) g b g' →
        (ret b dmem).AllEnvLSE2 D env g' post
  | .rmw k _ dmem addr w op ret =>
    env.ok (.rmw k addr w.bytes (rmwOpBits w.bits op)) g ∧
      ∀ old g', env.step (.rmw k addr w.bytes (rmwOpBits w.bits op)) g old g' →
        (ret (old.setWidth w.bits) dmem).AllEnvLSE2 D env g' post
  | .fence k ok =>
    env.ok (.fence k) g ∧ ∀ g', env.step (.fence k) g () g' → (ok ()).AllEnvLSE2 D env g' post
  | @Effects.rmw_pair k dmem addr w cmp1 cmp2 new1 new2 ret =>
    env.CaspEnv k addr w cmp1 cmp2 new1 new2 g fun o₁ o₂ g' => (ret o₁ o₂ dmem).AllEnvLSE2 D env g' post
  | .sync_load_pair k xcl dmem addr w ret =>
    xcl = false ∧
    ((addr, 2 * w.bytes) ∈ D →
      env.ok (.load k false addr (2 * w.bytes)) g ∧
        ∀ v g', env.step (.load k false addr (2 * w.bytes)) g v g' →
          (ret (v.setWidth w.bits) ((v >>> w.bits).setWidth w.bits) dmem).AllEnvLSE2 D env g' post) ∧
    ((addr, 2 * w.bytes) ∉ D →
      env.ok (.load k false addr w.bytes) g ∧
        ∀ v₁ g₁, env.step (.load k false addr w.bytes) g v₁ g₁ →
          env.ok (.load k false (addr + w.bytesv) w.bytes) g₁ ∧
            ∀ v₂ g₂, env.step (.load k false (addr + w.bytesv) w.bytes) g₁ v₂ g₂ →
              (ret (v₁.setWidth w.bits) (v₂.setWidth w.bits) dmem).AllEnvLSE2 D env g₂ post)
  | @Effects.sync_store_pair k xcl dmem addr w v1 v2 ret =>
    xcl = false ∧
    ((addr, 2 * w.bytes) ∈ D →
      env.ok (.store k false addr (2 * w.bytes) ((v2.setWidth 128 <<< w.bits) ||| v1.setWidth 128)) g ∧
        ∀ b g', env.step (.store k false addr (2 * w.bytes)
            ((v2.setWidth 128 <<< w.bits) ||| v1.setWidth 128)) g b g' →
          (ret b dmem).AllEnvLSE2 D env g' post) ∧
    ((addr, 2 * w.bytes) ∉ D →
      env.ok (.store k false addr w.bytes (v1.setWidth 128)) g ∧
        ∀ b₁ g₁, env.step (.store k false addr w.bytes (v1.setWidth 128)) g b₁ g₁ →
          env.ok (.store k false (addr + w.bytesv) w.bytes (v2.setWidth 128)) g₁ ∧
            ∀ b₂ g₂, env.step (.store k false (addr + w.bytesv) w.bytes (v2.setWidth 128)) g₁ b₂ g₂ →
              (ret true dmem).AllEnvLSE2 D env g₂ post)

/-- `AllEnvLSE2` is monotone in the postcondition. -/
theorem Effects.AllEnvLSE2.mono {D : SharedEnv.Layout} {env : SharedEnv}
    {post₁ post₂ : MachineState → env.State → Prop}
    (hp : ∀ s g, post₁ s g → post₂ s g) (e : Effects) :
    ∀ g, e.AllEnvLSE2 D env g post₁ → e.AllEnvLSE2 D env g post₂ := by
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
  | sync_load_pair k xcl dmem addr w ret ih =>
    exact fun g ⟨hx, h1, h2⟩ =>
      ⟨hx, fun hm => ⟨(h1 hm).1, fun v g' hs => ih _ _ _ g' ((h1 hm).2 v g' hs)⟩,
        fun hm => ⟨(h2 hm).1, fun v₁ g₁ hs₁ => ⟨((h2 hm).2 v₁ g₁ hs₁).1,
          fun v₂ g₂ hs₂ => ih _ _ _ g₂ (((h2 hm).2 v₁ g₁ hs₁).2 v₂ g₂ hs₂)⟩⟩⟩
  | sync_store_pair k xcl dmem addr v1 v2 ret ih =>
    exact fun g ⟨hx, h1, h2⟩ =>
      ⟨hx, fun hm => ⟨(h1 hm).1, fun b g' hs => ih _ _ g' ((h1 hm).2 b g' hs)⟩,
        fun hm => ⟨(h2 hm).1, fun b₁ g₁ hs₁ => ⟨((h2 hm).2 b₁ g₁ hs₁).1,
          fun b₂ g₂ hs₂ => ih _ _ g₂ (((h2 hm).2 b₁ g₁ hs₁).2 b₂ g₂ hs₂)⟩⟩⟩
  | rmw_pair k dmem addr cmp1 cmp2 new1 new2 ret ih =>
    exact fun g h => SharedEnv.CaspEnv.mono (fun o₁ o₂ g' => ih o₁ o₂ dmem g') h

/-- An `AllEnv` judgment is an `AllEnvLSE2` judgment, for any `D`: the two
differ only at the non-exclusive pairs, which are `False` in `AllEnv`. -/
theorem Effects.allEnvLSE2_of_allEnv {D : SharedEnv.Layout} {env : SharedEnv}
    {post : MachineState → env.State → Prop} (e : Effects) :
    ∀ g, e.AllEnv env g post → e.AllEnvLSE2 D env g post := by
  induction e with
  | done a => exact fun g h => h
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
  | sync_load_pair => exact fun _ h => h.elim
  | sync_store_pair => exact fun _ h => h.elim
  | rmw_pair k dmem addr cmp1 cmp2 new1 new2 ret ih =>
    exact fun g h => SharedEnv.CaspEnv.mono (fun o₁ o₂ g' => ih o₁ o₂ dmem g') h

/-! ## The environment side condition of the embedding -/

/-- The side condition under which every `AllEnv` step is an `AllEnvLSE2`
step relative to `D`: an 8-byte plain access at the address of a 16-byte
location of `D` (the low half of a pair the machine performs as one access)
is refused, and a non-exclusive store never reports failure. The first is
the access discipline (no mixed-size access to a 16-byte location); the
second holds of every environment in this development (a plain store always
succeeds). -/
class Kraken.SharedEnv.LSE2Disc (D : SharedEnv.Layout) (env : SharedEnv) : Prop where
  refuse_load : ∀ a g, (a, 16) ∈ D → ¬ env.ok (.load .plain false a 8) g
  refuse_store : ∀ a v g, (a, 16) ∈ D → ¬ env.ok (.store .plain false a 8 v) g
  store_ok : ∀ a n v g g', ¬ env.step (.store .plain false a n v) g false g'

/-- **`lastWrite L` meets the side condition for `D = L`** when no location
of `L` is the low half of a 16-byte location of `L` (which `SharedLayout.WF`
gives, `Kraken.Promising.AArch64.lastWrite_lse2Disc_of_wf`). -/
theorem Kraken.SharedEnv.lastWrite_lse2Disc {L : Layout} (h : ∀ a, (a, 16) ∈ L → (a, 8) ∉ L) :
    (lastWrite L).LSE2Disc L where
  refuse_load a _ ha hok := h a ha hok
  refuse_store a _ _ ha hok := h a ha hok
  store_ok _ _ _ _ _ hs := by
    rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩
    · cases h1
    · cases h1

/-! ## The step relation, the wp and triples -/

/-- `Executable.stepAtEnv` under FEAT_LSE2: the cell read by
`Directive.interpLSE2`, its accesses answered by `AllEnvLSE2` relative to
`D`. -/
def Kraken.Executable.stepAtEnvLSE2 (e : Kraken.Executable Directive) (D : SharedEnv.Layout)
    (env : SharedEnv) (d : Directive) (z : Nat) (st : MachineState × env.State)
    (post : MachineState × env.State → Prop) : Prop :=
  (@Directive.interpLSE2 (_root_.Executable.labels e) d st.1.1 (.mk st.1.2 (st.1.2 + .ofNat z))
      (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).AllEnvLSE2 D env st.2
    (fun m g => post ((m.1, st.1.2 + .ofNat z), g))
  ∨ (@Directive.interpLSE2 (_root_.Executable.labels e) d st.1.1 (.mk st.1.2 (st.1.2 + .ofNat z))
      (fun _ => .unimplemented "fallthrough") (fun pc' s' => .done (s', pc'))).AllEnvLSE2 D env st.2
    (fun m g => post (m, g))

/-- `Executable.instrStepEnv` under FEAT_LSE2. -/
def Kraken.Executable.instrStepEnvLSE2 (e : Kraken.Executable Directive) (D : SharedEnv.Layout)
    (env : SharedEnv) (st : MachineState × env.State) (post : MachineState × env.State → Prop) : Prop :=
  ∃ d z rest, e.codeAt st.1.2 = (d, z) :: rest ∧ e.stepAtEnvLSE2 D env d z st post

/-- `Executable.wpEnv` under FEAT_LSE2. -/
def Kraken.Executable.wpEnvLSE2 (e : Kraken.Executable Directive) (D : SharedEnv.Layout)
    (env : SharedEnv) (q : Program) (Q : MachineData → env.State → Prop)
    (E : Int64 → MachineData → env.State → Prop) (s : MachineData) (g : env.State) : Prop :=
  ∀ (pc : Int64), e.sits pc q →
    Eventually (e.instrStepEnvLSE2 D env)
      (fun x => (x.1.2 = e.after pc q ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2) ((s, pc), g)

theorem Kraken.Executable.wpEnvLSE2_mono {e : Kraken.Executable Directive} {D : SharedEnv.Layout}
    {env : SharedEnv} {q : Program}
    {Q₁ Q₂ : MachineData → env.State → Prop} {E₁ E₂ : Int64 → MachineData → env.State → Prop}
    (hQ : ∀ s g, Q₁ s g → Q₂ s g) (hE : ∀ a s g, E₁ a s g → E₂ a s g)
    {s : MachineData} {g : env.State} (h : e.wpEnvLSE2 D env q Q₁ E₁ s g) :
    e.wpEnvLSE2 D env q Q₂ E₂ s g :=
  fun pc hpl => eventually_weaken _ _ _ _
    (fun _ hst => hst.imp (fun ⟨ha, hq⟩ => ⟨ha, hQ _ _ hq⟩) (hE _ _ _)) (h pc hpl)

/-- `wpEnv_cons` under FEAT_LSE2. -/
theorem Kraken.Executable.wpEnvLSE2_cons {e : Kraken.Executable Directive} {D : SharedEnv.Layout}
    {env : SharedEnv} {d : Directive} {q : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} {s : MachineData} {g : env.State}
    (h : e.wpEnvLSE2 D env [d] (fun s' g' => e.wpEnvLSE2 D env q Q E s' g') E s g) :
    e.wpEnvLSE2 D env (d :: q) Q E s g := by
  intro pc hpl
  have hcont : ∀ pc', e.sits pc' q → ∀ x : MachineState × env.State,
      (x.1.2 = pc' ∧ e.wpEnvLSE2 D env q Q E x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2 →
      Eventually (e.instrStepEnvLSE2 D env)
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

namespace MachineWP

/-- A triple with the environment under FEAT_LSE2. -/
def TripleEnvLSE2 [CodeEnv] (D : SharedEnv.Layout) (env : SharedEnv) (P : MachineData → env.State → Prop)
    (q : Program) (Q : MachineData → env.State → Prop) (E : Int64 → MachineData → env.State → Prop) : Prop :=
  ∀ s g, P s g → cenv.wpEnvLSE2 D env q Q E s g

end MachineWP

/-! ## The embedding

Every cell's `AllEnv` step is its `AllEnvLSE2` step, with the same
continuations. A cell without an LSE2 reading has the same tree under both
(`Directive.interpLSE2_of_none`); an aligned `LDP`/`STP` of two `X` registers
is two accesses in the base tree and one pair access in the LSE2 tree, and
the four cases of which halves are in `dmem` agree: both in `dmem`, no access;
one in `dmem`, the same single access on the other half (for a store, given
that it succeeds, `LSE2Disc.store_ok`); neither, the two accesses of the base
tree, which `AllEnvLSE2` asks for when the address is not a 16-byte location
of `D` and which the environment refuses when it is (`LSE2Disc`). -/

section Embed

variable {D : SharedEnv.Layout} {env : SharedEnv} {g : env.State} {P : MachineState → env.State → Prop}

private theorem checkSP_embed {a : AddrExpr} {s : MachineData} {ok₁ ok₂ : Unit → Effects}
    (hk : (ok₁ ()).AllEnv env g P → (ok₂ ()).AllEnvLSE2 D env g P)
    (h : (a.checkSPAlignment s ok₁).AllEnv env g P) : (a.checkSPAlignment s ok₂).AllEnvLSE2 D env g P := by
  unfold AddrExpr.checkSPAlignment at h ⊢
  generalize a.base = b at h ⊢
  cases b with
  | low x w' =>
    cases x with
    | reg x => exact hk h
    | SP =>
      simp only at h ⊢
      split at h
      · exact h.elim
      · rename_i hc
        rw [ite_eq_right hc]
        exact hk h

/-- A cell other than a 64-bit `LDP`/`STP` or a `CASP` of `X` registers has no
FEAT_LSE2 reading. -/
private theorem Directive.not_lse2Free {d : Directive} (h : ¬ d.LSE2Free) :
    (∃ d₁ d₂ a, d = .instr ⟨.W64, .LDP d₁ d₂ a⟩) ∨ (∃ s₁ s₂ a, d = .instr ⟨.W64, .STP s₁ s₂ a⟩) ∨
      (∃ k r₁ r₂ r₃ r₄ a, d = .instr ⟨.W64, .CASP k r₁ r₂ r₃ r₄ a⟩) := by
  unfold Directive.LSE2Free at h
  split at h
  · exact .inl ⟨_, _, _, rfl⟩
  · exact .inr (.inl ⟨_, _, _, rfl⟩)
  · exact .inr (.inr ⟨_, _, _, _, _, _, rfl⟩)
  · exact (h trivial).elim

/-- A store to the low half of a pair leaves the high half's mapping as it
was. -/
theorem loadInt_store_hi (dm : DataMem) (addr : BitVec 64) (v : Int) :
    (Mem.storeInt dm addr MemWidth.W64.bytes v).loadInt (addr + RegWidth.W64.bytesv) MemWidth.W64.bytes =
      dm.loadInt (addr + 8#64) 8 := by
  have h : addr + 8#64 - addr = 8#64 := by rw [BitVec.add_comm, BitVec.add_sub_cancel]
  exact Mem.loadInt_storeInt_of_above _ _ _ _ _ _ (by rw [h]; exact Nat.le_refl _) (by rw [h]; decide)

theorem Directive.ldp_lse2_embed [Labels] [hD : SharedEnv.LSE2Disc D env] (d₁ d₂ : RegOrZr .W64)
    (a : AddrExpr) (s : MachineData) (p : Std.Rco Int64) (k : MachineData → Effects)
    (j : Int64 → MachineData → Effects)
    (h : ((Directive.instr ⟨.W64, .LDP d₁ d₂ a⟩).interp s p k j).AllEnv env g P) :
    ((Directive.instr ⟨.W64, .LDP d₁ d₂ a⟩).interpLSE2 s p k j).AllEnvLSE2 D env g P := by
  have h0 := h
  unfold Directive.interpLSE2 Directive.interpLSE2?
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.AllEnv] at h
  generalize hev : a.eval s p = ev at h
  obtain ⟨addr, ⟨r, f, dm⟩⟩ := ev
  simp only [hev] at h ⊢
  by_cases hal : (addr % 16 != 0) = true
  · simp only [hal, ite_true, Option.getD_none]
    exact Effects.allEnvLSE2_of_allEnv _ _ h0
  · simp only [hal, Bool.false_eq_true, ite_false, Option.getD_some]
    refine checkSP_embed (fun h => ?_) h
    simp only [MachineData.load, MachineData.loadPairK, Effects.AllEnv, Effects.AllEnvLSE2] at h ⊢
    cases hd₁ : Mem.loadInt dm addr 8 <;> cases hd₂ : Mem.loadInt dm (addr + 8#64) 8 <;>
      simp only [hd₁, hd₂, Effects.AllEnv, Effects.AllEnvLSE2, MachineData.setRegOrZr] at h ⊢
    · exact ⟨trivial, fun hm => (hD.refuse_load addr g hm h.1).elim, fun _ => ⟨h.1, fun v₁ g₁ hs₁ =>
        ⟨(h.2 v₁ g₁ hs₁).1, fun v₂ g₂ hs₂ => Effects.allEnvLSE2_of_allEnv _ _ ((h.2 v₁ g₁ hs₁).2 v₂ g₂ hs₂)⟩⟩⟩
    · exact ⟨h.1, fun v g' hs => Effects.allEnvLSE2_of_allEnv _ _ (h.2 v g' hs)⟩
    · exact ⟨h.1, fun v g' hs => Effects.allEnvLSE2_of_allEnv _ _ (h.2 v g' hs)⟩
    · exact Effects.allEnvLSE2_of_allEnv _ _ h

theorem Directive.stp_lse2_embed [Labels] [hD : SharedEnv.LSE2Disc D env] (s₁ s₂ : RegOrZr .W64)
    (a : AddrExpr) (s : MachineData) (p : Std.Rco Int64) (k : MachineData → Effects)
    (j : Int64 → MachineData → Effects)
    (h : ((Directive.instr ⟨.W64, .STP s₁ s₂ a⟩).interp s p k j).AllEnv env g P) :
    ((Directive.instr ⟨.W64, .STP s₁ s₂ a⟩).interpLSE2 s p k j).AllEnvLSE2 D env g P := by
  have h0 := h
  unfold Directive.interpLSE2 Directive.interpLSE2?
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.AllEnv] at h
  generalize hev : a.eval s p = ev at h
  obtain ⟨addr, ⟨r, f, dm⟩⟩ := ev
  simp only [hev] at h ⊢
  by_cases hal : (addr % 16 != 0) = true
  · simp only [hal, ite_true, Option.getD_none]
    exact Effects.allEnvLSE2_of_allEnv _ _ h0
  · simp only [hal, Bool.false_eq_true, ite_false, Option.getD_some]
    refine checkSP_embed (fun h => ?_) h
    simp only [MachineData.store, MachineData.storePairK, Effects.AllEnv, Effects.AllEnvLSE2] at h ⊢
    cases hd₁ : Mem.loadInt dm addr 8 <;> cases hd₂ : Mem.loadInt dm (addr + 8#64) 8 <;>
      simp only [hd₁, hd₂, Effects.AllEnv, Effects.AllEnvLSE2] at h ⊢
    · exact ⟨trivial, fun hm => (hD.refuse_store addr _ g hm h.1).elim, fun _ => ⟨h.1, fun b₁ g₁ hs₁ =>
        ⟨(h.2 b₁ g₁ hs₁).1, fun b₂ g₂ hs₂ => Effects.allEnvLSE2_of_allEnv _ _ ((h.2 b₁ g₁ hs₁).2 b₂ g₂ hs₂)⟩⟩⟩
    · refine ⟨h.1, fun b g' hs => ?_⟩
      cases b
      · exact (hD.store_ok _ _ _ _ _ hs).elim
      · exact Effects.allEnvLSE2_of_allEnv _ _ (h.2 true g' hs)
    · rw [loadInt_store_hi, hd₂] at h
      simp only [Effects.AllEnv] at h
      refine ⟨h.1, fun b g' hs => ?_⟩
      cases b
      · exact (hD.store_ok _ _ _ _ _ hs).elim
      · exact Effects.allEnvLSE2_of_allEnv _ _ (h.2 true g' hs)
    · rw [loadInt_store_hi, hd₂] at h
      simp only at h
      exact Effects.allEnvLSE2_of_allEnv _ _ h

/-- **The embedding, one cell.** -/
theorem Directive.allEnvLSE2_interpLSE2 [Labels] [SharedEnv.LSE2Disc D env] (d : Directive)
    (s : MachineData) (p : Std.Rco Int64) (k : MachineData → Effects) (j : Int64 → MachineData → Effects)
    (h : (d.interp s p k j).AllEnv env g P) : (d.interpLSE2 s p k j).AllEnvLSE2 D env g P := by
  by_cases hf : d.LSE2Free
  · rw [Directive.interpLSE2_of_none j (Directive.interpLSE2?_none_of_free hf s p k)]
    exact Effects.allEnvLSE2_of_allEnv _ _ h
  · rcases Directive.not_lse2Free hf with ⟨d₁, d₂, a, rfl⟩ | ⟨s₁, s₂, a, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩
    · exact Directive.ldp_lse2_embed d₁ d₂ a s p k j h
    · exact Directive.stp_lse2_embed s₁ s₂ a s p k j h
    · rw [Directive.interpLSE2_of_none j rfl]
      exact Effects.allEnvLSE2_of_allEnv _ _ h

end Embed

/-- **The embedding, one instruction.** -/
theorem Kraken.Executable.instrStepEnvLSE2_of_instrStepEnv {e : Kraken.Executable Directive}
    {D : SharedEnv.Layout} {env : SharedEnv} [SharedEnv.LSE2Disc D env] {st : MachineState × env.State}
    {post : MachineState × env.State → Prop} (h : e.instrStepEnv env st post) :
    e.instrStepEnvLSE2 D env st post := by
  obtain ⟨d, z, rest, hcode, hstep⟩ := h
  refine ⟨d, z, rest, hcode, ?_⟩
  letI := _root_.Executable.labels e
  rcases hstep with h | h
  · exact .inl (Directive.allEnvLSE2_interpLSE2 d _ _ _ _ h)
  · exact .inr (Directive.allEnvLSE2_interpLSE2 d _ _ _ _ h)

/-- **The embedding, runs.** -/
theorem Kraken.Executable.eventually_instrStepEnvLSE2 {e : Kraken.Executable Directive}
    {D : SharedEnv.Layout} {env : SharedEnv} [SharedEnv.LSE2Disc D env]
    {P : MachineState × env.State → Prop} {st : MachineState × env.State}
    (h : Eventually (e.instrStepEnv env) P st) : Eventually (e.instrStepEnvLSE2 D env) P st := by
  induction h with
  | done st hP => exact .done _ hP
  | step st mid hT _ ih => exact .step _ _ (instrStepEnvLSE2_of_instrStepEnv hT) ih

/-- **The embedding, wp.** -/
theorem Kraken.Executable.wpEnvLSE2_of_wpEnv {e : Kraken.Executable Directive}
    {D : SharedEnv.Layout} {env : SharedEnv} [SharedEnv.LSE2Disc D env] {q : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    {s : MachineData} {g : env.State} (h : e.wpEnv env q Q E s g) : e.wpEnvLSE2 D env q Q E s g :=
  fun pc hpl => eventually_instrStepEnvLSE2 (h pc hpl)

namespace MachineWP

/-- **The embedding, triples.** -/
theorem TripleEnvLSE2.of_tripleEnv [CodeEnv] {D : SharedEnv.Layout} {env : SharedEnv}
    [SharedEnv.LSE2Disc D env] {P : MachineData → env.State → Prop} {q : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    (h : TripleEnv env P q Q E) : TripleEnvLSE2 D env P q Q E :=
  fun s g hp => Executable.wpEnvLSE2_of_wpEnv (h s g hp)

end MachineWP

/-! ## The rules: a 16-byte `LDP`/`STP` on a shared location -/

/-- The low half of the 16-byte value of a pair `x : y`. -/
@[simp] theorem lse2_pair_lo (x y : BitVec 64) : ((x.setWidth 128 <<< 64) ||| y.setWidth 128).setWidth 64 = y := by
  ext i hi
  simp

/-- The high half of the 16-byte value of a pair `x : y`. -/
@[simp] theorem lse2_pair_hi (x y : BitVec 64) :
    (((x.setWidth 128 <<< 64) ||| y.setWidth 128) >>> 64).setWidth 64 = x := by
  ext i hi
  simp [show 64 + i < 128 by omega, show i < 128 by omega, BitVec.getLsbD_eq_getElem, hi]

section Rules

variable {D : SharedEnv.Layout} {env : SharedEnv} {g : env.State} {P : MachineState → env.State → Prop}

private theorem AddrExpr.checkSP_AllEnvLSE2 {a : AddrExpr} {s : MachineData} {ok : Unit → Effects}
    (ha : a.SPAligned s) (hk : (ok ()).AllEnvLSE2 D env g P) :
    (a.checkSPAlignment s ok).AllEnvLSE2 D env g P := by
  obtain ⟨⟨b, w⟩, off⟩ := a
  cases b with
  | reg r => exact hk
  | SP =>
    have h := ha rfl
    simp only [AddrExpr.checkSPAlignment, Reg64s.getRegOrSp_SP, h, bne_self_eq_false,
      Bool.false_eq_true, ite_false]
    exact hk

end Rules

namespace MachineWP

/-- Unfold the fall-through address past one instruction cell. -/
private theorem after_instr' [CodeEnv] {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

variable [CodeEnv] (D : SharedEnv.Layout) (env : SharedEnv) {p : Program}
  {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}

/-- `LDP Xt1, Xt2, [Xn|SP …]` under FEAT_LSE2, at a 16-byte-aligned address
that is a 16-byte location of `D`, both halves outside `dmem`: **one** plain
16-byte load; `Xt1` receives the low half and `Xt2` the high half of every
value the environment allows, after the base writeback. -/
theorem ldp_lse2_shared (dst1 dst2 : RegOrZr .W64) (a : AddrExpr) :
    TripleEnvLSE2 D env
      (fun s g => a.SPAligned s ∧ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        e.1 % 16 = 0 ∧ (e.1, 16) ∈ D ∧
          Mem.loadInt e.2.dmem e.1 8 = none ∧ Mem.loadInt e.2.dmem (e.1 + 8) 8 = none ∧
          env.ok (.load .plain false e.1 16) g ∧
          ∀ v g', env.step (.load .plain false e.1 16) g v g' →
            let r := (e.2.regs.setRegOrZr dst1 (v.setWidth 64)).setRegOrZr dst2 ((v >>> 64).setWidth 64)
            cenv.wpEnvLSE2 D env p Q E { e.2 with regs := r } g')
      (Directive.instr ⟨.W64, .LDP dst1 dst2 a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩ pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  rw [after_instr' hseg]
  refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩
  obtain ⟨hal, hmem, hn₁, hn₂, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [Directive.interpLSE2, Directive.interpLSE2?]
  generalize @AddrExpr.eval (_root_.Executable.labels cenv) a s ⟨pc, pc + .ofNat z⟩ = ev at hal hmem hn₁ hn₂ hok hk ⊢
  obtain ⟨addr, s'⟩ := ev
  simp only at hal hmem hn₁ hn₂ hok hk ⊢
  simp only [hal, bne_self_eq_false, Bool.false_eq_true, ite_false, Option.getD_some]
  refine AddrExpr.checkSP_AllEnvLSE2 ha ?_
  simp only [MachineData.loadPairK, Effects.AllEnvLSE2]
  rw [show addr + MemWidth.W64.bytesv = addr + 8 from rfl, hn₁, hn₂]
  exact ⟨rfl, fun _ => ⟨hok, fun v g' hs => hk v g' hs _ hpl'⟩, fun hn => (hn hmem).elim⟩

/-- `STP Xt1, Xt2, [Xn|SP …]` under FEAT_LSE2, at a 16-byte-aligned address
that is a 16-byte location of `D`, both halves outside `dmem`: **one** plain
16-byte store of `Xt2 : Xt1` (`Xt1` the low half). -/
theorem stp_lse2_shared (src1 src2 : RegOrZr .W64) (a : AddrExpr) :
    TripleEnvLSE2 D env
      (fun s g => a.SPAligned s ∧ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let v := ((s.regs.getRegOrZr src2).setWidth 128 <<< 64) ||| (s.regs.getRegOrZr src1).setWidth 128
        e.1 % 16 = 0 ∧ (e.1, 16) ∈ D ∧
          Mem.loadInt e.2.dmem e.1 8 = none ∧ Mem.loadInt e.2.dmem (e.1 + 8) 8 = none ∧
          env.ok (.store .plain false e.1 16 v) g ∧
          ∀ ok g', env.step (.store .plain false e.1 16 v) g ok g' → cenv.wpEnvLSE2 D env p Q E e.2 g')
      (Directive.instr ⟨.W64, .STP src1 src2 a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩ pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  rw [after_instr' hseg]
  refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩
  obtain ⟨hal, hmem, hn₁, hn₂, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [Directive.interpLSE2, Directive.interpLSE2?]
  generalize @AddrExpr.eval (_root_.Executable.labels cenv) a s ⟨pc, pc + .ofNat z⟩ = ev at hal hmem hn₁ hn₂ hok hk ⊢
  obtain ⟨addr, s'⟩ := ev
  simp only at hal hmem hn₁ hn₂ hok hk ⊢
  simp only [hal, bne_self_eq_false, Bool.false_eq_true, ite_false, Option.getD_some]
  refine AddrExpr.checkSP_AllEnvLSE2 ha ?_
  simp only [MachineData.storePairK, Effects.AllEnvLSE2]
  rw [show addr + MemWidth.W64.bytesv = addr + 8 from rfl, hn₁, hn₂]
  exact ⟨rfl, fun _ => ⟨hok, fun b g' hs => hk b g' hs _ hpl'⟩, fun hn => (hn hmem).elim⟩

end MachineWP

/-! ## `vcgen` -/

/-- A `Program` run in the environment `env` under FEAT_LSE2, relative to the
declared locations `D`: the program type of `MachineWP.instWPEnvLSE2`. -/
structure EnvProgramLSE2 (D : SharedEnv.Layout) (env : SharedEnv) where
  prog : Program

namespace MachineWP

/-- A triple on an `EnvProgramLSE2` is the LSE2 environment wp of the ambient
code. -/
scoped instance instWPEnvLSE2 [CodeEnv] (D : SharedEnv.Layout) (env : SharedEnv) :
    WP (EnvProgramLSE2 D env) Unit (MachineData → env.State → Prop)
      (Int64 → MachineData → env.State → Prop) where
  wpTrans q := ⟨fun Q E s g => cenv.wpEnvLSE2 D env q.prog (Q ()) E s g⟩
  wp_trans_monotone _ _ _ _ _ hE hQ := fun _ _ h =>
    Executable.wpEnvLSE2_mono (fun s' g' => hQ () s' g') hE h

/-- A triple on `⟨q⟩` is a `TripleEnvLSE2` on `q`. -/
theorem TripleEnvLSE2.of_triple [CodeEnv] {D : SharedEnv.Layout} {env : SharedEnv}
    {P : MachineData → env.State → Prop} {q : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop}
    (h : ⦃ P ⦄ (⟨q⟩ : EnvProgramLSE2 D env) ⦃ fun _ => Q; E ⦄) : TripleEnvLSE2 D env P q Q E :=
  fun s g hp => h.le_wp s g hp

/-- A `TripleEnvLSE2` on `q` is a triple on `⟨q⟩`, from any stronger
precondition. -/
theorem TripleEnvLSE2.triple [CodeEnv] {D : SharedEnv.Layout} {env : SharedEnv}
    {P P' : MachineData → env.State → Prop} {q : Program} {Q : Unit → MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop}
    (hP : ∀ s g, P s g → P' s g) (h : TripleEnvLSE2 D env P' q (Q ()) E) :
    ⦃ P ⦄ (⟨q⟩ : EnvProgramLSE2 D env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g hp => h s g (hP s g hp)

end MachineWP

section Specs

open MachineWP

variable [CodeEnv] {D : SharedEnv.Layout} {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

@[spec] theorem MachineWP.env_lse2_nil_spec :
    ⦃ fun s g => Q () s g ⦄ (⟨[]⟩ : EnvProgramLSE2 D env) ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => fun _ _ => Eventually.done _ (Or.inl ⟨rfl, h⟩)

/-- **The generic rule under FEAT_LSE2.** Any cell, in an environment that
meets `LSE2Disc` for `D`: run it by the `EnvProgram` rules (every
shared-location rule, the generic `env_lift_spec`, the combined rules), with
the tail's LSE2 wp as its postcondition. The embedding
(`Executable.wpEnvLSE2_of_wpEnv`). -/
@[spec low] theorem MachineWP.env_lse2_lift_spec [SharedEnv.LSE2Disc D env] (d : Directive) :
    ⦃ fun s g => WP.wp (⟨[d]⟩ : EnvProgram env) (fun _ s' g' => WP.wp (⟨p⟩ : EnvProgramLSE2 D env) Q E s' g')
        E s g ⦄
      (⟨d :: p⟩ : EnvProgramLSE2 D env) ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => Executable.wpEnvLSE2_cons (Executable.wpEnvLSE2_of_wpEnv h)

/-- `LDP Xt1, Xt2, [Xn|SP …]` as one 16-byte load (`ldp_lse2_shared`). Above
the generic rule: on a pair in `dmem` erase it for that call
(`vcgen [-MachineWP.ldp_lse2_shared_spec]`). -/
@[spec] theorem MachineWP.ldp_lse2_shared_spec (dst1 dst2 : RegOrZr .W64) (a : AddrExpr) :
    ⦃ fun s g => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        (e.1 % 16 = 0) ⊓ ((e.1, 16) ∈ D) ⊓
          (Mem.loadInt e.2.dmem e.1 8 = none) ⊓ (Mem.loadInt e.2.dmem (e.1 + 8) 8 = none) ⊓
          env.ok (.load .plain false e.1 16) g ⊓
          (∀ v g', env.step (.load .plain false e.1 16) g v g' →
            let r := (e.2.regs.setRegOrZr dst1 (v.setWidth 64)).setRegOrZr dst2 ((v >>> 64).setWidth 64)
            WP.wp (⟨p⟩ : EnvProgramLSE2 D env) Q E { e.2 with regs := r } g') ⦄
      (⟨Directive.instr ⟨.W64, .LDP dst1 dst2 a⟩ :: p⟩ : EnvProgramLSE2 D env) ⦃ Q; E ⦄ :=
  TripleEnvLSE2.triple (fun _ _ h => by
      simp only [meet_prop_eq_and] at h
      exact ⟨h.1, fun rng => ⟨(h.2 rng).1.1.1.1.1, (h.2 rng).1.1.1.1.2, (h.2 rng).1.1.1.2,
        (h.2 rng).1.1.2, (h.2 rng).1.2, (h.2 rng).2⟩⟩)
    (ldp_lse2_shared D env dst1 dst2 a)

/-- `STP Xt1, Xt2, [Xn|SP …]` as one 16-byte store (`stp_lse2_shared`).
Above the generic rule: on a pair in `dmem` erase it for that call
(`vcgen [-MachineWP.stp_lse2_shared_spec]`). -/
@[spec] theorem MachineWP.stp_lse2_shared_spec (src1 src2 : RegOrZr .W64) (a : AddrExpr) :
    ⦃ fun s g => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let v := ((s.regs.getRegOrZr src2).setWidth 128 <<< 64) ||| (s.regs.getRegOrZr src1).setWidth 128
        (e.1 % 16 = 0) ⊓ ((e.1, 16) ∈ D) ⊓
          (Mem.loadInt e.2.dmem e.1 8 = none) ⊓ (Mem.loadInt e.2.dmem (e.1 + 8) 8 = none) ⊓
          env.ok (.store .plain false e.1 16 v) g ⊓
          (∀ ok g', env.step (.store .plain false e.1 16 v) g ok g' →
            WP.wp (⟨p⟩ : EnvProgramLSE2 D env) Q E e.2 g') ⦄
      (⟨Directive.instr ⟨.W64, .STP src1 src2 a⟩ :: p⟩ : EnvProgramLSE2 D env) ⦃ Q; E ⦄ :=
  TripleEnvLSE2.triple (fun _ _ h => by
      simp only [meet_prop_eq_and] at h
      exact ⟨h.1, fun rng => ⟨(h.2 rng).1.1.1.1.1, (h.2 rng).1.1.1.1.2, (h.2 rng).1.1.1.2,
        (h.2 rng).1.1.2, (h.2 rng).1.2, (h.2 rng).2⟩⟩)
    (stp_lse2_shared D env src1 src2 a)

end Specs
