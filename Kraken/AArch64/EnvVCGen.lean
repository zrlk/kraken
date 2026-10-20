/-
`vcgen` over the environment-aware wp, AArch64 (design note
`Kraken/Promising/EnvWP.md` §8). Copied from x64's
`Kraken/EnvVCGen.lean`, adapted to the AArch64 rules of
`Kraken/AArch64/EnvWPRules.lean`.

- `EnvProgram env`, `MachineWP.instWPEnv`, `TripleEnv.of_triple`,
  `TripleEnv.triple`: as on x64.
- **The generic rule** `env_lift_spec` (`@[spec low]`, `[env.Skips]`): every
  AArch64 `MachineWP` rule (mapped memory) serves the environment wp,
  the environment state passed through. Some `MachineWP` rules are `low` too
  (`add_e_spec`, `orr_s_spec`); they are keyed on `Program`, so they are only
  tried for the inner wp of `[d]` and do not compete with this rule.
- The shared-location rules, restated over `EnvProgram` (`*_shared_spec`):
  * the acquire, exclusive, release and read-modify-write accesses (`LDAR`
    and its kin, `STLR`, `STXR`, `CAS`, `SWP`, `LD<op>`) are `@[spec]`, above
    the generic rule; on a location in `dmem` erase the rule for that call
    (`vcgen [-cas_shared_spec]`);
  * `CASP` (all ordering variants, both halves shared): `casp_shared_spec`
    in any environment (it leaves the `SharedEnv.CaspEnv` obligation), and
    `casp_lastWrite_spec` (`high`, keyed on `EnvProgram (lastWrite L)`), which
    collapses it to one continuation;
  * the barriers (`DMB`, `DSB`, `ISB`) are `@[spec 50]`, below the generic
    rule, which steps them as no-ops where fences skip;
  * `LDRB`/`LDRH`/`STRB`/`STRH` and `LDP`/`STP` are not registered: pass them
    to the `vcgen` call that needs them.
- **Combined rules** for `LDR` and `STR` (`ldr_env_spec`, `str_env_spec`,
  `@[spec]`): mapped or shared in one rule, one disjunction in front of one
  continuation, as x64's `mov_load_env_spec`. No `Skips` needed. Likewise
  for the unscaled and literal forms, which have no `MachineWP` rule, so these
  are their only `vcgen` rules: `ldur_env_spec`, `stur_env_spec`,
  `ldr_lit_env_spec` (`LDR Rt, label`) and `ldr_pool_env_spec` (`LDR Rt,
  =expr`, no access at all).
- **Combined rules for the sign-extending loads** (`@[spec]`):
  `ldrsb_env_spec`, `ldrsh_env_spec`, `ldrsw_env_spec`, `ldursb_env_spec`,
  `ldursh_env_spec`, `ldursw_env_spec`, `ldrsw_lit_env_spec`,
  `ldrsw_pool_env_spec`, and `ldpsw_env_spec` (each of the two slots mapped
  or shared on its own). Keyed on their own instructions, so no other
  instruction tries them.

A program defined by name must be unfolded first (`unfold prog; vcgen`).
-/
import Kraken.AArch64.EnvWPRules

open Kraken
open Std.WP
open Lean.Order

/-- A `Program` run in the environment `env`: the program type of the
environment wp's `WP` instance (`MachineWP.instWPEnv`). -/
structure EnvProgram (env : SharedEnv) where
  prog : Program

namespace MachineWP

/-- A triple on an `EnvProgram` is the environment wp of the ambient code. -/
scoped instance instWPEnv [CodeEnv] (env : SharedEnv) :
    WP (EnvProgram env) Unit (MachineData → env.State → Prop)
      (Int64 → MachineData → env.State → Prop) where
  wpTrans q := ⟨fun Q E s g => cenv.wpEnv env q.prog (Q ()) E s g⟩
  wp_trans_monotone _ _ _ _ _ hE hQ := fun _ _ h =>
    Executable.wpEnv_mono (fun s' g' => hQ () s' g') hE h

/-- Unfold an `EnvProgram` triple's wp into the environment wp. -/
theorem wpEnv_eq [CodeEnv] {env : SharedEnv} (q : EnvProgram env)
    (Q : Unit → MachineData → env.State → Prop) (E : Int64 → MachineData → env.State → Prop)
    (s : MachineData) (g : env.State) :
    WP.wp q Q E s g = cenv.wpEnv env q.prog (Q ()) E s g := rfl

/-- A triple on `⟨q⟩` is a `TripleEnv` on `q`. -/
theorem TripleEnv.of_triple [CodeEnv] {env : SharedEnv} {P : MachineData → env.State → Prop}
    {q : Program} {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    (h : ⦃ P ⦄ (⟨q⟩ : EnvProgram env) ⦃ fun _ => Q; E ⦄) : TripleEnv env P q Q E :=
  fun s g hp => h.le_wp s g hp

/-- A `TripleEnv` on `q` is a triple on `⟨q⟩`, from any stronger
precondition. -/
theorem TripleEnv.triple [CodeEnv] {env : SharedEnv} {P P' : MachineData → env.State → Prop}
    {q : Program} {Q : Unit → MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop}
    (hP : ∀ s g, P s g → P' s g) (h : TripleEnv env P' q (Q ()) E) :
    ⦃ P ⦄ (⟨q⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g hp => h s g (hP s g hp)

end MachineWP

/-! ## The structural rules and the generic rule -/

section Specs

open MachineWP

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

@[spec] theorem MachineWP.env_nil_spec :
    ⦃ fun s g => Q () s g ⦄ (⟨[]⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun _ _ h => fun _ _ => Eventually.done _ (Or.inl ⟨rfl, h⟩)

/-- **The generic rule.** Any cell, in an environment whose fences skip: run
it by the `MachineWP` rules (the `Program` wp of `[d]`), with the tail's
environment wp at the same environment state as its postcondition. Lifting
(`Executable.wpEnv_of_wp`) with the invariant `(· = g)`. -/
@[spec low] theorem MachineWP.env_lift_spec [env.Skips] (d : Directive) :
    ⦃ fun s g => WP.wp ([d] : Program) (fun _ s' => WP.wp (⟨p⟩ : EnvProgram env) Q E s' g)
        (fun a s' => E a s' g) s ⦄
      (⟨d :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    apply Executable.wpEnv_cons
    have hI := (SharedEnv.Skips.fencesSkip (env := env)).fenceInv_eq g
    exact Executable.wpEnv_mono (fun _ _ ⟨h1, h2⟩ => h2 ▸ h1) (fun _ _ _ ⟨h1, h2⟩ => h2 ▸ h1)
      (Executable.wpEnv_of_wp (Q := fun s' => cenv.wpEnv env p (Q ()) E s' g)
        (E := fun a s' => E a s' g) hI h g rfl)

end Specs

/-! ## The shared-location rules over `EnvProgram`

Each is its `Kraken/AArch64/EnvWPRules.lean` theorem with `⊓` for `∧` and the
tail as an `EnvProgram` wp, so that `vcgen` continues into it. -/

section SharedSpecs

open MachineWP

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

/-- `LDAR`/`LDAPR`/`LDXR`/`LDAXR Rt, [Xn|SP]` (+`B`/`H`) on a shared location
(`ldar_shared`). -/
@[spec] theorem MachineWP.ldar_shared_spec {w : RegWidth} (k : LoadKind) (xcl : Bool)
    (sz : MemWidth) (dst : RegOrZr w) (base : RegOrSp .W64) :
    ⦃ fun s g =>
        let a := s.regs.getRegOrSp base
        base.SPAligned s ⊓ (Mem.loadInt s.dmem a sz.bytes = none) ⊓ env.ok (.load k xcl a sz.bytes) g ⊓
          (∀ v g', env.step (.load k xcl a sz.bytes) g v g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with regs := s.regs.setRegOrZr dst ((v.setWidth sz.bits).setWidth w.bits) } g') ⦄
      (⟨Directive.instr ⟨w, .LDAR k xcl sz dst base⟩ :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple
    (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (ldar_shared env k xcl sz dst base)

/-- `STLR Rt, [Xn|SP]` (+`B`/`H`) on a shared location (`stlr_shared`). -/
@[spec] theorem MachineWP.stlr_shared_spec {w : RegWidth} (sz : MemWidth) (src : RegOrZr w)
    (base : RegOrSp .W64) :
    ⦃ fun s g =>
        let a := s.regs.getRegOrSp base
        let v := ((s.regs.getRegOrZr src).setWidth sz.bits).setWidth 128
        base.SPAligned s ⊓ (Mem.loadInt s.dmem a sz.bytes = none) ⊓
          env.ok (.store .rel false a sz.bytes v) g ⊓
          (∀ ok g', env.step (.store .rel false a sz.bytes v) g ok g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr ⟨w, .STLR sz src base⟩ :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple
    (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (stlr_shared env sz src base)

/-- `STXR`/`STLXR Ws, Rt, [Xn|SP]` (+`B`/`H`) on a shared location
(`stxr_shared`): success and failure are the environment's answer. -/
@[spec] theorem MachineWP.stxr_shared_spec {w : RegWidth} (k : StoreKind) (sz : MemWidth)
    (status : RegOrZr .W32) (src : RegOrZr w) (base : RegOrSp .W64) :
    ⦃ fun s g =>
        let a := s.regs.getRegOrSp base
        let v := ((s.regs.getRegOrZr src).setWidth sz.bits).setWidth 128
        base.SPAligned s ⊓ (Mem.loadInt s.dmem a sz.bytes = none) ⊓
          env.ok (.store k true a sz.bytes v) g ⊓
          (∀ ok g', env.step (.store k true a sz.bytes v) g ok g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with regs := s.regs.setRegOrZr status (if ok then 0#32 else 1#32) } g') ⦄
      (⟨Directive.instr ⟨w, .STXR k sz status src base⟩ :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple
    (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (stxr_shared env k sz status src base)

/-- `CAS`/`CASA`/`CASL`/`CASAL Rs, Rt, [Xn|SP]` (+`B`/`H`) on a shared
location (`cas_shared`). -/
@[spec] theorem MachineWP.cas_shared_spec {w : RegWidth} (k : RmwKind) (sz : MemWidth)
    (rs rt : RegOrZr w) (base : RegOrSp .W64) :
    ⦃ fun s g =>
        let a := s.regs.getRegOrSp base
        let cmp := (s.regs.getRegOrZr rs).setWidth sz.bits
        let new := (s.regs.getRegOrZr rt).setWidth sz.bits
        let acc := SharedAccess.rmw k a sz.bytes
          (rmwOpBits sz.bits (fun old => if old == cmp then some new else none))
        base.SPAligned s ⊓ (Mem.loadInt s.dmem a sz.bytes = none) ⊓ env.ok acc g ⊓
          (∀ v g', env.step acc g v g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with regs := s.regs.setRegOrZr rs ((v.setWidth sz.bits).setWidth w.bits) } g') ⦄
      (⟨Directive.instr ⟨w, .CAS k sz rs rt base⟩ :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple
    (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (cas_shared env k sz rs rt base)

/-- `SWP`/`SWPA`/`SWPL`/`SWPAL Rs, Rt, [Xn|SP]` (+`B`/`H`) on a shared
location (`swp_shared`). -/
@[spec] theorem MachineWP.swp_shared_spec {w : RegWidth} (k : RmwKind) (sz : MemWidth)
    (rs rt : RegOrZr w) (base : RegOrSp .W64) :
    ⦃ fun s g =>
        let a := s.regs.getRegOrSp base
        let new := (s.regs.getRegOrZr rs).setWidth sz.bits
        let acc := SharedAccess.rmw k a sz.bytes (rmwOpBits sz.bits (fun _ => some new))
        base.SPAligned s ⊓ (Mem.loadInt s.dmem a sz.bytes = none) ⊓ env.ok acc g ⊓
          (∀ v g', env.step acc g v g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with regs := s.regs.setRegOrZr rt ((v.setWidth sz.bits).setWidth w.bits) } g') ⦄
      (⟨Directive.instr ⟨w, .SWP k sz rs rt base⟩ :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple
    (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (swp_shared env k sz rs rt base)

/-- `LD<op>` (+`A`/`L`/`AL`, +`B`/`H`) and `ST<op>` on a shared location
(`ldop_shared`). -/
@[spec] theorem MachineWP.ldop_shared_spec {w : RegWidth} (op : AtomicOp) (k : RmwKind)
    (sz : MemWidth) (rs rt : RegOrZr w) (base : RegOrSp .W64) :
    ⦃ fun s g =>
        let a := s.regs.getRegOrSp base
        let arg := (s.regs.getRegOrZr rs).setWidth sz.bits
        let acc := SharedAccess.rmw k a sz.bytes (rmwOpBits sz.bits (fun old => some (op.apply old arg)))
        base.SPAligned s ⊓ (Mem.loadInt s.dmem a sz.bytes = none) ⊓ env.ok acc g ⊓
          (∀ v g', env.step acc g v g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with regs := s.regs.setRegOrZr rt ((v.setWidth sz.bits).setWidth w.bits) } g') ⦄
      (⟨Directive.instr ⟨w, .LDOP op k sz rs rt base⟩ :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple
    (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    (ldop_shared env op k sz rs rt base)

/-- `CASP`/`CASPA`/`CASPL`/`CASPAL Rs1, Rs2, Rt1, Rt2, [Xn|SP]` with both
halves shared, in any environment (`casp_shared`). `vcgen` stops at the
`CaspEnv` obligation (its continuation is under the per-half quantifiers); in
`lastWrite` the rule below fires instead. -/
@[spec] theorem MachineWP.casp_shared_spec {w : RegWidth} (k : RmwKind) (rs1 rs2 rt1 rt2 : RegOrZr w)
    (base : RegOrSp .W64) :
    ⦃ fun s g =>
        let a := s.regs.getRegOrSp base
        base.SPAligned s ⊓ (Mem.loadInt s.dmem a (w : MemWidth).bytes = none) ⊓
          (Mem.loadInt s.dmem (a + (w : MemWidth).bytesv) (w : MemWidth).bytes = none) ⊓
          env.CaspEnv k a w (s.regs.getRegOrZr rs1) (s.regs.getRegOrZr rs2) (s.regs.getRegOrZr rt1)
            (s.regs.getRegOrZr rt2) g (fun o₁ o₂ g' =>
              WP.wp (⟨p⟩ : EnvProgram env) Q E { s with regs := (s.regs.setRegOrZr rs1 o₁).setRegOrZr rs2 o₂ } g') ⦄
      (⟨Directive.instr ⟨w, .CASP k rs1 rs2 rt1 rt2 base⟩ :: p⟩ : EnvProgram env)
    ⦃ Q; E ⦄ :=
  TripleEnv.triple
    (fun _ _ h => by
      simp only [meet_prop_eq_and] at h
      exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2.mono fun _ _ _ h => h⟩)
    (casp_shared env k rs1 rs2 rt1 rt2 base)

/-- `DMB <option>` asking the environment (`dmb_shared`). Below the generic
rule: it fires only where `env` has no `Skips` instance. -/
@[spec 50] theorem MachineWP.dmb_shared_spec (k : FenceKind) :
    ⦃ fun s g => env.ok (.fence k) g ⊓
        (∀ g', env.step (.fence k) g () g' → WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr ⟨.W64, .DMB k⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact h) (dmb_shared env k)

/-- `DSB <option>` asking the environment (`dsb_shared`), as `dmb_shared_spec`. -/
@[spec 50] theorem MachineWP.dsb_shared_spec (k : FenceKind) :
    ⦃ fun s g =>
        let k' := if k == .st then FenceKind.stAll else k
        env.ok (.fence k') g ⊓
          (∀ g', env.step (.fence k') g () g' → WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr ⟨.W64, .DSB k⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact h) (dsb_shared env k)

/-- `ISB` asking the environment (`isb_shared`), as `dmb_shared_spec`. -/
@[spec 50] theorem MachineWP.isb_shared_spec :
    ⦃ fun s g => env.ok (.fence .isb) g ⊓
        (∀ g', env.step (.fence .isb) g () g' → WP.wp (⟨p⟩ : EnvProgram env) Q E s g') ⦄
      (⟨Directive.instr ⟨.W64, .ISB⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by simp only [meet_prop_eq_and] at h; exact h) (isb_shared env)

/-! The narrow and paired plain accesses: not `@[spec]` (a location in `dmem`
is the common case and is the generic rule's); pass them to the `vcgen` call
that accesses a shared location with one. -/

/-- `LDRB Wt, [Xn|SP …]` on a shared location (`ldrb_shared`). -/
theorem MachineWP.ldrb_shared_spec (dst : RegOrZr .W32) (a : AddrExpr) :
    ⦃ fun s g => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        (Mem.loadInt e.2.dmem e.1 1 = none) ⊓ env.ok (.load .plain false e.1 1) g ⊓
          (∀ v g', env.step (.load .plain false e.1 1) g v g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { e.2 with regs := e.2.regs.setRegOrZr dst ((v.setWidth 8).setWidth 32) } g') ⦄
      (⟨Directive.instr ⟨.W32, .LDRB dst a⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by
      simp only [meet_prop_eq_and] at h
      exact ⟨h.1, fun rng => ⟨(h.2 rng).1.1, (h.2 rng).1.2, (h.2 rng).2⟩⟩)
    (ldrb_shared env dst a)

/-- `LDRH Wt, [Xn|SP …]` on a shared location (`ldrh_shared`). -/
theorem MachineWP.ldrh_shared_spec (dst : RegOrZr .W32) (a : AddrExpr) :
    ⦃ fun s g => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        (Mem.loadInt e.2.dmem e.1 2 = none) ⊓ env.ok (.load .plain false e.1 2) g ⊓
          (∀ v g', env.step (.load .plain false e.1 2) g v g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { e.2 with regs := e.2.regs.setRegOrZr dst ((v.setWidth 16).setWidth 32) } g') ⦄
      (⟨Directive.instr ⟨.W32, .LDRH dst a⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by
      simp only [meet_prop_eq_and] at h
      exact ⟨h.1, fun rng => ⟨(h.2 rng).1.1, (h.2 rng).1.2, (h.2 rng).2⟩⟩)
    (ldrh_shared env dst a)

/-- `STRB Wt, [Xn|SP …]` on a shared location (`strb_shared`). -/
theorem MachineWP.strb_shared_spec (src : RegOrZr .W32) (a : AddrExpr) :
    ⦃ fun s g => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let v := ((s.regs.getRegOrZr src).setWidth 8).setWidth 128
        (Mem.loadInt e.2.dmem e.1 1 = none) ⊓ env.ok (.store .plain false e.1 1 v) g ⊓
          (∀ ok g', env.step (.store .plain false e.1 1 v) g ok g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E e.2 g') ⦄
      (⟨Directive.instr ⟨.W32, .STRB src a⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by
      simp only [meet_prop_eq_and] at h
      exact ⟨h.1, fun rng => ⟨(h.2 rng).1.1, (h.2 rng).1.2, (h.2 rng).2⟩⟩)
    (strb_shared env src a)

/-- `STRH Wt, [Xn|SP …]` on a shared location (`strh_shared`). -/
theorem MachineWP.strh_shared_spec (src : RegOrZr .W32) (a : AddrExpr) :
    ⦃ fun s g => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let v := ((s.regs.getRegOrZr src).setWidth 16).setWidth 128
        (Mem.loadInt e.2.dmem e.1 2 = none) ⊓ env.ok (.store .plain false e.1 2 v) g ⊓
          (∀ ok g', env.step (.store .plain false e.1 2 v) g ok g' →
            WP.wp (⟨p⟩ : EnvProgram env) Q E e.2 g') ⦄
      (⟨Directive.instr ⟨.W32, .STRH src a⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by
      simp only [meet_prop_eq_and] at h
      exact ⟨h.1, fun rng => ⟨(h.2 rng).1.1, (h.2 rng).1.2, (h.2 rng).2⟩⟩)
    (strh_shared env src a)

/-- `LDP Rt1, Rt2, [Xn|SP …]` with both slots shared (`ldp_shared`). -/
theorem MachineWP.ldp_shared_spec {w : RegWidth} (dst1 dst2 : RegOrZr w) (a : AddrExpr) :
    ⦃ fun s g => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let a₂ := e.1 + BitVec.ofNat 64 w.bytes
        (Mem.loadInt e.2.dmem e.1 w.bytes = none) ⊓ (Mem.loadInt e.2.dmem a₂ w.bytes = none) ⊓
          env.ok (.load .plain false e.1 w.bytes) g ⊓
          (∀ v₁ g₁, env.step (.load .plain false e.1 w.bytes) g v₁ g₁ →
            env.ok (.load .plain false a₂ w.bytes) g₁ ⊓
            (∀ v₂ g₂, env.step (.load .plain false a₂ w.bytes) g₁ v₂ g₂ →
              let r := (e.2.regs.setRegOrZr dst1 (v₁.setWidth w.bits)).setRegOrZr dst2 (v₂.setWidth w.bits)
              WP.wp (⟨p⟩ : EnvProgram env) Q E { e.2 with regs := r } g₂)) ⦄
      (⟨Directive.instr ⟨w, .LDP dst1 dst2 a⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by
      simp only [meet_prop_eq_and] at h
      exact ⟨h.1, fun rng => ⟨(h.2 rng).1.1.1, (h.2 rng).1.1.2, (h.2 rng).1.2, (h.2 rng).2⟩⟩)
    (ldp_shared env dst1 dst2 a)

/-- `STP Rt1, Rt2, [Xn|SP …]` with both slots shared (`stp_shared`). -/
theorem MachineWP.stp_shared_spec {w : RegWidth} (src1 src2 : RegOrZr w) (a : AddrExpr) :
    ⦃ fun s g => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let a₂ := e.1 + BitVec.ofNat 64 w.bytes
        let v₁ := (s.regs.getRegOrZr src1).setWidth 128
        let v₂ := (s.regs.getRegOrZr src2).setWidth 128
        (Mem.loadInt e.2.dmem e.1 w.bytes = none) ⊓ (Mem.loadInt e.2.dmem a₂ w.bytes = none) ⊓
          env.ok (.store .plain false e.1 w.bytes v₁) g ⊓
          (∀ b₁ g₁, env.step (.store .plain false e.1 w.bytes v₁) g b₁ g₁ →
            env.ok (.store .plain false a₂ w.bytes v₂) g₁ ⊓
            (∀ b₂ g₂, env.step (.store .plain false a₂ w.bytes v₂) g₁ b₂ g₂ →
              WP.wp (⟨p⟩ : EnvProgram env) Q E e.2 g₂)) ⦄
      (⟨Directive.instr ⟨w, .STP src1 src2 a⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => by
      simp only [meet_prop_eq_and] at h
      exact ⟨h.1, fun rng => ⟨(h.2 rng).1.1.1, (h.2 rng).1.1.2, (h.2 rng).1.2, (h.2 rng).2⟩⟩)
    (stp_shared env src1 src2 a)

end SharedSpecs

/-! ### `CASP` in `lastWrite`

The `CaspEnv` obligation of `casp_shared_spec` collapsed by
`SharedEnv.lastWrite_caspEnv_iff`: one continuation, at the old halves and
the state `SharedEnv.caspLW` (both writes on a match, otherwise unchanged), so
`vcgen` continues into the tail once. Keyed on `EnvProgram (lastWrite L)` and above
`casp_shared_spec` (`high`), so it is the rule `vcgen` uses in `lastWrite`. -/

section CaspLastWrite

open MachineWP

variable [CodeEnv] {L : SharedEnv.Layout} {Q : Unit → MachineData → (SharedEnv.lastWrite L).State → Prop}
  {E : Int64 → MachineData → (SharedEnv.lastWrite L).State → Prop} {p : Program}

/-- `CASP` (all ordering variants) in `lastWrite L` (`casp_lastWrite`). -/
@[spec high] theorem MachineWP.casp_lastWrite_spec {w : RegWidth} (k : RmwKind) (rs1 rs2 rt1 rt2 : RegOrZr w)
    (base : RegOrSp .W64) :
    ⦃ fun s g =>
        let a := s.regs.getRegOrSp base
        let a₂ := a + (w : MemWidth).bytesv
        let o₁ := (g a).setWidth (w : MemWidth).bits
        let o₂ := (g a₂).setWidth (w : MemWidth).bits
        base.SPAligned s ⊓ (Mem.loadInt s.dmem a (w : MemWidth).bytes = none) ⊓
          (Mem.loadInt s.dmem a₂ (w : MemWidth).bytes = none) ⊓
          ((a, (w : MemWidth).bytes) ∈ L) ⊓ ((a₂, (w : MemWidth).bytes) ∈ L) ⊓
          WP.wp (⟨p⟩ : EnvProgram (SharedEnv.lastWrite L)) Q E
            { s with regs := (s.regs.setRegOrZr rs1 o₁).setRegOrZr rs2 o₂ }
            (SharedEnv.caspLW g a w (s.regs.getRegOrZr rs1) (s.regs.getRegOrZr rs2) (s.regs.getRegOrZr rt1)
              (s.regs.getRegOrZr rt2)) ⦄
      (⟨Directive.instr ⟨w, .CASP k rs1 rs2 rt1 rt2 base⟩ :: p⟩ : EnvProgram (SharedEnv.lastWrite L))
    ⦃ Q; E ⦄ :=
  TripleEnv.triple
    (fun _ _ h => by
      simp only [meet_prop_eq_and] at h
      exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩)
    (casp_lastWrite k rs1 rs2 rt1 rt2 base)

end CaspLastWrite

/-! ## Combined rules for `LDR` and `STR`

Mapped or shared, in one rule, as x64's `mov_load_env_spec`: the bytes are in
`dmem` and the access reads or writes them with the environment state
unchanged, or they are not and the access is a plain one the environment must
permit, with `dmem` unchanged. One disjunction, one continuation. -/

section CombinedSpecs

variable {env : SharedEnv} {g : env.State} {P : MachineState → env.State → Prop}

private theorem AddrExpr.checkSP_AllEnv' {a : AddrExpr} {s : MachineData} {ok : Unit → Effects}
    (ha : a.SPAligned s) (hk : (ok ()).AllEnv env g P) : (a.checkSPAlignment s ok).AllEnv env g P := by
  obtain ⟨⟨b, w⟩, off⟩ := a
  cases b with
  | reg r => exact hk
  | SP =>
    have h := ha rfl
    simp only [AddrExpr.checkSPAlignment, Reg64s.getRegOrSp_SP, h, bne_self_eq_false,
      Bool.false_eq_true, ite_false]
    exact hk

/-- `MachineData.load`, mapped or not. -/
private theorem MachineData.load_AllEnv' {s : MachineData} {addr : BitVec 64} {w : MemWidth}
    {ret : w.type → MachineData → Effects}
    (hok : Mem.loadInt s.dmem addr w.bytes = none → env.ok (.load .plain false addr w.bytes) g)
    (hk : ∀ x g',
      (∃ v, Mem.loadInt s.dmem addr w.bytes = some v ∧ x = BitVec.ofInt w.bits v ∧ g' = g)
        ∨ (Mem.loadInt s.dmem addr w.bytes = none ∧
          ∃ v, env.step (.load .plain false addr w.bytes) g v g' ∧ x = v.setWidth w.bits) →
      (ret x s).AllEnv env g' P) :
    (s.load addr w ret).AllEnv env g P := by
  cases hl : Mem.loadInt s.dmem addr w.bytes with
  | none =>
    simp only [MachineData.load, Effects.AllEnv, hl]
    exact ⟨hok hl, fun v g' hs => hk _ g' (.inr ⟨hl, v, hs, rfl⟩)⟩
  | some i =>
    simp only [MachineData.load, Effects.AllEnv, hl]
    exact hk _ g (.inl ⟨i, hl, rfl, rfl⟩)

/-- `MachineData.store`, mapped or not. -/
private theorem MachineData.store_AllEnv' {s : MachineData} {addr : BitVec 64} {w : MemWidth}
    {val : w.type} {ret : MachineData → Effects}
    (hok : Mem.loadInt s.dmem addr w.bytes = none →
      env.ok (.store .plain false addr w.bytes (val.setWidth 128)) g)
    (hk : ∀ m g',
      ((Mem.loadInt s.dmem addr w.bytes).isSome = true ∧
          m = Mem.storeInt s.dmem addr w.bytes val.toInt ∧ g' = g)
        ∨ (Mem.loadInt s.dmem addr w.bytes = none ∧ m = s.dmem ∧
          ∃ b, env.step (.store .plain false addr w.bytes (val.setWidth 128)) g b g') →
      (ret { s with dmem := m }).AllEnv env g' P) :
    (s.store addr val ret).AllEnv env g P := by
  cases hl : Mem.loadInt s.dmem addr w.bytes with
  | none =>
    simp only [MachineData.store, Effects.AllEnv, hl]
    exact ⟨hok hl, fun b g' hs => hk s.dmem g' (.inr ⟨hl, rfl, b, hs⟩)⟩
  | some i =>
    simp only [MachineData.store, Effects.AllEnv, hl]
    exact hk _ g (.inl ⟨by rw [hl]; rfl, rfl, rfl⟩)

end CombinedSpecs

namespace MachineWP

/-- Unfold the fall-through address past one instruction cell. -/
private theorem after_instr' [CodeEnv] {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

set_option hygiene false in
/-- One cell: place it, step it, and leave the `AllEnv` goal of its
fall-through tree, with the placement of the tail as `hpl'`. -/
local macro "env_step" : tactic =>
  `(tactic| (
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr' hseg]
    refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩
    simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setRegOrZr,
      BitVec.take_eq_setWidth]))

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

/-- `LDR Rt, [Xn|SP …]`, mapped or shared: `Rt` gets the `dmem` bytes, or any
value the environment allows; then the base writeback. -/
@[spec] theorem ldr_env_spec {w : RegWidth} (dst : RegOrZr w) (a : AddrExpr) :
    ⦃ fun s g => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        (Mem.loadInt e.2.dmem e.1 w.bytes = none → env.ok (.load .plain false e.1 w.bytes) g) ⊓
          (∀ x g',
            (∃ v, Mem.loadInt e.2.dmem e.1 w.bytes = some v ∧ x = BitVec.ofInt w.bits v ∧ g' = g)
              ∨ (Mem.loadInt e.2.dmem e.1 w.bytes = none ∧
                ∃ v, env.step (.load .plain false e.1 w.bytes) g v g' ∧ x = v.setWidth w.bits) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { e.2 with regs := e.2.regs.setRegOrZr dst x } g') ⦄
      (⟨Directive.instr ⟨w, .LDR dst (.addr a)⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    obtain ⟨hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
    simp only [AddrOrLit.interpLoad, AddrExpr.interpLoad]
    exact AddrExpr.checkSP_AllEnv' ha (MachineData.load_AllEnv' hok fun x g' ho => hk x g' ho _ hpl')

/-- `STR Rt, [Xn|SP …]`, mapped or shared: the `dmem` bytes are written, or
the environment is; then the base writeback. -/
@[spec] theorem str_env_spec {w : RegWidth} (src : RegOrZr w) (a : AddrExpr) :
    ⦃ fun s g => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let v := (s.regs.getRegOrZr src).setWidth 128
        (Mem.loadInt e.2.dmem e.1 w.bytes = none → env.ok (.store .plain false e.1 w.bytes v) g) ⊓
          (∀ m g',
            ((Mem.loadInt e.2.dmem e.1 w.bytes).isSome = true ∧
                m = Mem.storeInt e.2.dmem e.1 w.bytes (s.regs.getRegOrZr src).toInt ∧ g' = g)
              ∨ (Mem.loadInt e.2.dmem e.1 w.bytes = none ∧ m = e.2.dmem ∧
                ∃ ok, env.step (.store .plain false e.1 w.bytes v) g ok g') →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { e.2 with dmem := m } g') ⦄
      (⟨Directive.instr ⟨w, .STR src a⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    obtain ⟨hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
    simp only [AddrExpr.interpStore]
    exact AddrExpr.checkSP_AllEnv' ha (MachineData.store_AllEnv' hok fun m g' ho => hk m g' ho _ hpl')

/-- `LDUR Rt, [Xn|SP, #simm9]`, mapped or shared: as `ldr_env_spec`, no
writeback. (`MachineWP` has no `LDUR` rule; this one serves both cases.) -/
@[spec] theorem ldur_env_spec {w : RegWidth} (dst : RegOrZr w) (a : UnscaledAddrExpr) :
    ⦃ fun s g => a.base.SPAligned s ⊓ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        (Mem.loadInt s.dmem e w.bytes = none → env.ok (.load .plain false e w.bytes) g) ⊓
          (∀ x g',
            (∃ v, Mem.loadInt s.dmem e w.bytes = some v ∧ x = BitVec.ofInt w.bits v ∧ g' = g)
              ∨ (Mem.loadInt s.dmem e w.bytes = none ∧
                ∃ v, env.step (.load .plain false e w.bytes) g v g' ∧ x = v.setWidth w.bits) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with regs := s.regs.setRegOrZr dst x } g') ⦄
      (⟨Directive.instr ⟨w, .LDUR dst a⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    obtain ⟨hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
    simp only [UnscaledAddrExpr.interpLoad]
    exact UnscaledAddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv' hok fun x g' ho => hk x g' ho _ hpl')

/-- `STUR Rt, [Xn|SP, #simm9]`, mapped or shared: as `str_env_spec`, no
writeback. -/
@[spec] theorem stur_env_spec {w : RegWidth} (src : RegOrZr w) (a : UnscaledAddrExpr) :
    ⦃ fun s g => a.base.SPAligned s ⊓ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let v := (s.regs.getRegOrZr src).setWidth 128
        (Mem.loadInt s.dmem e w.bytes = none → env.ok (.store .plain false e w.bytes v) g) ⊓
          (∀ m g',
            ((Mem.loadInt s.dmem e w.bytes).isSome = true ∧
                m = Mem.storeInt s.dmem e w.bytes (s.regs.getRegOrZr src).toInt ∧ g' = g)
              ∨ (Mem.loadInt s.dmem e w.bytes = none ∧ m = s.dmem ∧
                ∃ ok, env.step (.store .plain false e w.bytes v) g ok g') →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with dmem := m } g') ⦄
      (⟨Directive.instr ⟨w, .STUR src a⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    obtain ⟨hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
    simp only [UnscaledAddrExpr.interpStore]
    exact UnscaledAddrExpr.checkSP_AllEnv ha (MachineData.store_AllEnv' hok fun m g' ho => hk m g' ho _ hpl')

/-- `LDR Rt, label`, mapped or shared: as `ldr_env_spec`, from the label's
address. -/
@[spec] theorem ldr_lit_env_spec {w : RegWidth} (dst : RegOrZr w) (l : Label) :
    ⦃ fun s g =>
        let e := (@Labels.label (_root_.Executable.labels cenv) l).toBitVec
        (Mem.loadInt s.dmem e w.bytes = none → env.ok (.load .plain false e w.bytes) g) ⊓
          (∀ x g',
            (∃ v, Mem.loadInt s.dmem e w.bytes = some v ∧ x = BitVec.ofInt w.bits v ∧ g' = g)
              ∨ (Mem.loadInt s.dmem e w.bytes = none ∧
                ∃ v, env.step (.load .plain false e w.bytes) g v g' ∧ x = v.setWidth w.bits) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E { s with regs := s.regs.setRegOrZr dst x } g') ⦄
      (⟨Directive.instr ⟨w, .LDR dst (.lit (.addr ⟨l⟩))⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    simp only [AddrOrLit.interpLoad, Literal.interpLoad, BitVec.ofInt_toInt_int64, Effects.AllEnv]
    exact MachineData.load_AllEnv' hok fun x g' ho => hk x g' ho _ hpl'

/-- `LDR Rt, =expr` (`ldr_pool_env`): no memory access, any environment. -/
@[spec] theorem ldr_pool_env_spec {w : RegWidth} (dst : RegOrZr w) (c : ConstExpr) :
    ⦃ fun s g => ∀ rng,
        let v := BitVec.ofInt w.bits (@ConstExpr.interp (_root_.Executable.labels cenv) c rng).toInt
        WP.wp (⟨p⟩ : EnvProgram env) Q E { s with regs := s.regs.setRegOrZr dst v } g ⦄
      (⟨Directive.instr ⟨w, .LDR dst (.lit (.pool ⟨c⟩))⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => h) (ldr_pool_env env dst c)

/-! ### Sign-extending loads

Mapped or shared, as `ldr_env_spec`, the loaded field sign-extended to the
register. Above the generic rule, which would serve only the mapped case
(`Kraken.AArch64.WP.RulesSignExt`). -/

/-- `LDRSB Rt, [Xn|SP …]`, mapped or shared: the byte, sign-extended; then the base
writeback. -/
@[spec] theorem ldrsb_env_spec {w : RegWidth} (dst : RegOrZr w) (a : AddrExpr) :
    ⦃ fun s g => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        (Mem.loadInt e.2.dmem e.1 1 = none → env.ok (.load .plain false e.1 1) g) ⊓
          (∀ (x : BitVec 8) g',
            (∃ v, Mem.loadInt e.2.dmem e.1 1 = some v ∧ x = BitVec.ofInt 8 v ∧ g' = g)
              ∨ (Mem.loadInt e.2.dmem e.1 1 = none ∧
                ∃ v, env.step (.load .plain false e.1 1) g v g' ∧ x = v.setWidth 8) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { e.2 with regs := e.2.regs.setRegOrZr dst (x.signExtend w.bits) } g') ⦄
      (⟨Directive.instr ⟨w, .LDRSB dst a⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    obtain ⟨hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
    simp only [AddrExpr.interpLoad]
    exact AddrExpr.checkSP_AllEnv' ha (MachineData.load_AllEnv' (w := .W8) hok fun x g' ho =>
      hk x g' ho _ hpl')

/-- `LDRSH Rt, [Xn|SP …]`, mapped or shared, as `ldrsb_env_spec`. -/
@[spec] theorem ldrsh_env_spec {w : RegWidth} (dst : RegOrZr w) (a : AddrExpr) :
    ⦃ fun s g => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        (Mem.loadInt e.2.dmem e.1 2 = none → env.ok (.load .plain false e.1 2) g) ⊓
          (∀ (x : BitVec 16) g',
            (∃ v, Mem.loadInt e.2.dmem e.1 2 = some v ∧ x = BitVec.ofInt 16 v ∧ g' = g)
              ∨ (Mem.loadInt e.2.dmem e.1 2 = none ∧
                ∃ v, env.step (.load .plain false e.1 2) g v g' ∧ x = v.setWidth 16) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { e.2 with regs := e.2.regs.setRegOrZr dst (x.signExtend w.bits) } g') ⦄
      (⟨Directive.instr ⟨w, .LDRSH dst a⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    obtain ⟨hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
    simp only [AddrExpr.interpLoad]
    exact AddrExpr.checkSP_AllEnv' ha (MachineData.load_AllEnv' (w := .W16) hok fun x g' ho =>
      hk x g' ho _ hpl')

/-- `LDRSW Xt, [Xn|SP …]`, mapped or shared, as `ldrsb_env_spec`. -/
@[spec] theorem ldrsw_env_spec (dst : RegOrZr .W64) (a : AddrExpr) :
    ⦃ fun s g => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        (Mem.loadInt e.2.dmem e.1 4 = none → env.ok (.load .plain false e.1 4) g) ⊓
          (∀ (x : BitVec 32) g',
            (∃ v, Mem.loadInt e.2.dmem e.1 4 = some v ∧ x = BitVec.ofInt 32 v ∧ g' = g)
              ∨ (Mem.loadInt e.2.dmem e.1 4 = none ∧
                ∃ v, env.step (.load .plain false e.1 4) g v g' ∧ x = v.setWidth 32) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { e.2 with regs := e.2.regs.setRegOrZr dst (x.signExtend 64) } g') ⦄
      (⟨Directive.instr ⟨.W64, .LDRSW dst (.addr a)⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    obtain ⟨hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
    simp only [AddrOrLit.interpLoad, AddrExpr.interpLoad]
    exact AddrExpr.checkSP_AllEnv' ha (MachineData.load_AllEnv' (w := .W32) hok fun x g' ho =>
      hk x g' ho _ hpl')

/-- `LDURSB Rt, [Xn|SP, #simm9]`, mapped or shared: as `ldrsb_env_spec`, no
writeback. -/
@[spec] theorem ldursb_env_spec {w : RegWidth} (dst : RegOrZr w) (a : UnscaledAddrExpr) :
    ⦃ fun s g => a.base.SPAligned s ⊓ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        (Mem.loadInt s.dmem e 1 = none → env.ok (.load .plain false e 1) g) ⊓
          (∀ (x : BitVec 8) g',
            (∃ v, Mem.loadInt s.dmem e 1 = some v ∧ x = BitVec.ofInt 8 v ∧ g' = g)
              ∨ (Mem.loadInt s.dmem e 1 = none ∧
                ∃ v, env.step (.load .plain false e 1) g v g' ∧ x = v.setWidth 8) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with regs := s.regs.setRegOrZr dst (x.signExtend w.bits) } g') ⦄
      (⟨Directive.instr ⟨w, .LDURSB dst a⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    obtain ⟨hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
    simp only [UnscaledAddrExpr.interpLoad]
    exact UnscaledAddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv' (w := .W8) hok fun x g' ho =>
      hk x g' ho _ hpl')

/-- `LDURSH Rt, [Xn|SP, #simm9]`, mapped or shared, as `ldursb_env_spec`. -/
@[spec] theorem ldursh_env_spec {w : RegWidth} (dst : RegOrZr w) (a : UnscaledAddrExpr) :
    ⦃ fun s g => a.base.SPAligned s ⊓ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        (Mem.loadInt s.dmem e 2 = none → env.ok (.load .plain false e 2) g) ⊓
          (∀ (x : BitVec 16) g',
            (∃ v, Mem.loadInt s.dmem e 2 = some v ∧ x = BitVec.ofInt 16 v ∧ g' = g)
              ∨ (Mem.loadInt s.dmem e 2 = none ∧
                ∃ v, env.step (.load .plain false e 2) g v g' ∧ x = v.setWidth 16) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with regs := s.regs.setRegOrZr dst (x.signExtend w.bits) } g') ⦄
      (⟨Directive.instr ⟨w, .LDURSH dst a⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    obtain ⟨hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
    simp only [UnscaledAddrExpr.interpLoad]
    exact UnscaledAddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv' (w := .W16) hok fun x g' ho =>
      hk x g' ho _ hpl')

/-- `LDURSW Xt, [Xn|SP, #simm9]`, mapped or shared, as `ldursb_env_spec`. -/
@[spec] theorem ldursw_env_spec (dst : RegOrZr .W64) (a : UnscaledAddrExpr) :
    ⦃ fun s g => a.base.SPAligned s ⊓ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        (Mem.loadInt s.dmem e 4 = none → env.ok (.load .plain false e 4) g) ⊓
          (∀ (x : BitVec 32) g',
            (∃ v, Mem.loadInt s.dmem e 4 = some v ∧ x = BitVec.ofInt 32 v ∧ g' = g)
              ∨ (Mem.loadInt s.dmem e 4 = none ∧
                ∃ v, env.step (.load .plain false e 4) g v g' ∧ x = v.setWidth 32) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with regs := s.regs.setRegOrZr dst (x.signExtend 64) } g') ⦄
      (⟨Directive.instr ⟨.W64, .LDURSW dst a⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    obtain ⟨hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
    simp only [UnscaledAddrExpr.interpLoad]
    exact UnscaledAddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv' (w := .W32) hok fun x g' ho =>
      hk x g' ho _ hpl')

/-- `LDPSW Xt1, Xt2, [Xn|SP …]`, each slot mapped or shared: two 4-byte loads,
the lower address first, each from `dmem` or from the environment (the second
in the environment state the first left), both sign-extended; then the base
writeback. -/
@[spec] theorem ldpsw_env_spec (dst1 dst2 : RegOrZr .W64) (a : AddrExpr) :
    ⦃ fun s g => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let a₂ := e.1 + 4#64
        (Mem.loadInt e.2.dmem e.1 4 = none → env.ok (.load .plain false e.1 4) g) ⊓
          (∀ (x₁ : BitVec 32) g₁,
            (∃ v, Mem.loadInt e.2.dmem e.1 4 = some v ∧ x₁ = BitVec.ofInt 32 v ∧ g₁ = g)
              ∨ (Mem.loadInt e.2.dmem e.1 4 = none ∧
                ∃ v, env.step (.load .plain false e.1 4) g v g₁ ∧ x₁ = v.setWidth 32) →
            (Mem.loadInt e.2.dmem a₂ 4 = none → env.ok (.load .plain false a₂ 4) g₁) ⊓
              (∀ (x₂ : BitVec 32) g₂,
                (∃ v, Mem.loadInt e.2.dmem a₂ 4 = some v ∧ x₂ = BitVec.ofInt 32 v ∧ g₂ = g₁)
                  ∨ (Mem.loadInt e.2.dmem a₂ 4 = none ∧
                    ∃ v, env.step (.load .plain false a₂ 4) g₁ v g₂ ∧ x₂ = v.setWidth 32) →
                let r := (e.2.regs.setRegOrZr dst1 (x₁.signExtend 64)).setRegOrZr dst2 (x₂.signExtend 64)
                WP.wp (⟨p⟩ : EnvProgram env) Q E { e.2 with regs := r } g₂)) ⦄
      (⟨Directive.instr ⟨.W64, .LDPSW dst1 dst2 a⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    obtain ⟨hok₁, hk⟩ := h ⟨pc, pc + .ofNat z⟩
    refine AddrExpr.checkSP_AllEnv' ha (MachineData.load_AllEnv' (w := .W32) hok₁ fun x₁ g₁ ho₁ => ?_)
    obtain ⟨hok₂, hk⟩ := hk x₁ g₁ ho₁
    exact MachineData.load_AllEnv' (w := .W32) hok₂ fun x₂ g₂ ho₂ => hk x₂ g₂ ho₂ _ hpl'

/-- `LDRSW Xt, label`, mapped or shared: as `ldrsw_env_spec`, from the label's
address. -/
@[spec] theorem ldrsw_lit_env_spec (dst : RegOrZr .W64) (l : Label) :
    ⦃ fun s g =>
        let e := (@Labels.label (_root_.Executable.labels cenv) l).toBitVec
        (Mem.loadInt s.dmem e 4 = none → env.ok (.load .plain false e 4) g) ⊓
          (∀ (x : BitVec 32) g',
            (∃ v, Mem.loadInt s.dmem e 4 = some v ∧ x = BitVec.ofInt 32 v ∧ g' = g)
              ∨ (Mem.loadInt s.dmem e 4 = none ∧
                ∃ v, env.step (.load .plain false e 4) g v g' ∧ x = v.setWidth 32) →
            WP.wp (⟨p⟩ : EnvProgram env) Q E
              { s with regs := s.regs.setRegOrZr dst (x.signExtend 64) } g') ⦄
      (⟨Directive.instr ⟨.W64, .LDRSW dst (.lit (.addr ⟨l⟩))⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s g h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hok, hk⟩ := h
    show cenv.wpEnv env _ (Q ()) E s g
    env_step
    simp only [AddrOrLit.interpLoad, Literal.interpLoad, BitVec.ofInt_toInt_int64, Effects.AllEnv]
    exact MachineData.load_AllEnv' (w := .W32) hok fun x g' ho => hk x g' ho _ hpl'

/-- `LDRSW Xt, =expr` (`ldrsw_pool_env`): no memory access, any environment. -/
@[spec] theorem ldrsw_pool_env_spec (dst : RegOrZr .W64) (c : ConstExpr) :
    ⦃ fun s g => ∀ rng,
        let v := (BitVec.ofInt 32 (@ConstExpr.interp (_root_.Executable.labels cenv) c rng).toInt).signExtend 64
        WP.wp (⟨p⟩ : EnvProgram env) Q E { s with regs := s.regs.setRegOrZr dst v } g ⦄
      (⟨Directive.instr ⟨.W64, .LDRSW dst (.lit (.pool ⟨c⟩))⟩ :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  TripleEnv.triple (fun _ _ h => h) (ldrsw_pool_env env dst c)

end MachineWP
