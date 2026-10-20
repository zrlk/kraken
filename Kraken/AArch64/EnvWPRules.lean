/-
The shared-location rules of the AArch64 environment-aware wp. Copied from
x64's `Kraken/EnvWPRules.lean`, adapted to the AArch64 instructions of
`Kraken.AArch64.WP.Rules` and `Kraken.AArch64.WP.RulesAtomic`. Design note:
`Kraken/Promising/EnvWP.md` §7.

Where a `MachineWP` rule asks for the bytes to be mapped (`isSome`), the
shared rule asks for them to be outside `dmem` (`Mem.loadInt s.dmem a n =
none`), for the access to be permitted (`env.ok`), and for the tail's wp at
every outcome the environment allows (`env.step`), exactly as
`Effects.AllEnv` consults the environment. The `SP` alignment side condition
is the mapped rule's. Each rule unfolds one cell, like the `MachineWP` rules.

The rules are `TripleEnv` theorems, not `@[spec]` triples, as on x64
(`EnvWP.md` §8). A program mixing private and shared accesses composes
them with `Executable.wpEnv_cons`: the shared accesses by these rules and the
rest by `MachineWP.wpEnv_of_triple` of a `vcgen` triple
(`Kraken/AArch64/Examples/AtomicsLink.lean`, `cas_correctEnv`).

No rule splits on the environment's answers: a load's value, a
store-exclusive's success and an `rmw`'s old value are whatever `env.step`
allows, so the store-exclusive rule covers success and failure at once (the
status register gets `0` or `1` from the `Bool` the environment returns; in
`lastWrite` a failure leaves the location unchanged) and the `CAS` rule
covers a match and a mismatch (the old value lands in `Rs` either way; the
operation `rmwOpBits sz.bits (compare-and-swap)` tells the environment
whether anything is written).

| Instruction | Rule | Access |
|---|---|---|
| `LDR Rt, [Xn\|SP …]` (X, W) | `ldr_shared` | `load .plain` of 8 / 4 |
| `STR Rt, [Xn\|SP …]` (X, W) | `str_shared` | `store .plain` of 8 / 4 |
| `LDRB`/`LDRH`, `STRB`/`STRH` | `ldrb_shared`, `ldrh_shared`, `strb_shared`, `strh_shared` | `load`/`store .plain` of 1 / 2 |
| `LDP`/`STP Rt1, Rt2, [Xn\|SP …]` (X, W), both slots shared | `ldp_shared`, `stp_shared` | two plain accesses, lower address first |
| `LDUR`/`STUR Rt, [Xn\|SP, #simm9]` (X, W); `LDURB`/`LDURH`, `STURB`/`STURH` | `ldur_shared`, `stur_shared`; `ldurb_shared`, `ldurh_shared`, `sturb_shared`, `sturh_shared` | `load`/`store .plain` of 8 / 4; 1 / 2 |
| `LDR Rt, label` (X, W) | `ldr_lit_shared` | `load .plain` of 8 / 4 at the label's address |
| `LDR Rt, =expr` | `ldr_pool_env` | none (the constant is the value) |
| `LDRSB`/`LDRSH Rt, [Xn\|SP …]` (X, W), `LDRSW Xt, [Xn\|SP …]` | `ldrsb_shared`, `ldrsh_shared`, `ldrsw_shared` | `load .plain` of 1 / 2 / 4, sign-extended |
| `LDURSB`/`LDURSH Rt, [Xn\|SP, #simm9]` (X, W), `LDURSW Xt, …` | `ldursb_shared`, `ldursh_shared`, `ldursw_shared` | `load .plain` of 1 / 2 / 4, sign-extended |
| `LDRSW Xt, label`; `LDRSW Xt, =expr` | `ldrsw_lit_shared`; `ldrsw_pool_env` | `load .plain` of 4; none |
| `LDPSW Xt1, Xt2, [Xn\|SP …]`, both slots shared | `ldpsw_shared` | two plain loads of 4, lower address first |
| `LDAR`, `LDAPR`, `LDXR`, `LDAXR` (+`B`/`H`) | `ldar_shared` | `load k xcl` |
| `STLR` (+`B`/`H`) | `stlr_shared` | `store .rel false` |
| `STXR`, `STLXR` (+`B`/`H`) | `stxr_shared` (success and failure) | `store k true` |
| `CAS`, `CASA`, `CASL`, `CASAL` (+`B`/`H`) | `cas_shared` | `rmw k` (writes only on a match) |
| `CASP`, `CASPA`, `CASPL`, `CASPAL` (X, W), both halves shared | `casp_shared`; in `lastWrite`: `casp_lastWrite` | `SharedEnv.CaspEnv`: one `rmw k` per half, either order |
| `SWP`, `SWPA`, `SWPL`, `SWPAL` (+`B`/`H`) | `swp_shared` | `rmw k` |
| `LD<op>` (+`A`/`L`/`AL`, +`B`/`H`), `ST<op>` | `ldop_shared` | `rmw k` |
| `DMB`, `DSB`, `ISB` | `dmb_shared`, `dsb_shared`, `isb_shared`; with `FencesSkip`: `dmb_skip`, `dsb_skip`, `isb_skip` | `fence k` (`DSB ST` is `.stAll`; `ISB` is `.isb`) |

The `LDR`/`STR` rules take any `AddrExpr`, so they cover the pre- and
post-indexed forms (`[Xn, #imm]!`, `[Xn], #imm`: `AddrExpr.eval` writes the base
back) and the register-offset form as well as the plain offset.

Out of scope: `LDXP`/`STXP` (deferred with LL/SC), the
FEAT_LSE2 16-byte `LDP`/`STP` (`isaLSE2` only; its rules `ldp_lse2_shared`/
`stp_lse2_shared` are over `TripleEnvLSE2` in `Kraken/AArch64/EnvLSE2.lean`,
`EnvWP.md` "Pair effects"), `CASP` with one half private and one shared (the
mixed case is a single `rmw` on the shared half, which `AllEnv` covers but no
rule states), and mixed `LDP`/`STP` with one slot private and one
shared (`LDPSW` has a combined rule, `ldpsw_env_spec` in
`Kraken/AArch64/EnvVCGen.lean`, that covers that mix). The sign-extending
loads have mapped rules in `Kraken.AArch64.WP.RulesSignExt`.
-/
import Kraken.AArch64.EnvWP
import Kraken.AArch64.WP.RulesSignExt

open Kraken

-- `UnscaledAddrExpr.eval_eq` (the base plus the offset of `[Xn|SP, #simm9]`)
-- lives in `Kraken.AArch64.WP.RulesSignExt`, so that the mapped rules have it.

/-! ## The primitives off `dmem` -/

section Prims

variable {env : SharedEnv} {g : env.State} {P : MachineState → env.State → Prop}

private theorem AddrExpr.checkSP_AllEnv {a : AddrExpr} {s : MachineData} {ok : Unit → Effects}
    (ha : a.SPAligned s) (hk : (ok ()).AllEnv env g P) : (a.checkSPAlignment s ok).AllEnv env g P := by
  obtain ⟨⟨b, w⟩, off⟩ := a
  cases b with
  | reg r => exact hk
  | SP =>
    have h := ha rfl
    simp only [AddrExpr.checkSPAlignment, Reg64s.getRegOrSp_SP, h, bne_self_eq_false,
      Bool.false_eq_true, ite_false]
    exact hk

/-- `UnscaledAddrExpr.checkSPAlignment` passes on an aligned base. Public: the
combined rules of `Kraken/AArch64/EnvVCGen.lean` use it too. -/
theorem UnscaledAddrExpr.checkSP_AllEnv {a : UnscaledAddrExpr} {s : MachineData}
    {ok : Unit → Effects} (ha : a.base.SPAligned s) (hk : (ok ()).AllEnv env g P) :
    (a.checkSPAlignment s ok).AllEnv env g P := by
  obtain ⟨⟨b, w⟩, off⟩ := a
  cases b with
  | reg r => exact hk
  | SP =>
    have h := ha rfl
    simp only [UnscaledAddrExpr.checkSPAlignment, Reg64s.getRegOrSp_SP, h, bne_self_eq_false,
      Bool.false_eq_true, ite_false]
    exact hk

private theorem RegOrSp.interpBase_AllEnv {b : RegOrSp .W64} {s : MachineData}
    {ok : BitVec 64 → Effects} (ha : b.SPAligned s) (hk : (ok (s.regs.getRegOrSp b)).AllEnv env g P) :
    (b.interpBase s ok).AllEnv env g P := by
  obtain ⟨b, w⟩ := b
  cases b with
  | reg r => exact hk
  | SP =>
    have h := ha rfl
    simp only [RegOrSp.interpBase, Reg64s.getRegOrSp_SP, h, bne_self_eq_false,
      Bool.false_eq_true, ite_false]
    simpa using hk

private theorem MachineData.load_AllEnv {s : MachineData} {addr : BitVec 64} {w : MemWidth}
    {ret : w.type → MachineData → Effects} (hv : Mem.loadInt s.dmem addr w.bytes = none)
    (hok : env.ok (.load .plain false addr w.bytes) g)
    (hk : ∀ v g', env.step (.load .plain false addr w.bytes) g v g' → (ret (v.setWidth w.bits) s).AllEnv env g' P) :
    (s.load addr w ret).AllEnv env g P := by
  simp only [MachineData.load, Effects.AllEnv, hv]
  exact ⟨hok, hk⟩

private theorem MachineData.store_AllEnv {s : MachineData} {addr : BitVec 64} {w : MemWidth}
    {val : w.type} {ret : MachineData → Effects} (hv : Mem.loadInt s.dmem addr w.bytes = none)
    (hok : env.ok (.store .plain false addr w.bytes (val.setWidth 128)) g)
    (hk : ∀ b g', env.step (.store .plain false addr w.bytes (val.setWidth 128)) g b g' → (ret s).AllEnv env g' P) :
    (s.store addr val ret).AllEnv env g P := by
  simp only [MachineData.store, Effects.AllEnv, hv]
  exact ⟨hok, hk⟩

private theorem MachineData.loadK_AllEnv {s : MachineData} {k : LoadKind} {xcl : Bool}
    {addr : BitVec 64} {w : MemWidth} {ret : w.type → MachineData → Effects}
    (hv : Mem.loadInt s.dmem addr w.bytes = none) (hok : env.ok (.load k xcl addr w.bytes) g)
    (hk : ∀ v g', env.step (.load k xcl addr w.bytes) g v g' → (ret (v.setWidth w.bits) s).AllEnv env g' P) :
    (s.loadK k xcl addr w ret).AllEnv env g P := by
  simp only [MachineData.loadK, Effects.AllEnv, hv]
  exact ⟨hok, hk⟩

private theorem MachineData.storeK_AllEnv {s : MachineData} {k : StoreKind} {xcl : Bool}
    {addr : BitVec 64} {w : MemWidth} {val : w.type} {ret : Bool → MachineData → Effects}
    (hv : Mem.loadInt s.dmem addr w.bytes = none)
    (hok : env.ok (.store k xcl addr w.bytes (val.setWidth 128)) g)
    (hk : ∀ b g', env.step (.store k xcl addr w.bytes (val.setWidth 128)) g b g' → (ret b s).AllEnv env g' P) :
    (s.storeK k xcl addr val ret).AllEnv env g P := by
  simp only [MachineData.storeK, Effects.AllEnv, hv]
  exact ⟨hok, hk⟩

private theorem MachineData.rmwK_AllEnv {s : MachineData} {k : RmwKind} {noRet : Bool}
    {addr : BitVec 64} {w : MemWidth} {op : w.type → Option w.type}
    {ret : w.type → MachineData → Effects} (hv : Mem.loadInt s.dmem addr w.bytes = none)
    (hok : env.ok (.rmw k addr w.bytes (rmwOpBits w.bits op)) g)
    (hk : ∀ old g', env.step (.rmw k addr w.bytes (rmwOpBits w.bits op)) g old g' →
      (ret (old.setWidth w.bits) s).AllEnv env g' P) :
    (s.rmwK k noRet addr w op ret).AllEnv env g P := by
  simp only [MachineData.rmwK, Effects.AllEnv, hv]
  exact ⟨hok, hk⟩

/-- `CASP` with both halves outside `dmem`: the environment's `CaspEnv`
reading (two per-half `rmw`s, either order). -/
private theorem MachineData.rmwPairK_AllEnv {s : MachineData} {k : RmwKind} {addr : BitVec 64}
    {w : MemWidth} {cmp1 cmp2 new1 new2 : w.type} {ret : w.type → w.type → MachineData → Effects}
    (hv₁ : Mem.loadInt s.dmem addr w.bytes = none) (hv₂ : Mem.loadInt s.dmem (addr + w.bytesv) w.bytes = none)
    (hk : env.CaspEnv k addr w cmp1 cmp2 new1 new2 g fun o₁ o₂ g' => (ret o₁ o₂ s).AllEnv env g' P) :
    (s.rmwPairK k addr cmp1 cmp2 new1 new2 ret).AllEnv env g P := by
  simp only [MachineData.rmwPairK, Effects.AllEnv, hv₁, hv₂]
  exact hk

end Prims

namespace MachineWP

/-- Unfold the fall-through address past one instruction cell. -/
private theorem after_instr [CodeEnv] {i : Instr} {q : Program} {pc : Int64} {z : Nat}
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
    rw [after_instr hseg]
    refine step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl ?_⟩
    simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setRegOrZr,
      BitVec.take_eq_setWidth]))

variable [CodeEnv] (env : SharedEnv) {p : Program} {Q : MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop}

/-! ## Plain loads and stores (the addressing forms of `WP.Rules`) -/

/-- `LDR Rt, [Xn|SP …]` on a location outside `dmem`: a plain load of the
register's width; the tail runs, after the base writeback, from every value
and environment state the environment allows. -/
theorem ldr_shared {w : RegWidth} (dst : RegOrZr w) (a : AddrExpr) :
    TripleEnv env
      (fun s g => a.SPAligned s ∧ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        Mem.loadInt e.2.dmem e.1 w.bytes = none ∧ env.ok (.load .plain false e.1 w.bytes) g ∧
          ∀ v g', env.step (.load .plain false e.1 w.bytes) g v g' →
            cenv.wpEnv env p Q E { e.2 with regs := e.2.regs.setRegOrZr dst (v.setWidth w.bits) } g')
      (Directive.instr ⟨w, .LDR dst (.addr a)⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [AddrOrLit.interpLoad, AddrExpr.interpLoad]
  exact AddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv hnone hok fun v g' hs => hk v g' hs _ hpl')

/-- `STR Rt, [Xn|SP …]` on a location outside `dmem`: a plain store of the
register; the tail runs, after the base writeback, in every environment state
the store may leave. -/
theorem str_shared {w : RegWidth} (src : RegOrZr w) (a : AddrExpr) :
    TripleEnv env
      (fun s g => a.SPAligned s ∧ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let v := (s.regs.getRegOrZr src).setWidth 128
        Mem.loadInt e.2.dmem e.1 w.bytes = none ∧ env.ok (.store .plain false e.1 w.bytes v) g ∧
          ∀ ok g', env.step (.store .plain false e.1 w.bytes v) g ok g' → cenv.wpEnv env p Q E e.2 g')
      (Directive.instr ⟨w, .STR src a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [AddrExpr.interpStore]
  exact AddrExpr.checkSP_AllEnv ha (MachineData.store_AllEnv hnone hok fun b g' hs => hk b g' hs _ hpl')

/-- `LDRB Wt, [Xn|SP …]` on a location outside `dmem`: a plain 1-byte load,
zero-extended. -/
theorem ldrb_shared (dst : RegOrZr .W32) (a : AddrExpr) :
    TripleEnv env
      (fun s g => a.SPAligned s ∧ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        Mem.loadInt e.2.dmem e.1 1 = none ∧ env.ok (.load .plain false e.1 1) g ∧
          ∀ v g', env.step (.load .plain false e.1 1) g v g' →
            cenv.wpEnv env p Q E
              { e.2 with regs := e.2.regs.setRegOrZr dst ((v.setWidth 8).setWidth 32) } g')
      (Directive.instr ⟨.W32, .LDRB dst a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [AddrExpr.interpLoad]
  exact AddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv (w := .W8) hnone hok fun v g' hs =>
    hk v g' hs _ hpl')

/-- `LDRH Wt, [Xn|SP …]` on a location outside `dmem`: a plain 2-byte load,
zero-extended. -/
theorem ldrh_shared (dst : RegOrZr .W32) (a : AddrExpr) :
    TripleEnv env
      (fun s g => a.SPAligned s ∧ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        Mem.loadInt e.2.dmem e.1 2 = none ∧ env.ok (.load .plain false e.1 2) g ∧
          ∀ v g', env.step (.load .plain false e.1 2) g v g' →
            cenv.wpEnv env p Q E
              { e.2 with regs := e.2.regs.setRegOrZr dst ((v.setWidth 16).setWidth 32) } g')
      (Directive.instr ⟨.W32, .LDRH dst a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [AddrExpr.interpLoad]
  exact AddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv (w := .W16) hnone hok fun v g' hs =>
    hk v g' hs _ hpl')

/-- `STRB Wt, [Xn|SP …]` on a location outside `dmem`: a plain 1-byte store of
the low byte. -/
theorem strb_shared (src : RegOrZr .W32) (a : AddrExpr) :
    TripleEnv env
      (fun s g => a.SPAligned s ∧ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let v := ((s.regs.getRegOrZr src).setWidth 8).setWidth 128
        Mem.loadInt e.2.dmem e.1 1 = none ∧ env.ok (.store .plain false e.1 1 v) g ∧
          ∀ ok g', env.step (.store .plain false e.1 1 v) g ok g' → cenv.wpEnv env p Q E e.2 g')
      (Directive.instr ⟨.W32, .STRB src a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [AddrExpr.interpStore]
  exact AddrExpr.checkSP_AllEnv ha (MachineData.store_AllEnv (w := .W8) hnone hok fun b g' hs =>
    hk b g' hs _ hpl')

/-- `STRH Wt, [Xn|SP …]` on a location outside `dmem`: a plain 2-byte store of
the low halfword. -/
theorem strh_shared (src : RegOrZr .W32) (a : AddrExpr) :
    TripleEnv env
      (fun s g => a.SPAligned s ∧ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let v := ((s.regs.getRegOrZr src).setWidth 16).setWidth 128
        Mem.loadInt e.2.dmem e.1 2 = none ∧ env.ok (.store .plain false e.1 2 v) g ∧
          ∀ ok g', env.step (.store .plain false e.1 2 v) g ok g' → cenv.wpEnv env p Q E e.2 g')
      (Directive.instr ⟨.W32, .STRH src a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [AddrExpr.interpStore]
  exact AddrExpr.checkSP_AllEnv ha (MachineData.store_AllEnv (w := .W16) hnone hok fun b g' hs =>
    hk b g' hs _ hpl')

/-- `LDP Rt1, Rt2, [Xn|SP …]` with both slots outside `dmem`: two plain loads
of the register's width, the lower address first (the order the sequential
semantics fixes); the tail runs from every pair of values and environment
state the environment allows. -/
theorem ldp_shared {w : RegWidth} (dst1 dst2 : RegOrZr w) (a : AddrExpr) :
    TripleEnv env
      (fun s g => a.SPAligned s ∧ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let a₂ := e.1 + BitVec.ofNat 64 w.bytes
        Mem.loadInt e.2.dmem e.1 w.bytes = none ∧ Mem.loadInt e.2.dmem a₂ w.bytes = none ∧
          env.ok (.load .plain false e.1 w.bytes) g ∧
          ∀ v₁ g₁, env.step (.load .plain false e.1 w.bytes) g v₁ g₁ →
            env.ok (.load .plain false a₂ w.bytes) g₁ ∧
            ∀ v₂ g₂, env.step (.load .plain false a₂ w.bytes) g₁ v₂ g₂ →
              let r := (e.2.regs.setRegOrZr dst1 (v₁.setWidth w.bits)).setRegOrZr dst2 (v₂.setWidth w.bits)
              cenv.wpEnv env p Q E { e.2 with regs := r } g₂)
      (Directive.instr ⟨w, .LDP dst1 dst2 a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hn₁, hn₂, hok₁, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  refine AddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv hn₁ hok₁ fun v₁ g₁ hs₁ => ?_)
  obtain ⟨hok₂, hk⟩ := hk v₁ g₁ hs₁
  exact MachineData.load_AllEnv hn₂ hok₂ fun v₂ g₂ hs₂ => hk v₂ g₂ hs₂ _ hpl'

/-- `STP Rt1, Rt2, [Xn|SP …]` with both slots outside `dmem`: two plain stores
of the register's width, the lower address first. -/
theorem stp_shared {w : RegWidth} (src1 src2 : RegOrZr w) (a : AddrExpr) :
    TripleEnv env
      (fun s g => a.SPAligned s ∧ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let a₂ := e.1 + BitVec.ofNat 64 w.bytes
        let v₁ := (s.regs.getRegOrZr src1).setWidth 128
        let v₂ := (s.regs.getRegOrZr src2).setWidth 128
        Mem.loadInt e.2.dmem e.1 w.bytes = none ∧ Mem.loadInt e.2.dmem a₂ w.bytes = none ∧
          env.ok (.store .plain false e.1 w.bytes v₁) g ∧
          ∀ b₁ g₁, env.step (.store .plain false e.1 w.bytes v₁) g b₁ g₁ →
            env.ok (.store .plain false a₂ w.bytes v₂) g₁ ∧
            ∀ b₂ g₂, env.step (.store .plain false a₂ w.bytes v₂) g₁ b₂ g₂ → cenv.wpEnv env p Q E e.2 g₂)
      (Directive.instr ⟨w, .STP src1 src2 a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hn₁, hn₂, hok₁, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  refine AddrExpr.checkSP_AllEnv ha (MachineData.store_AllEnv hn₁ hok₁ fun b₁ g₁ hs₁ => ?_)
  obtain ⟨hok₂, hk⟩ := hk b₁ g₁ hs₁
  exact MachineData.store_AllEnv hn₂ hok₂ fun b₂ g₂ hs₂ => hk b₂ g₂ hs₂ _ hpl'

/-! ## The unscaled forms (`LDUR`/`STUR` and their narrow kin)

`[Xn|SP, #simm9]`, never written back (`UnscaledAddrExpr.eval_eq`); the `SP`
alignment side condition is the base register's (`RegOrSp.SPAligned`).
`MachineWP` has no rule for these (`WP.Rules` covers the scaled forms only), so in
`vcgen` they are served by the combined rules of
`Kraken/AArch64/EnvVCGen.lean` (`ldur_env_spec`, `stur_env_spec`). -/

/-- `LDUR Rt, [Xn|SP, #simm9]` on a location outside `dmem`: a plain load of
the register's width. -/
theorem ldur_shared {w : RegWidth} (dst : RegOrZr w) (a : UnscaledAddrExpr) :
    TripleEnv env
      (fun s g => a.base.SPAligned s ∧ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        Mem.loadInt s.dmem e w.bytes = none ∧ env.ok (.load .plain false e w.bytes) g ∧
          ∀ v g', env.step (.load .plain false e w.bytes) g v g' →
            cenv.wpEnv env p Q E { s with regs := s.regs.setRegOrZr dst (v.setWidth w.bits) } g')
      (Directive.instr ⟨w, .LDUR dst a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [UnscaledAddrExpr.interpLoad]
  exact UnscaledAddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv hnone hok fun v g' hs => hk v g' hs _ hpl')

/-- `STUR Rt, [Xn|SP, #simm9]` on a location outside `dmem`: a plain store of
the register. -/
theorem stur_shared {w : RegWidth} (src : RegOrZr w) (a : UnscaledAddrExpr) :
    TripleEnv env
      (fun s g => a.base.SPAligned s ∧ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let v := (s.regs.getRegOrZr src).setWidth 128
        Mem.loadInt s.dmem e w.bytes = none ∧ env.ok (.store .plain false e w.bytes v) g ∧
          ∀ ok g', env.step (.store .plain false e w.bytes v) g ok g' → cenv.wpEnv env p Q E s g')
      (Directive.instr ⟨w, .STUR src a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [UnscaledAddrExpr.interpStore]
  exact UnscaledAddrExpr.checkSP_AllEnv ha (MachineData.store_AllEnv hnone hok fun b g' hs => hk b g' hs _ hpl')

/-- `LDURB Wt, [Xn|SP, #simm9]` on a location outside `dmem`: a plain 1-byte
load, zero-extended. -/
theorem ldurb_shared (dst : RegOrZr .W32) (a : UnscaledAddrExpr) :
    TripleEnv env
      (fun s g => a.base.SPAligned s ∧ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        Mem.loadInt s.dmem e 1 = none ∧ env.ok (.load .plain false e 1) g ∧
          ∀ v g', env.step (.load .plain false e 1) g v g' →
            cenv.wpEnv env p Q E
              { s with regs := s.regs.setRegOrZr dst ((v.setWidth 8).setWidth 32) } g')
      (Directive.instr ⟨.W32, .LDURB dst a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [UnscaledAddrExpr.interpLoad]
  exact UnscaledAddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv (w := .W8) hnone hok fun v g' hs =>
    hk v g' hs _ hpl')

/-- `LDURH Wt, [Xn|SP, #simm9]` on a location outside `dmem`: a plain 2-byte
load, zero-extended. -/
theorem ldurh_shared (dst : RegOrZr .W32) (a : UnscaledAddrExpr) :
    TripleEnv env
      (fun s g => a.base.SPAligned s ∧ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        Mem.loadInt s.dmem e 2 = none ∧ env.ok (.load .plain false e 2) g ∧
          ∀ v g', env.step (.load .plain false e 2) g v g' →
            cenv.wpEnv env p Q E
              { s with regs := s.regs.setRegOrZr dst ((v.setWidth 16).setWidth 32) } g')
      (Directive.instr ⟨.W32, .LDURH dst a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [UnscaledAddrExpr.interpLoad]
  exact UnscaledAddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv (w := .W16) hnone hok fun v g' hs =>
    hk v g' hs _ hpl')

/-- `STURB Wt, [Xn|SP, #simm9]` on a location outside `dmem`: a plain 1-byte
store of the low byte. -/
theorem sturb_shared (src : RegOrZr .W32) (a : UnscaledAddrExpr) :
    TripleEnv env
      (fun s g => a.base.SPAligned s ∧ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let v := ((s.regs.getRegOrZr src).setWidth 8).setWidth 128
        Mem.loadInt s.dmem e 1 = none ∧ env.ok (.store .plain false e 1 v) g ∧
          ∀ ok g', env.step (.store .plain false e 1 v) g ok g' → cenv.wpEnv env p Q E s g')
      (Directive.instr ⟨.W32, .STURB src a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [UnscaledAddrExpr.interpStore]
  exact UnscaledAddrExpr.checkSP_AllEnv ha (MachineData.store_AllEnv (w := .W8) hnone hok fun b g' hs =>
    hk b g' hs _ hpl')

/-- `STURH Wt, [Xn|SP, #simm9]` on a location outside `dmem`: a plain 2-byte
store of the low halfword. -/
theorem sturh_shared (src : RegOrZr .W32) (a : UnscaledAddrExpr) :
    TripleEnv env
      (fun s g => a.base.SPAligned s ∧ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let v := ((s.regs.getRegOrZr src).setWidth 16).setWidth 128
        Mem.loadInt s.dmem e 2 = none ∧ env.ok (.store .plain false e 2 v) g ∧
          ∀ ok g', env.step (.store .plain false e 2 v) g ok g' → cenv.wpEnv env p Q E s g')
      (Directive.instr ⟨.W32, .STURH src a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [UnscaledAddrExpr.interpStore]
  exact UnscaledAddrExpr.checkSP_AllEnv ha (MachineData.store_AllEnv (w := .W16) hnone hok fun b g' hs =>
    hk b g' hs _ hpl')

/-! ## PC-relative literal loads

`LDR Rt, label` (`Literal.addr`) is a plain load from the label's address,
through `dmem` like any other load: nothing makes a label's bytes private, so
it gets the shared rule like `LDR Rt, [Xn …]` (the address is the label's
value, no base register, no `SP` check). `LDR Rt, =expr` (`Literal.pool`)
accesses no memory in Kraken's semantics (the assembler's pool constant is the
value itself), so it is never a shared access: its rule asks nothing of the
environment and holds in every environment. -/

/-- `LDR Rt, label` on a location outside `dmem`: a plain load of the
register's width from the label's address. -/
theorem ldr_lit_shared {w : RegWidth} (dst : RegOrZr w) (l : Label) :
    TripleEnv env
      (fun s g =>
        let e := (@Labels.label (_root_.Executable.labels cenv) l).toBitVec
        Mem.loadInt s.dmem e w.bytes = none ∧ env.ok (.load .plain false e w.bytes) g ∧
          ∀ v g', env.step (.load .plain false e w.bytes) g v g' →
            cenv.wpEnv env p Q E { s with regs := s.regs.setRegOrZr dst (v.setWidth w.bits) } g')
      (Directive.instr ⟨w, .LDR dst (.lit (.addr ⟨l⟩))⟩ :: p) Q E := by
  intro s g ⟨hnone, hok, hk⟩
  env_step
  simp only [AddrOrLit.interpLoad, Literal.interpLoad, BitVec.ofInt_toInt_int64, Effects.AllEnv]
  exact MachineData.load_AllEnv hnone hok fun v g' hs => hk v g' hs _ hpl'

/-- `LDR Rt, =expr`: no memory access; `Rt` gets the constant (truncated to the
register's width), in any environment, the environment state unchanged. -/
theorem ldr_pool_env {w : RegWidth} (dst : RegOrZr w) (c : ConstExpr) :
    TripleEnv env
      (fun s g => ∀ rng,
        let v := BitVec.ofInt w.bits (@ConstExpr.interp (_root_.Executable.labels cenv) c rng).toInt
        cenv.wpEnv env p Q E { s with regs := s.regs.setRegOrZr dst v } g)
      (Directive.instr ⟨w, .LDR dst (.lit (.pool ⟨c⟩))⟩ :: p) Q E := by
  intro s g h
  env_step
  have hk := h ⟨pc, pc + .ofNat z⟩
  simp only [AddrOrLit.interpLoad, Literal.interpLoad, Effects.AllEnv]
  exact hk _ hpl'

/-! ## Sign-extending loads

`LDRSB`/`LDRSH`/`LDRSW`, their unscaled forms and `LDPSW`: a plain load of the
field's width, as `LDRB`/`LDRH`/`LDR`, the value sign-extended to the
register (`Kraken.AArch64.WP.RulesSignExt` has the mapped rules). -/

/-- `LDRSB Rt, [Xn|SP …]` on a location outside `dmem`: a plain 1-byte load,
sign-extended. -/
theorem ldrsb_shared {w : RegWidth} (dst : RegOrZr w) (a : AddrExpr) :
    TripleEnv env
      (fun s g => a.SPAligned s ∧ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        Mem.loadInt e.2.dmem e.1 1 = none ∧ env.ok (.load .plain false e.1 1) g ∧
          ∀ v g', env.step (.load .plain false e.1 1) g v g' →
            cenv.wpEnv env p Q E
              { e.2 with regs := e.2.regs.setRegOrZr dst ((v.setWidth 8).signExtend w.bits) } g')
      (Directive.instr ⟨w, .LDRSB dst a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [AddrExpr.interpLoad]
  exact AddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv (w := .W8) hnone hok fun v g' hs =>
    hk v g' hs _ hpl')

/-- `LDRSH Rt, [Xn|SP …]` on a location outside `dmem`: a plain 2-byte load,
sign-extended. -/
theorem ldrsh_shared {w : RegWidth} (dst : RegOrZr w) (a : AddrExpr) :
    TripleEnv env
      (fun s g => a.SPAligned s ∧ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        Mem.loadInt e.2.dmem e.1 2 = none ∧ env.ok (.load .plain false e.1 2) g ∧
          ∀ v g', env.step (.load .plain false e.1 2) g v g' →
            cenv.wpEnv env p Q E
              { e.2 with regs := e.2.regs.setRegOrZr dst ((v.setWidth 16).signExtend w.bits) } g')
      (Directive.instr ⟨w, .LDRSH dst a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [AddrExpr.interpLoad]
  exact AddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv (w := .W16) hnone hok fun v g' hs =>
    hk v g' hs _ hpl')

/-- `LDRSW Xt, [Xn|SP …]` on a location outside `dmem`: a plain 4-byte load,
sign-extended. -/
theorem ldrsw_shared (dst : RegOrZr .W64) (a : AddrExpr) :
    TripleEnv env
      (fun s g => a.SPAligned s ∧ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        Mem.loadInt e.2.dmem e.1 4 = none ∧ env.ok (.load .plain false e.1 4) g ∧
          ∀ v g', env.step (.load .plain false e.1 4) g v g' →
            cenv.wpEnv env p Q E
              { e.2 with regs := e.2.regs.setRegOrZr dst ((v.setWidth 32).signExtend 64) } g')
      (Directive.instr ⟨.W64, .LDRSW dst (.addr a)⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [AddrOrLit.interpLoad, AddrExpr.interpLoad]
  exact AddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv (w := .W32) hnone hok fun v g' hs =>
    hk v g' hs _ hpl')

/-- `LDPSW Xt1, Xt2, [Xn|SP …]` with both slots outside `dmem`: two plain
4-byte loads, the lower address first, each sign-extended. -/
theorem ldpsw_shared (dst1 dst2 : RegOrZr .W64) (a : AddrExpr) :
    TripleEnv env
      (fun s g => a.SPAligned s ∧ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let a₂ := e.1 + 4#64
        Mem.loadInt e.2.dmem e.1 4 = none ∧ Mem.loadInt e.2.dmem a₂ 4 = none ∧
          env.ok (.load .plain false e.1 4) g ∧
          ∀ v₁ g₁, env.step (.load .plain false e.1 4) g v₁ g₁ →
            env.ok (.load .plain false a₂ 4) g₁ ∧
            ∀ v₂ g₂, env.step (.load .plain false a₂ 4) g₁ v₂ g₂ →
              let r := (e.2.regs.setRegOrZr dst1 ((v₁.setWidth 32).signExtend 64)).setRegOrZr dst2
                ((v₂.setWidth 32).signExtend 64)
              cenv.wpEnv env p Q E { e.2 with regs := r } g₂)
      (Directive.instr ⟨.W64, .LDPSW dst1 dst2 a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hn₁, hn₂, hok₁, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  refine AddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv (w := .W32) hn₁ hok₁ fun v₁ g₁ hs₁ => ?_)
  obtain ⟨hok₂, hk⟩ := hk v₁ g₁ hs₁
  exact MachineData.load_AllEnv (w := .W32) hn₂ hok₂ fun v₂ g₂ hs₂ => hk v₂ g₂ hs₂ _ hpl'

/-- `LDURSB Rt, [Xn|SP, #simm9]` on a location outside `dmem`: a plain 1-byte
load, sign-extended. -/
theorem ldursb_shared {w : RegWidth} (dst : RegOrZr w) (a : UnscaledAddrExpr) :
    TripleEnv env
      (fun s g => a.base.SPAligned s ∧ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        Mem.loadInt s.dmem e 1 = none ∧ env.ok (.load .plain false e 1) g ∧
          ∀ v g', env.step (.load .plain false e 1) g v g' →
            cenv.wpEnv env p Q E
              { s with regs := s.regs.setRegOrZr dst ((v.setWidth 8).signExtend w.bits) } g')
      (Directive.instr ⟨w, .LDURSB dst a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [UnscaledAddrExpr.interpLoad]
  exact UnscaledAddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv (w := .W8) hnone hok fun v g' hs =>
    hk v g' hs _ hpl')

/-- `LDURSH Rt, [Xn|SP, #simm9]` on a location outside `dmem`: a plain 2-byte
load, sign-extended. -/
theorem ldursh_shared {w : RegWidth} (dst : RegOrZr w) (a : UnscaledAddrExpr) :
    TripleEnv env
      (fun s g => a.base.SPAligned s ∧ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        Mem.loadInt s.dmem e 2 = none ∧ env.ok (.load .plain false e 2) g ∧
          ∀ v g', env.step (.load .plain false e 2) g v g' →
            cenv.wpEnv env p Q E
              { s with regs := s.regs.setRegOrZr dst ((v.setWidth 16).signExtend w.bits) } g')
      (Directive.instr ⟨w, .LDURSH dst a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [UnscaledAddrExpr.interpLoad]
  exact UnscaledAddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv (w := .W16) hnone hok fun v g' hs =>
    hk v g' hs _ hpl')

/-- `LDURSW Xt, [Xn|SP, #simm9]` on a location outside `dmem`: a plain 4-byte
load, sign-extended. -/
theorem ldursw_shared (dst : RegOrZr .W64) (a : UnscaledAddrExpr) :
    TripleEnv env
      (fun s g => a.base.SPAligned s ∧ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        Mem.loadInt s.dmem e 4 = none ∧ env.ok (.load .plain false e 4) g ∧
          ∀ v g', env.step (.load .plain false e 4) g v g' →
            cenv.wpEnv env p Q E
              { s with regs := s.regs.setRegOrZr dst ((v.setWidth 32).signExtend 64) } g')
      (Directive.instr ⟨.W64, .LDURSW dst a⟩ :: p) Q E := by
  intro s g ⟨ha, h⟩
  env_step
  obtain ⟨hnone, hok, hk⟩ := h ⟨pc, pc + .ofNat z⟩
  simp only [UnscaledAddrExpr.interpLoad]
  exact UnscaledAddrExpr.checkSP_AllEnv ha (MachineData.load_AllEnv (w := .W32) hnone hok fun v g' hs =>
    hk v g' hs _ hpl')

/-- `LDRSW Xt, label` on a location outside `dmem`: a plain 4-byte load from
the label's address, sign-extended. -/
theorem ldrsw_lit_shared (dst : RegOrZr .W64) (l : Label) :
    TripleEnv env
      (fun s g =>
        let e := (@Labels.label (_root_.Executable.labels cenv) l).toBitVec
        Mem.loadInt s.dmem e 4 = none ∧ env.ok (.load .plain false e 4) g ∧
          ∀ v g', env.step (.load .plain false e 4) g v g' →
            cenv.wpEnv env p Q E
              { s with regs := s.regs.setRegOrZr dst ((v.setWidth 32).signExtend 64) } g')
      (Directive.instr ⟨.W64, .LDRSW dst (.lit (.addr ⟨l⟩))⟩ :: p) Q E := by
  intro s g ⟨hnone, hok, hk⟩
  env_step
  simp only [AddrOrLit.interpLoad, Literal.interpLoad, BitVec.ofInt_toInt_int64, Effects.AllEnv]
  exact MachineData.load_AllEnv (w := .W32) hnone hok fun v g' hs => hk v g' hs _ hpl'

/-- `LDRSW Xt, =expr`: no memory access; `Xt` gets the constant truncated to
32 bits and sign-extended, in any environment. -/
theorem ldrsw_pool_env (dst : RegOrZr .W64) (c : ConstExpr) :
    TripleEnv env
      (fun s g => ∀ rng,
        let v := (BitVec.ofInt 32 (@ConstExpr.interp (_root_.Executable.labels cenv) c rng).toInt).signExtend 64
        cenv.wpEnv env p Q E { s with regs := s.regs.setRegOrZr dst v } g)
      (Directive.instr ⟨.W64, .LDRSW dst (.lit (.pool ⟨c⟩))⟩ :: p) Q E := by
  intro s g h
  env_step
  have hk := h ⟨pc, pc + .ofNat z⟩
  simp only [AddrOrLit.interpLoad, Literal.interpLoad, Effects.AllEnv]
  exact hk _ hpl'

/-! ## Acquire, exclusive and release accesses (the base-register forms of `WP.RulesAtomic`) -/

/-- `LDAR`/`LDAPR`/`LDXR`/`LDAXR Rt, [Xn|SP]` (+`B`/`H`) on a location outside
`dmem`: a load of kind `k` (`xcl`: exclusive) of `sz`; the tail runs with the
value zero-extended in `Rt`. -/
theorem ldar_shared {w : RegWidth} (k : LoadKind) (xcl : Bool) (sz : MemWidth) (dst : RegOrZr w)
    (base : RegOrSp .W64) :
    TripleEnv env
      (fun s g => base.SPAligned s ∧
        let a := s.regs.getRegOrSp base
        Mem.loadInt s.dmem a sz.bytes = none ∧ env.ok (.load k xcl a sz.bytes) g ∧
          ∀ v g', env.step (.load k xcl a sz.bytes) g v g' →
            cenv.wpEnv env p Q E
              { s with regs := s.regs.setRegOrZr dst ((v.setWidth sz.bits).setWidth w.bits) } g')
      (Directive.instr ⟨w, .LDAR k xcl sz dst base⟩ :: p) Q E := by
  intro s g ⟨ha, hnone, hok, hk⟩
  env_step
  exact RegOrSp.interpBase_AllEnv ha (MachineData.loadK_AllEnv hnone hok fun v g' hs => hk v g' hs _ hpl')

/-- `STLR Rt, [Xn|SP]` (+`B`/`H`) on a location outside `dmem`: a release
store of the low `sz` bits. -/
theorem stlr_shared {w : RegWidth} (sz : MemWidth) (src : RegOrZr w) (base : RegOrSp .W64) :
    TripleEnv env
      (fun s g => base.SPAligned s ∧
        let a := s.regs.getRegOrSp base
        let v := ((s.regs.getRegOrZr src).setWidth sz.bits).setWidth 128
        Mem.loadInt s.dmem a sz.bytes = none ∧ env.ok (.store .rel false a sz.bytes v) g ∧
          ∀ ok g', env.step (.store .rel false a sz.bytes v) g ok g' → cenv.wpEnv env p Q E s g')
      (Directive.instr ⟨w, .STLR sz src base⟩ :: p) Q E := by
  intro s g ⟨ha, hnone, hok, hk⟩
  env_step
  exact RegOrSp.interpBase_AllEnv ha (MachineData.storeK_AllEnv hnone hok fun b g' hs => hk b g' hs _ hpl')

/-- `STXR`/`STLXR Ws, Rt, [Xn|SP]` (+`B`/`H`) on a location outside `dmem`: a
store-exclusive of kind `k`. Success and failure are the environment's answer
`ok` (the `∀ ok` pattern of `WP.RulesAtomic`, with `env.step` in place of the machine's
nondeterminism): `Ws` gets `0` on success and `1` on failure, and the
environment state is whatever the store left. -/
theorem stxr_shared {w : RegWidth} (k : StoreKind) (sz : MemWidth) (status : RegOrZr .W32)
    (src : RegOrZr w) (base : RegOrSp .W64) :
    TripleEnv env
      (fun s g => base.SPAligned s ∧
        let a := s.regs.getRegOrSp base
        let v := ((s.regs.getRegOrZr src).setWidth sz.bits).setWidth 128
        Mem.loadInt s.dmem a sz.bytes = none ∧ env.ok (.store k true a sz.bytes v) g ∧
          ∀ ok g', env.step (.store k true a sz.bytes v) g ok g' →
            cenv.wpEnv env p Q E
              { s with regs := s.regs.setRegOrZr status (if ok then 0#32 else 1#32) } g')
      (Directive.instr ⟨w, .STXR k sz status src base⟩ :: p) Q E := by
  intro s g ⟨ha, hnone, hok, hk⟩
  env_step
  exact RegOrSp.interpBase_AllEnv ha (MachineData.storeK_AllEnv hnone hok fun b g' hs => hk b g' hs _ hpl')

/-! ## Read-modify-writes -/

/-- `CAS`/`CASA`/`CASL`/`CASAL Rs, Rt, [Xn|SP]` (+`B`/`H`) on a location
outside `dmem`: one `rmw` of kind `k` that writes `Rt` (truncated to `sz`) if
the old value equals `Rs` (truncated), and nothing otherwise; the old value
lands in `Rs`, zero-extended, either way. -/
theorem cas_shared {w : RegWidth} (k : RmwKind) (sz : MemWidth) (rs rt : RegOrZr w)
    (base : RegOrSp .W64) :
    TripleEnv env
      (fun s g => base.SPAligned s ∧
        let a := s.regs.getRegOrSp base
        let cmp := (s.regs.getRegOrZr rs).setWidth sz.bits
        let new := (s.regs.getRegOrZr rt).setWidth sz.bits
        let acc := SharedAccess.rmw k a sz.bytes
          (rmwOpBits sz.bits (fun old => if old == cmp then some new else none))
        Mem.loadInt s.dmem a sz.bytes = none ∧ env.ok acc g ∧
          ∀ v g', env.step acc g v g' →
            cenv.wpEnv env p Q E
              { s with regs := s.regs.setRegOrZr rs ((v.setWidth sz.bits).setWidth w.bits) } g')
      (Directive.instr ⟨w, .CAS k sz rs rt base⟩ :: p) Q E := by
  intro s g ⟨ha, hnone, hok, hk⟩
  env_step
  exact RegOrSp.interpBase_AllEnv ha (MachineData.rmwK_AllEnv hnone hok fun v g' hs => hk v g' hs _ hpl')

/-- `SWP`/`SWPA`/`SWPL`/`SWPAL Rs, Rt, [Xn|SP]` (+`B`/`H`) on a location
outside `dmem`: one `rmw` of kind `k` that writes `Rs` (truncated to `sz`);
the old value lands in `Rt`, zero-extended. -/
theorem swp_shared {w : RegWidth} (k : RmwKind) (sz : MemWidth) (rs rt : RegOrZr w)
    (base : RegOrSp .W64) :
    TripleEnv env
      (fun s g => base.SPAligned s ∧
        let a := s.regs.getRegOrSp base
        let new := (s.regs.getRegOrZr rs).setWidth sz.bits
        let acc := SharedAccess.rmw k a sz.bytes (rmwOpBits sz.bits (fun _ => some new))
        Mem.loadInt s.dmem a sz.bytes = none ∧ env.ok acc g ∧
          ∀ v g', env.step acc g v g' →
            cenv.wpEnv env p Q E
              { s with regs := s.regs.setRegOrZr rt ((v.setWidth sz.bits).setWidth w.bits) } g')
      (Directive.instr ⟨w, .SWP k sz rs rt base⟩ :: p) Q E := by
  intro s g ⟨ha, hnone, hok, hk⟩
  env_step
  exact RegOrSp.interpBase_AllEnv ha (MachineData.rmwK_AllEnv hnone hok fun v g' hs => hk v g' hs _ hpl')

/-- `LD<op>`/`LD<op>A`/`LD<op>L`/`LD<op>AL Rs, Rt, [Xn|SP]` (+`B`/`H`) for `op`
among `ADD CLR EOR SET SMAX SMIN UMAX UMIN`, and `ST<op>` (`Rt` is `ZR`), on a
location outside `dmem`: one `rmw` of kind `k` that writes `op old Rs`; the
old value lands in `Rt`, zero-extended. -/
theorem ldop_shared {w : RegWidth} (op : AtomicOp) (k : RmwKind) (sz : MemWidth) (rs rt : RegOrZr w)
    (base : RegOrSp .W64) :
    TripleEnv env
      (fun s g => base.SPAligned s ∧
        let a := s.regs.getRegOrSp base
        let arg := (s.regs.getRegOrZr rs).setWidth sz.bits
        let acc := SharedAccess.rmw k a sz.bytes (rmwOpBits sz.bits (fun old => some (op.apply old arg)))
        Mem.loadInt s.dmem a sz.bytes = none ∧ env.ok acc g ∧
          ∀ v g', env.step acc g v g' →
            cenv.wpEnv env p Q E
              { s with regs := s.regs.setRegOrZr rt ((v.setWidth sz.bits).setWidth w.bits) } g')
      (Directive.instr ⟨w, .LDOP op k sz rs rt base⟩ :: p) Q E := by
  intro s g ⟨ha, hnone, hok, hk⟩
  env_step
  exact RegOrSp.interpBase_AllEnv ha (MachineData.rmwK_AllEnv hnone hok fun v g' hs => hk v g' hs _ hpl')

/-- `CASP`/`CASPA`/`CASPL`/`CASPAL Rs1, Rs2, Rt1, Rt2, [Xn|SP]` (`X` or `W`
registers) with both halves outside `dmem`: the halves at `Xn` and
`Xn + w.bytes` compare with `Rs1`, `Rs2` and, on a match of both, take `Rt1`,
`Rt2`; the old halves land in `Rs1`, `Rs2` either way. The access is
`CaspEnv`: two `rmw`s of kind `k`, one per half, in either order (the pair is
not one atomic access, as in the Promising machine and herd). In `lastWrite`
use `casp_lastWrite`. -/
theorem casp_shared {w : RegWidth} (k : RmwKind) (rs1 rs2 rt1 rt2 : RegOrZr w) (base : RegOrSp .W64) :
    TripleEnv env
      (fun s g => base.SPAligned s ∧
        let a := s.regs.getRegOrSp base
        Mem.loadInt s.dmem a (w : MemWidth).bytes = none ∧
        Mem.loadInt s.dmem (a + (w : MemWidth).bytesv) (w : MemWidth).bytes = none ∧
        env.CaspEnv k a w (s.regs.getRegOrZr rs1) (s.regs.getRegOrZr rs2) (s.regs.getRegOrZr rt1)
          (s.regs.getRegOrZr rt2) g fun o₁ o₂ g' =>
            cenv.wpEnv env p Q E { s with regs := (s.regs.setRegOrZr rs1 o₁).setRegOrZr rs2 o₂ } g')
      (Directive.instr ⟨w, .CASP k rs1 rs2 rt1 rt2 base⟩ :: p) Q E := by
  intro s g ⟨ha, hn₁, hn₂, hk⟩
  env_step
  exact RegOrSp.interpBase_AllEnv ha (MachineData.rmwPairK_AllEnv hn₁ hn₂ (hk.mono fun _ _ _ h => h _ hpl'))

/-! ## Barriers

A barrier is a `fence` access: permitted and answered by the environment (an
environment with views raises them there). With `FencesSkip` (`lastWrite`,
`none`, any environment without views) it is a no-op, as on one thread. -/

/-- `DMB <option>`: a `fence k`. -/
theorem dmb_shared (k : FenceKind) :
    TripleEnv env
      (fun s g => env.ok (.fence k) g ∧ ∀ g', env.step (.fence k) g () g' → cenv.wpEnv env p Q E s g')
      (Directive.instr ⟨.W64, .DMB k⟩ :: p) Q E := by
  intro s g ⟨hok, hk⟩
  env_step
  simp only [Effects.AllEnv]
  exact ⟨hok, fun g' hs => hk g' hs _ hpl'⟩

/-- `DSB <option>`: a `fence k`, where `DSB ST` is the stronger `.stAll`
(earlier stores before every later access). -/
theorem dsb_shared (k : FenceKind) :
    let k' := if k == .st then FenceKind.stAll else k
    TripleEnv env
      (fun s g => env.ok (.fence k') g ∧ ∀ g', env.step (.fence k') g () g' → cenv.wpEnv env p Q E s g')
      (Directive.instr ⟨.W64, .DSB k⟩ :: p) Q E := by
  intro k' s g ⟨hok, hk⟩
  env_step
  simp only [Effects.AllEnv]
  exact ⟨hok, fun g' hs => hk g' hs _ hpl'⟩

/-- `ISB`: a `fence .isb`. -/
theorem isb_shared :
    TripleEnv env
      (fun s g => env.ok (.fence .isb) g ∧ ∀ g', env.step (.fence .isb) g () g' → cenv.wpEnv env p Q E s g')
      (Directive.instr ⟨.W64, .ISB⟩ :: p) Q E := by
  intro s g ⟨hok, hk⟩
  env_step
  simp only [Effects.AllEnv]
  exact ⟨hok, fun g' hs => hk g' hs _ hpl'⟩

variable {env}

/-- `DMB <option>` where fences skip: the tail's wp at the same state. -/
theorem dmb_skip (h : env.FencesSkip) (k : FenceKind) :
    TripleEnv env (fun s g => cenv.wpEnv env p Q E s g) (Directive.instr ⟨.W64, .DMB k⟩ :: p) Q E :=
  fun s g hk => dmb_shared env k s g ⟨(h k g).1, fun g' hs => ((h k g).2 g' hs) ▸ hk⟩

/-- `DSB <option>` where fences skip. -/
theorem dsb_skip (h : env.FencesSkip) (k : FenceKind) :
    TripleEnv env (fun s g => cenv.wpEnv env p Q E s g) (Directive.instr ⟨.W64, .DSB k⟩ :: p) Q E :=
  fun s g hk => dsb_shared env k s g ⟨(h _ g).1, fun g' hs => ((h _ g).2 g' hs) ▸ hk⟩

/-- `ISB` where fences skip. -/
theorem isb_skip (h : env.FencesSkip) :
    TripleEnv env (fun s g => cenv.wpEnv env p Q E s g) (Directive.instr ⟨.W64, .ISB⟩ :: p) Q E :=
  fun s g hk => isb_shared env s g ⟨(h _ g).1, fun g' hs => ((h _ g).2 g' hs) ▸ hk⟩

/-- `CASP` (all ordering variants) in `lastWrite L`: both halves are
locations of `L`; the tail runs with the old halves in `Rs1`, `Rs2` and, on a
match of both, both new values written (`SharedEnv.caspLW`; `casp_shared` by
`SharedEnv.lastWrite_caspEnv_iff`). -/
theorem casp_lastWrite {L : SharedEnv.Layout} {Q : MachineData → (SharedEnv.lastWrite L).State → Prop}
    {E : Int64 → MachineData → (SharedEnv.lastWrite L).State → Prop} {w : RegWidth} (k : RmwKind)
    (rs1 rs2 rt1 rt2 : RegOrZr w) (base : RegOrSp .W64) :
    TripleEnv (SharedEnv.lastWrite L)
      (fun s g => base.SPAligned s ∧
        let a := s.regs.getRegOrSp base
        let a₂ := a + (w : MemWidth).bytesv
        let o₁ := (g a).setWidth (w : MemWidth).bits
        let o₂ := (g a₂).setWidth (w : MemWidth).bits
        Mem.loadInt s.dmem a (w : MemWidth).bytes = none ∧ Mem.loadInt s.dmem a₂ (w : MemWidth).bytes = none ∧
        (a, (w : MemWidth).bytes) ∈ L ∧ (a₂, (w : MemWidth).bytes) ∈ L ∧
        cenv.wpEnv (SharedEnv.lastWrite L) p Q E { s with regs := (s.regs.setRegOrZr rs1 o₁).setRegOrZr rs2 o₂ }
          (SharedEnv.caspLW g a w (s.regs.getRegOrZr rs1) (s.regs.getRegOrZr rs2) (s.regs.getRegOrZr rt1)
            (s.regs.getRegOrZr rt2)))
      (Directive.instr ⟨w, .CASP k rs1 rs2 rt1 rt2 base⟩ :: p) Q E :=
  fun s g ⟨ha, hn₁, hn₂, hm₁, hm₂, hk⟩ =>
    casp_shared _ k rs1 rs2 rt1 rt2 base s g ⟨ha, hn₁, hn₂, SharedEnv.lastWrite_caspEnv_iff.mpr ⟨hm₁, hm₂, hk⟩⟩

end MachineWP
