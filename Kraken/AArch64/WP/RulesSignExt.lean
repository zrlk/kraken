/-
The sign-extending loads of the AArch64 machine-founded wp, next to the
zero-extending ones of `Kraken.AArch64.WP.Rules` (`ldrb_spec`, `ldrh_spec`)
and the base-register forms of `Kraken.AArch64.WP.RulesAtomic`.

As the memory rules of `WP.Rules`: mapped memory (`dmem`) only, the bytes must be readable
(`isSome`), the tail runs at every value they may hold, and an access through
`SP` needs `SP` 16-byte aligned (`AddrExpr.SPAligned` for the scaled forms,
`RegOrSp.SPAligned` of the base for the unscaled ones). The value is the
loaded field sign-extended to the register (`BitVec.signExtend`); a `W`
destination is then zero-extended into the `X` register by `setRegOrZr`, as
for every `W` write.

## Coverage

| Rule | Instruction forms | Widths |
|---|---|---|
| `ldrsb_spec`, `ldrsh_spec` | `LDRSB`/`LDRSH Rt, [Xn\|SP …]`, every addressing form | X, W |
| `ldrsw_spec` | `LDRSW Xt, [Xn\|SP …]`, every addressing form | X |
| `ldursb_spec`, `ldursh_spec` | `LDURSB`/`LDURSH Rt, [Xn\|SP, #simm9]` | X, W |
| `ldursw_spec` | `LDURSW Xt, [Xn\|SP, #simm9]` | X |
| `ldpsw_spec` | `LDPSW Xt1, Xt2, [Xn\|SP …]`: offset, pre-index, post-index | X |

`LDRSW Xt, label` and `LDRSW Xt, =expr` (the literal forms) have no mapped
rule, like `LDR Rt, label`: the combined rules of
`Kraken/AArch64/EnvVCGen.lean` (`ldrsw_lit_env_spec`, `ldrsw_pool_env_spec`)
serve them.

The unscaled forms leave `UnscaledAddrExpr.eval` in a VC; `UnscaledAddrExpr.eval_eq`
(here, so that the mapped rules have it too) reduces it to the base plus the
offset.
-/
import Kraken.AArch64.WP.RulesAtomic

open Kraken
open Std.WP
open Lean.Order

/-- `[Xn|SP, #simm9]` (`LDUR`/`STUR`): the base plus the offset (the unscaled
counterpart of `AddrExpr.eval_imm`). -/
@[simp, grind =] theorem UnscaledAddrExpr.eval_eq [Labels] (b : RegOrSp .W64) (i : ConstExpr)
    (s : MachineData) (p : Std.Rco Int64) :
    UnscaledAddrExpr.eval ⟨b, i⟩ s p = s.regs.getRegOrSp b + (i.interp p).toBitVec := by
  simp only [UnscaledAddrExpr.eval, BitVec.signed_eq]
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt_int64]

private theorem AddrExpr.checkSP_All {a : AddrExpr} {s : MachineData} {ok : Unit → Effects}
    {P : MachineState → Prop} (ha : a.SPAligned s) (hk : (ok ()).All P) :
    (a.checkSPAlignment s ok).All P := by
  obtain ⟨⟨b, w⟩, off⟩ := a
  cases b with
  | reg r => exact hk
  | SP =>
    have h := ha rfl
    simp only [AddrExpr.checkSPAlignment, Reg64s.getRegOrSp_SP, h, bne_self_eq_false,
      Bool.false_eq_true, ite_false]
    exact hk

private theorem UnscaledAddrExpr.checkSP_All {a : UnscaledAddrExpr} {s : MachineData}
    {ok : Unit → Effects} {P : MachineState → Prop} (ha : a.base.SPAligned s)
    (hk : (ok ()).All P) : (a.checkSPAlignment s ok).All P := by
  obtain ⟨⟨b, w⟩, off⟩ := a
  cases b with
  | reg r => exact hk
  | SP =>
    have h := ha rfl
    simp only [UnscaledAddrExpr.checkSPAlignment, Reg64s.getRegOrSp_SP, h, bne_self_eq_false,
      Bool.false_eq_true, ite_false]
    exact hk

private theorem MachineData.load_All {s : MachineData} {addr : BitVec 64} {w : MemWidth}
    {ret : w.type → MachineData → Effects} {P : MachineState → Prop} {v : Int}
    (hv : Mem.loadInt s.dmem addr w.bytes = some v) (hk : (ret (.ofInt _ v) s).All P) :
    (s.load addr w ret).All P := by
  simp only [MachineData.load, Effects.All, hv]
  exact hk

section Specs

open MachineWP

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp, Effects.All,
      or_false, false_or])

/-- Unfold the fall-through address past one instruction cell (`Rules.lean`). -/
private theorem after_instr {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

/-- The rule of a cell that falls through with an arbitrary precondition
(`Rules.lean`'s `fallthrough_pre_spec`). -/
private theorem fallthrough_pre_spec {i : Instr} {P : MachineData → Prop}
    (hcell : ∀ (s : MachineData) (rng : Std.Rco Int64) (R : MachineState → Prop),
      P s → (∀ s', WP.wp p Q E s' → R (s', 0)) →
      (@Directive.interp (_root_.Executable.labels cenv) (Directive.instr i) s rng
        (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All R) :
    ⦃ P ⦄ (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    exact step_cps _ _ _ ⟨_, z, rest, hseg, Or.inl (hcell s _ _ h (fun s' hs' => hs' _ hpl'))⟩

/-! ### The scaled forms -/

/-- `LDRSB Rt, [Xn|SP …]` : the byte, sign-extended to the register. -/
@[spec] theorem MachineWP.ldrsb_spec {w : RegWidth} (dst : RegOrZr w) (a : AddrExpr) :
    ⦃ fun s => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        ((Mem.loadInt e.2.dmem e.1 1).isSome = true)
          ⊓ (∀ v, Mem.loadInt e.2.dmem e.1 1 = some v →
            WP.wp p Q E { e.2 with regs := e.2.regs.setRegOrZr dst ((BitVec.ofInt 8 v).signExtend w.bits) }) ⦄
      (Directive.instr ⟨w, .LDRSB dst a⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨hsome, hk⟩ := h rng
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    wp_step
    simp only [AddrExpr.interpLoad]
    exact AddrExpr.checkSP_All ha (MachineData.load_All (w := .W8) hv (hR _ (hk v hv))))

/-- `LDRSH Rt, [Xn|SP …]` : the halfword, sign-extended to the register. -/
@[spec] theorem MachineWP.ldrsh_spec {w : RegWidth} (dst : RegOrZr w) (a : AddrExpr) :
    ⦃ fun s => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        ((Mem.loadInt e.2.dmem e.1 2).isSome = true)
          ⊓ (∀ v, Mem.loadInt e.2.dmem e.1 2 = some v →
            WP.wp p Q E { e.2 with regs := e.2.regs.setRegOrZr dst ((BitVec.ofInt 16 v).signExtend w.bits) }) ⦄
      (Directive.instr ⟨w, .LDRSH dst a⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨hsome, hk⟩ := h rng
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    wp_step
    simp only [AddrExpr.interpLoad]
    exact AddrExpr.checkSP_All ha (MachineData.load_All (w := .W16) hv (hR _ (hk v hv))))

/-- `LDRSW Xt, [Xn|SP …]` : the word, sign-extended to 64 bits. -/
@[spec] theorem MachineWP.ldrsw_spec (dst : RegOrZr .W64) (a : AddrExpr) :
    ⦃ fun s => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        ((Mem.loadInt e.2.dmem e.1 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt e.2.dmem e.1 4 = some v →
            WP.wp p Q E { e.2 with regs := e.2.regs.setRegOrZr dst ((BitVec.ofInt 32 v).signExtend 64) }) ⦄
      (Directive.instr ⟨.W64, .LDRSW dst (.addr a)⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨hsome, hk⟩ := h rng
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    wp_step
    simp only [AddrOrLit.interpLoad, AddrExpr.interpLoad]
    exact AddrExpr.checkSP_All ha (MachineData.load_All (w := .W32) hv (hR _ (hk v hv))))

/-- `LDPSW Xt1, Xt2, [Xn|SP …]` : two words, at the address and 4 bytes on,
both readable; the tail runs with both sign-extended into the registers, after
the base writeback. -/
@[spec] theorem MachineWP.ldpsw_spec (dst1 dst2 : RegOrZr .W64) (a : AddrExpr) :
    ⦃ fun s => a.SPAligned s ⊓ ∀ rng,
        let e := @AddrExpr.eval (_root_.Executable.labels cenv) a s rng
        let a₂ := e.1 + 4#64
        ((Mem.loadInt e.2.dmem e.1 4).isSome = true)
          ⊓ ((Mem.loadInt e.2.dmem a₂ 4).isSome = true)
          ⊓ (∀ v₁ v₂, Mem.loadInt e.2.dmem e.1 4 = some v₁ →
              Mem.loadInt e.2.dmem a₂ 4 = some v₂ →
            let r := (e.2.regs.setRegOrZr dst1 ((BitVec.ofInt 32 v₁).signExtend 64)).setRegOrZr dst2
              ((BitVec.ofInt 32 v₂).signExtend 64)
            WP.wp p Q E { e.2 with regs := r }) ⦄
      (Directive.instr ⟨.W64, .LDPSW dst1 dst2 a⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨⟨hsome₁, hsome₂⟩, hk⟩ := h rng
    obtain ⟨v₁, hv₁⟩ := Option.isSome_iff_exists.mp hsome₁
    obtain ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.mp hsome₂
    wp_step
    exact AddrExpr.checkSP_All ha (MachineData.load_All (w := .W32) hv₁
      (MachineData.load_All (w := .W32) hv₂ (hR _ (hk v₁ v₂ hv₁ hv₂)))))

/-! ### The unscaled forms -/

/-- `LDURSB Rt, [Xn|SP, #simm9]` : the byte, sign-extended to the register. -/
@[spec] theorem MachineWP.ldursb_spec {w : RegWidth} (dst : RegOrZr w) (a : UnscaledAddrExpr) :
    ⦃ fun s => a.base.SPAligned s ⊓ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        ((Mem.loadInt s.dmem e 1).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem e 1 = some v →
            WP.wp p Q E { s with regs := s.regs.setRegOrZr dst ((BitVec.ofInt 8 v).signExtend w.bits) }) ⦄
      (Directive.instr ⟨w, .LDURSB dst a⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨hsome, hk⟩ := h rng
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    wp_step
    simp only [UnscaledAddrExpr.interpLoad]
    exact UnscaledAddrExpr.checkSP_All ha (MachineData.load_All (w := .W8) hv (hR _ (hk v hv))))

/-- `LDURSH Rt, [Xn|SP, #simm9]` : the halfword, sign-extended to the register. -/
@[spec] theorem MachineWP.ldursh_spec {w : RegWidth} (dst : RegOrZr w) (a : UnscaledAddrExpr) :
    ⦃ fun s => a.base.SPAligned s ⊓ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        ((Mem.loadInt s.dmem e 2).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem e 2 = some v →
            WP.wp p Q E { s with regs := s.regs.setRegOrZr dst ((BitVec.ofInt 16 v).signExtend w.bits) }) ⦄
      (Directive.instr ⟨w, .LDURSH dst a⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨hsome, hk⟩ := h rng
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    wp_step
    simp only [UnscaledAddrExpr.interpLoad]
    exact UnscaledAddrExpr.checkSP_All ha (MachineData.load_All (w := .W16) hv (hR _ (hk v hv))))

/-- `LDURSW Xt, [Xn|SP, #simm9]` : the word, sign-extended to 64 bits. -/
@[spec] theorem MachineWP.ldursw_spec (dst : RegOrZr .W64) (a : UnscaledAddrExpr) :
    ⦃ fun s => a.base.SPAligned s ⊓ ∀ rng,
        let e := @UnscaledAddrExpr.eval (_root_.Executable.labels cenv) a s rng
        ((Mem.loadInt s.dmem e 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem e 4 = some v →
            WP.wp p Q E { s with regs := s.regs.setRegOrZr dst ((BitVec.ofInt 32 v).signExtend 64) }) ⦄
      (Directive.instr ⟨.W64, .LDURSW dst a⟩ :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_pre_spec (fun s rng R h hR => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨hsome, hk⟩ := h rng
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    wp_step
    simp only [UnscaledAddrExpr.interpLoad]
    exact UnscaledAddrExpr.checkSP_All ha (MachineData.load_All (w := .W32) hv (hR _ (hk v hv))))

end Specs
