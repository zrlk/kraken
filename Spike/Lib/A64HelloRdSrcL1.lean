/-
**`wc_rodata`'s source rows from `.sp0` at rodata's own label** (AArch64,
`Level1I`'s `hP`): concrete invariants of `wc_rodata`'s nodes from the allocator's return
(`HelloRd.pN`'s `Jp'` … `J5`) at the label `l` rodata allocated, and `MainGlueS.MainWcPS`'s source fields at them
(`hr0`, `h1`, `h2`, `hr2`, `h3`, `h4`, `hfen`, `hedge`), from `HelloRodataSrc`'s rows (the hello twins of
`Hello1.sJp'` … `sJ4` and `hello1_rodata_setupW`'s cases).

Each invariant carries `RB lbl l σ0`: `.sp0`'s `x0` (the buffer's base) is `l`'s place, its two words below
`2 ^ 64`. At `.sp0` (`Jp`) the source is at `rdCA l ini` (`hJp`, the allocator's return past rodata's `newBuf`).
`wc_rodata`'s return pops the setup call's frame `frH env` into `HelloJr1.JrRL lbl env l` (`hedge`).

- `RB`, `jP'`, `jX1`, `jC2`, `jC2'`, `jX3`, `jC4`, `jRet`: the invariants.
- `hr0_rd`, `h1_rd`, `h2_rd`, `hr2_rd`, `h3_rd`, `h4_rd`, `hfen_rd`, `hedge_rd`: `MainWcPS`'s fields at them.
-/
import Spike.Lib.HelloRodataSrc
import Spike.Lib.A64HelloRdCf
import Spike.Lib.A64HelloJr1L
import Spike.Lib.A64HelloRodata

namespace Spike.Lib.A64.HelloPh.RdSrcL1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open TermRun (Word Env evalAt)
open Spike.Lib (Ctl LocalRun XchgSite FenceRun)
open Scc.Sem (ValRep)
open Spike.Lib.A64.Flow (rAddr)
open Spike.Lib.A64.Flow.Hello1 (rpK1 rpK2)
open Spike.Lib.HelloRodataSrc (rdCA rdC1 rdC2 rdC3 rdC4 rdRet rdCA_store rdC2_store rdC1_next rdC3_next rdC4_fence
  rdRet_ret)
open Spike.Lib.Hello1RodataSrc (rdK1 rdK2)
open Spike.Lib.HelloRdCf (frH retJH)
open Spike.Lib.A64.Flow.HelloJr1 (JrRL)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable (lbl : WeakMem.AllocLabel → Option Nat) (l : WeakMem.AllocLabel)

/-- **`.sp0`'s base**: `x0` is `l`'s place, its two words below `2 ^ 64`. -/
def RB (σ0 : FAS) : Prop :=
  lbl l = some σ0.regs.X0.toBitVec.toNat ∧ σ0.regs.X0.toBitVec.toNat + 16 ≤ 2 ^ 64

/-- Before the first exchange's load (`Hello1.sJp'`). -/
def jP' (σ0 : FAS) (c : Ctl) : Prop := RB lbl l σ0 ∧ ∃ ini, c = rdC1 l ini

/-- The first word held (`Hello1.sJh1`). -/
def jX1 (σ0 : FAS) (c : Ctl) : Prop :=
  RB lbl l σ0 ∧ ∃ ini w, c = { rdC1 l ini with hold := some ((rAddr σ0.regs .X0 0).toNat, w) }

/-- After the first exchange (`Hello1.sJ2`). -/
def jC2 (σ0 : FAS) (c : Ctl) : Prop := RB lbl l σ0 ∧ ∃ ini wo0, c = rdC2 l ini wo0

/-- Before the second exchange's load (`Hello1.sJ2'`). -/
def jC2' (σ0 : FAS) (c : Ctl) : Prop := RB lbl l σ0 ∧ ∃ ini wo0, c = rdC3 l ini wo0

/-- The second word held (`Hello1.sJh2`). -/
def jX3 (σ0 : FAS) (c : Ctl) : Prop :=
  RB lbl l σ0 ∧ ∃ ini wo0 w, c = { rdC3 l ini wo0 with hold := some ((rAddr σ0.regs .X0 8).toNat, w) }

/-- After the second exchange, at the publication (`Hello1.sJ4`). -/
def jC4 (σ0 : FAS) (c : Ctl) : Prop := RB lbl l σ0 ∧ ∃ ini wo0 wo1, c = rdC4 l ini wo0 wo1

/-- After the publication's fence, at `ret sl`. -/
def jRet (σ0 : FAS) (c : Ctl) : Prop := RB lbl l σ0 ∧ ∃ ini wo0 wo1, c = rdRet l ini wo0 wo1

variable {lbl l}

theorem rAddr0 {σ0 : FAS} (_h : RB lbl l σ0) : (rAddr σ0.regs .X0 0).toNat = σ0.regs.X0.toBitVec.toNat + 8 * 0 := by
  have : rAddr σ0.regs .X0 0 = σ0.regs.X0.toBitVec := by
    simp [rAddr, Reg64s.getXReg]
  rw [this]; omega

theorem rAddr8 {σ0 : FAS} (h : RB lbl l σ0) : (rAddr σ0.regs .X0 8).toNat = σ0.regs.X0.toBitVec.toNat + 8 * 1 := by
  have : rAddr σ0.regs .X0 8 = σ0.regs.X0.toBitVec + 8#64 := by
    simp [rAddr, Reg64s.getXReg, BitVec.ofInt_add]
  rw [this, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.2; omega)]

variable {p : Prog} {Jp : FAS → Ctl → Prop}

/-- **`MainWcPS.hr0`**: from `.sp0` at `rdCA l ini` (`hJp`) the `asLanes` step to `rdC1`. -/
theorem hr0_rd (hJp : ∀ σ0 c, Jp σ0 c → RB lbl l σ0 ∧ ∃ ini, c = rdCA l ini) :
    ∀ σ0 c, Jp σ0 c → ∃ c', LocalRun p c c' ∧ jP' lbl l σ0 c' := by
  intro σ0 c h
  obtain ⟨hB, ini, rfl⟩ := hJp σ0 c h
  exact ⟨_, .single (rdCA_store (p := p) (ini := ini) hB.1).1, hB, ini, rfl⟩

/-- **`MainWcPS.h1`**: the first exchange's site at `x0`, its load holding any word. -/
theorem h1_rd {rd : Word → Prop} :
    ∀ σ0 c, jP' lbl l σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : Word), rd w' → ValRep lbl w'.val (r.setWidth 64).toNat →
        jX1 lbl l σ0 { c with hold := some ((rAddr σ0.regs .X0 0).toNat, w') } := by
  rintro σ0 c ⟨hB, ini, rfl⟩
  obtain ⟨-, hx, hv, hh, -, -⟩ := rdCA_store (p := Spike.Lib.HelloSrc.helloSrc) (ini := ini) hB.1
  exact ⟨_, _, _, _, _, hx, by rw [rAddr0 hB]; exact hv, hh, fun _ w' _ _ => ⟨hB, ini, w', rfl⟩⟩

/-- **`MainWcPS.h2`**: the first exchange's store of `rdK1`, the old word bound, to `rdC2`. -/
theorem h2_rd :
    ∀ σ0 c, jX1 lbl l σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : Word),
      XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 0).toNat, wold) ∧ evalAt c.env v = some (tv, [wv]) ∧
      ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ jC2 lbl l σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩ := by
  rintro σ0 c ⟨hB, ini, w', rfl⟩
  obtain ⟨-, hx, hv, -, hev, hk⟩ := rdCA_store (p := Spike.Lib.HelloSrc.helloSrc) (ini := ini) hB.1
  refine ⟨_, _, _, _, _, _, _, w', hx, by rw [rAddr0 hB]; exact hv, rfl, hev, ?_, hB, ini, w',
    (rdC1_next l ini w').symm⟩
  rw [show (rpK1.setWidth 128).toNat = rdK1 by decide]; exact hk

/-- **`MainWcPS.hr2`**: the second `asLanes` step to `rdC3`. -/
theorem hr2_rd : ∀ σ0 c, jC2 lbl l σ0 c → ∃ c', LocalRun p c c' ∧ jC2' lbl l σ0 c' := by
  rintro σ0 c ⟨hB, ini, wo0, rfl⟩
  exact ⟨_, .single (rdC2_store (p := p) (ini := ini) (wo0 := wo0) hB.1).1, hB, ini, wo0, rfl⟩

/-- **`MainWcPS.h3`**: the second exchange's site at `x0 + 8`, its load holding any word. -/
theorem h3_rd {rd : Word → Prop} :
    ∀ σ0 c, jC2' lbl l σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : Word), rd w' → ValRep lbl w'.val (r.setWidth 64).toNat →
        jX3 lbl l σ0 { c with hold := some ((rAddr σ0.regs .X0 8).toNat, w') } := by
  rintro σ0 c ⟨hB, ini, wo0, rfl⟩
  obtain ⟨-, hx, hv, hh, -, -⟩ := rdC2_store (p := Spike.Lib.HelloSrc.helloSrc) (ini := ini) (wo0 := wo0) hB.1
  exact ⟨_, _, _, _, _, hx, by rw [rAddr8 hB]; exact hv, hh, fun _ w' _ _ => ⟨hB, ini, wo0, w', rfl⟩⟩

/-- **`MainWcPS.h4`**: the second exchange's store of `rdK2`, the old word bound, to `rdC4`. -/
theorem h4_rd :
    ∀ σ0 c, jX3 lbl l σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : Word),
      XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 8).toNat, wold) ∧ evalAt c.env v = some (tv, [wv]) ∧
      ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ jC4 lbl l σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩ := by
  rintro σ0 c ⟨hB, ini, wo0, w', rfl⟩
  obtain ⟨-, hx, hv, -, hev, hk⟩ := rdC2_store (p := Spike.Lib.HelloSrc.helloSrc) (ini := ini) (wo0 := wo0) hB.1
  refine ⟨_, _, _, _, _, _, _, w', hx, by rw [rAddr8 hB]; exact hv, rfl, hev, ?_, hB, ini, wo0, w',
    (rdC3_next l ini wo0 w').symm⟩
  rw [show (rpK2.setWidth 128).toNat = rdK2 by decide]; exact hk

/-- **`MainWcPS.hfen`**: the publication's fence run to `ret sl`, where the memory side admits it (`hP`). -/
theorem hfen_rd {P : Prop} (hP : P) : ∀ σ0 c, jC4 lbl l σ0 c → ∃ c', FenceRun p P .st c c' ∧ jRet lbl l σ0 c' := by
  rintro σ0 c ⟨hB, ini, wo0, wo1, rfl⟩
  exact ⟨_, rdC4_fence hP l ini wo0 wo1, hB, ini, wo0, wo1, rfl⟩

/-- **`MainWcPS.hedge`**: at `ret sl` (no further step), its pop of the setup call's frame `frH env` lands in
`JrRL lbl env l` at any state whose `x0` … `x3` are the slice's (`x0` `.sp0`'s base). -/
theorem hedge_rd {env : Env} :
    ∀ σ0 c, jRet lbl l σ0 c → ∀ σ' : FAS, σ'.regs.X0.toBitVec = σ0.regs.X0.toBitVec →
      σ'.regs.X1.toBitVec = 0#64 → σ'.regs.X2.toBitVec = 2#64 → σ'.regs.X3.toBitVec = 13#64 →
      σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
      ∃ c', LocalRun p c c' ∧ retJH (frH env) (JrRL lbl env l) σ' c' := by
  rintro σ0 c ⟨hB, ini, wo0, wo1, rfl⟩ σ' h0 h1 h2 h3 - -
  refine ⟨_, .refl _, _, _, _, (rdRet_ret l ini wo0 wo1).1, (rdRet_ret l ini wo0 wo1).2.2, rfl, ?_, ?_, ?_, ?_⟩
  · rw [h0]; exact hB.1
  · rw [h1]; rfl
  · rw [h2]; rfl
  · rw [h3]; rfl

end Spike.Lib.A64.HelloPh.RdSrcL1

/-- info: 'Spike.Lib.A64.HelloPh.RdSrcL1.hr0_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdSrcL1.hr0_rd

/-- info: 'Spike.Lib.A64.HelloPh.RdSrcL1.h1_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdSrcL1.h1_rd

/-- info: 'Spike.Lib.A64.HelloPh.RdSrcL1.h2_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdSrcL1.h2_rd

/-- info: 'Spike.Lib.A64.HelloPh.RdSrcL1.hr2_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdSrcL1.hr2_rd

/-- info: 'Spike.Lib.A64.HelloPh.RdSrcL1.h3_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdSrcL1.h3_rd

/-- info: 'Spike.Lib.A64.HelloPh.RdSrcL1.h4_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdSrcL1.h4_rd

/-- info: 'Spike.Lib.A64.HelloPh.RdSrcL1.hfen_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdSrcL1.hfen_rd

/-- info: 'Spike.Lib.A64.HelloPh.RdSrcL1.hedge_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdSrcL1.hedge_rd

/-- info: 'Spike.Lib.A64.HelloPh.RdSrcL1.rAddr0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdSrcL1.rAddr0

/-- info: 'Spike.Lib.A64.HelloPh.RdSrcL1.rAddr8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdSrcL1.rAddr8
