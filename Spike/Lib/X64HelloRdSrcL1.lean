/-
**`wc_rodata`'s source rows from `.x15` at rodata's own label** (x86-64; the twin of
`Spike/Lib/A64HelloRdSrcL1.lean`): concrete invariants of `wc_rodata`'s nodes from the allocator's return
(`HelloRd.pN`'s `Jp'` … `J4`) at the label `l` rodata allocated, and `MainGlueS.MainWcPS`'s source fields at them
(`hr0`, `h1`, `h2`, `hr2`, `h3`, `h4`), from `X64HelloRodataSrc`'s rows; the publication's source run (`hfen_rd`)
and the return's pop (`hedge_rd`) past it.

Each invariant carries `RB lbl l σ0`: `.x15`'s `%rax` (the buffer's base) is `l`'s place, its two words below
`2 ^ 64`. At `.x15` (`Jp`) the source is at `rdCA l ini` (`hJp`, the allocator's return past rodata's `newBuf`).
`wc_rodata`'s return pops the setup call's frame `frH env` into `HelloJr1.JrRL lbl env l` (`hedge_rd`).

- `RB`, `jP'`, `jX1`, `jC2`, `jC2'`, `jX3`, `jC4`, `jC5`, `jRet`: the invariants.
- `bAddr0`, `bAddr8`: the exchanges' addresses off `%rax`.
- `hr0_rd`, `h1_rd`, `h2_rd`, `hr2_rd`, `h3_rd`, `h4_rd`: `MainWcPS`'s fields at them.
- `hfen_rd`: the publication's `FenceRun` from `jC4` (at `let s = publish b`) to `jRet` (at `ret sl`).
- `hfen_msOfAX`: `hfen_rd` at the rows' memory side `msOfAX … ar …`, given `ar.pub` (`X64.WakeOD.arW_pub`).
- `pubStep_det`, `hpubx_rd`, `hlocx_rd`: the publication's step is determined by its control, so from `jC4` it
  lands in `jC5` (`MainWcPS.hpubx`), which runs locally to `jRet` (`MainWcPS.hlocx`).
- `hedge_rd`: at `jRet`, the return's pop of `frH env` lands in `JrRL lbl env l`.

## Differences from the AArch64 version

- The buffer's base is `%rax` and the exchanges' addresses are `bAddr σ0.regs .rax 0` / `8` (AArch64: `x0`,
  `rAddr … .X0`); `rAddr0`/`rAddr8` are named `bAddr0`/`bAddr8` accordingly. The slice's registers at the
  return are `%rax`, `%rdx`, `%rcx`, `%rsi` (AArch64: `x0` … `x3`), and the frame registers `hedge_rd` ignores
  are `%rbp`/`%rsp` (AArch64: `x29`/`x30`).
- x86-64's `wc_rodata` has no fence node (the source's `publish b` is lowered to no code under TSO). The
  publication is not a `LocalStep` (it moves the thread's release view, `fenceS … .st`), so it is taken as a
  source stutter before `wc_rodata`'s exit row (`X64SegWPub.SegWP`): `MainWcPS.hfen` is the publication's run
  from `J4` to `J5`, with no code row, and `MainWcPS.hedge` is from `J5`. At `J4 := jC4`, `J5 := jRet` they are
  `hfen_rd` (`hfen_msOfAX` at the rows' memory side) and `hedge_rd`, stated as AArch64's. The last block's
  controls past the publication are `MainWcPS`'s `J4x := jC5` (`hpubx_rd`, `hlocx_rd`; AArch64 has the fence
  node's invariant instead).
-/
import Spike.Lib.X64HelloRdCf
import Spike.Lib.X64HelloJr1L
import Spike.Lib.X64HelloRodata

namespace Spike.Lib.X64.HelloPh.RdSrcL1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open TermRun (Word Env evalAt)
open Spike.Lib (Ctl LocalRun XchgSite FenceRun PubStep)
open Scc.Sem (ValRep)
open Spike.Lib.X64 (bAddr)
open Spike.Lib.X64.Flow.Hello1 (rpK1 rpK2)
open Spike.Lib.X64HelloRodataSrc (rdCA rdC1 rdC2 rdC3 rdC4 rdC5 rdRet rdCA_store rdC2_store rdC1_next rdC3_next
  rdC4_fence rdCP_pub rdC5_run rdRet_ret)
open Spike.Lib.Hello1RodataSrc (rdK1 rdK2)
open Spike.Lib.X64HelloRdCf (frH retJH)
open Spike.Lib.X64.Flow.HelloJr1 (JrRL)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable (lbl : WeakMem.AllocLabel → Option Nat) (l : WeakMem.AllocLabel)

/-- **`.x15`'s base**: `%rax` is `l`'s place, its two words below `2 ^ 64`. -/
def RB (σ0 : FAS) : Prop :=
  lbl l = some σ0.regs.rax.toBitVec.toNat ∧ σ0.regs.rax.toBitVec.toNat + 16 ≤ 2 ^ 64

/-- Before the first exchange's load (`Hello1.sJp'`). -/
def jP' (σ0 : FAS) (c : Ctl) : Prop := RB lbl l σ0 ∧ ∃ ini, c = rdC1 l ini

/-- The first word held (`Hello1.sJh1`). -/
def jX1 (σ0 : FAS) (c : Ctl) : Prop :=
  RB lbl l σ0 ∧ ∃ ini w, c = { rdC1 l ini with hold := some ((bAddr σ0.regs .rax 0).toNat, w) }

/-- After the first exchange (`Hello1.sJ2`). -/
def jC2 (σ0 : FAS) (c : Ctl) : Prop := RB lbl l σ0 ∧ ∃ ini wo0, c = rdC2 l ini wo0

/-- Before the second exchange's load (`Hello1.sJ2'`). -/
def jC2' (σ0 : FAS) (c : Ctl) : Prop := RB lbl l σ0 ∧ ∃ ini wo0, c = rdC3 l ini wo0

/-- The second word held (`Hello1.sJh2`). -/
def jX3 (σ0 : FAS) (c : Ctl) : Prop :=
  RB lbl l σ0 ∧ ∃ ini wo0 w, c = { rdC3 l ini wo0 with hold := some ((bAddr σ0.regs .rax 8).toNat, w) }

/-- After the second exchange, at the publication (`Hello1.sJ4`). -/
def jC4 (σ0 : FAS) (c : Ctl) : Prop := RB lbl l σ0 ∧ ∃ ini wo0 wo1, c = rdC4 l ini wo0 wo1

/-- Right after the publication, at `let n = 13` (`rdCP_pub`'s target). -/
def jC5 (σ0 : FAS) (c : Ctl) : Prop := RB lbl l σ0 ∧ ∃ ini wo0 wo1, c = rdC5 l ini wo0 wo1

/-- After the publication, at `ret sl`. -/
def jRet (σ0 : FAS) (c : Ctl) : Prop := RB lbl l σ0 ∧ ∃ ini wo0 wo1, c = rdRet l ini wo0 wo1

variable {lbl l}

theorem bAddr0 {σ0 : FAS} (_h : RB lbl l σ0) :
    (bAddr σ0.regs .rax 0).toNat = σ0.regs.rax.toBitVec.toNat + 8 * 0 := by
  have : bAddr σ0.regs .rax 0 = σ0.regs.rax.toBitVec := by simp [bAddr, Reg64s.get64]
  rw [this]; omega

theorem bAddr8 {σ0 : FAS} (h : RB lbl l σ0) :
    (bAddr σ0.regs .rax 8).toNat = σ0.regs.rax.toBitVec.toNat + 8 * 1 := by
  have : bAddr σ0.regs .rax 8 = σ0.regs.rax.toBitVec + 8#64 := by simp [bAddr, Reg64s.get64]
  rw [this, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := h.2; omega)]

variable {p : Prog} {Jp : FAS → Ctl → Prop}

/-- **`MainWcPS.hr0`**: from `.x15` at `rdCA l ini` (`hJp`) the `asLanes` step to `rdC1`. -/
theorem hr0_rd (hJp : ∀ σ0 c, Jp σ0 c → RB lbl l σ0 ∧ ∃ ini, c = rdCA l ini) :
    ∀ σ0 c, Jp σ0 c → ∃ c', LocalRun p c c' ∧ jP' lbl l σ0 c' := by
  intro σ0 c h
  obtain ⟨hB, ini, rfl⟩ := hJp σ0 c h
  exact ⟨_, .single (rdCA_store (p := p) (ini := ini) hB.1).1, hB, ini, rfl⟩

/-- **`MainWcPS.h1`**: the first exchange's site at `%rax`, its load holding any word. -/
theorem h1_rd {rd : Word → Prop} :
    ∀ σ0 c, jP' lbl l σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : Word), rd w' → ValRep lbl w'.val (r.setWidth 64).toNat →
        jX1 lbl l σ0 { c with hold := some ((bAddr σ0.regs .rax 0).toNat, w') } := by
  rintro σ0 c ⟨hB, ini, rfl⟩
  obtain ⟨-, hx, hv, hh, -, -⟩ := rdCA_store (p := Spike.Lib.X64HelloSrc.helloSrc) (ini := ini) hB.1
  exact ⟨_, _, _, _, _, hx, by rw [bAddr0 hB]; exact hv, hh, fun _ w' _ _ => ⟨hB, ini, w', rfl⟩⟩

/-- **`MainWcPS.h2`**: the first exchange's store of `rdK1`, the old word bound, to `rdC2`. -/
theorem h2_rd :
    ∀ σ0 c, jX1 lbl l σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : Word),
      XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 0).toNat, wold) ∧ evalAt c.env v = some (tv, [wv]) ∧
      ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ jC2 lbl l σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩ := by
  rintro σ0 c ⟨hB, ini, w', rfl⟩
  obtain ⟨-, hx, hv, -, hev, hk⟩ := rdCA_store (p := Spike.Lib.X64HelloSrc.helloSrc) (ini := ini) hB.1
  refine ⟨_, _, _, _, _, _, _, w', hx, by rw [bAddr0 hB]; exact hv, rfl, hev, ?_, hB, ini, w',
    (rdC1_next l ini w').symm⟩
  rw [show (rpK1.setWidth 128).toNat = rdK1 by decide]; exact hk

/-- **`MainWcPS.hr2`**: the second `asLanes` step to `rdC3`. -/
theorem hr2_rd : ∀ σ0 c, jC2 lbl l σ0 c → ∃ c', LocalRun p c c' ∧ jC2' lbl l σ0 c' := by
  rintro σ0 c ⟨hB, ini, wo0, rfl⟩
  exact ⟨_, .single (rdC2_store (p := p) (ini := ini) (wo0 := wo0) hB.1).1, hB, ini, wo0, rfl⟩

/-- **`MainWcPS.h3`**: the second exchange's site at `%rax + 8`, its load holding any word. -/
theorem h3_rd {rd : Word → Prop} :
    ∀ σ0 c, jC2' lbl l σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : Word), rd w' → ValRep lbl w'.val (r.setWidth 64).toNat →
        jX3 lbl l σ0 { c with hold := some ((bAddr σ0.regs .rax 8).toNat, w') } := by
  rintro σ0 c ⟨hB, ini, wo0, rfl⟩
  obtain ⟨-, hx, hv, hh, -, -⟩ :=
    rdC2_store (p := Spike.Lib.X64HelloSrc.helloSrc) (ini := ini) (wo0 := wo0) hB.1
  exact ⟨_, _, _, _, _, hx, by rw [bAddr8 hB]; exact hv, hh, fun _ w' _ _ => ⟨hB, ini, wo0, w', rfl⟩⟩

/-- **`MainWcPS.h4`**: the second exchange's store of `rdK2`, the old word bound, to `rdC4`. -/
theorem h4_rd :
    ∀ σ0 c, jX3 lbl l σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : Word),
      XchgSite c x sa u v e ∧ ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 8).toNat, wold) ∧ evalAt c.env v = some (tv, [wv]) ∧
      ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ jC4 lbl l σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩ := by
  rintro σ0 c ⟨hB, ini, wo0, w', rfl⟩
  obtain ⟨-, hx, hv, -, hev, hk⟩ :=
    rdC2_store (p := Spike.Lib.X64HelloSrc.helloSrc) (ini := ini) (wo0 := wo0) hB.1
  refine ⟨_, _, _, _, _, _, _, w', hx, by rw [bAddr8 hB]; exact hv, rfl, hev, ?_, hB, ini, wo0, w',
    (rdC3_next l ini wo0 w').symm⟩
  rw [show (rpK2.setWidth 128).toNat = rdK2 by decide]; exact hk

/-- **The publication's source run**: from `jC4` (at `let s = publish b`) the publication, where the memory side
admits it (`hP`), then the local run to `ret sl`. -/
theorem hfen_rd {P : Prop} (hP : P) : ∀ σ0 c, jC4 lbl l σ0 c → ∃ c', FenceRun p P .st c c' ∧ jRet lbl l σ0 c' := by
  rintro σ0 c ⟨hB, ini, wo0, wo1, rfl⟩
  exact ⟨_, rdC4_fence hP l ini wo0 wo1, hB, ini, wo0, wo1, rfl⟩

/-- **`MainWcPS.hfen` at the rows' memory side**: `hfen_rd` at `msOfAX`'s publication, which is the arena's
(`X64SegWPub.msOfAX_pub`); wake's and hello's arena `X64.WakeOD.arW` has `pub` outright (`arW_pub`). -/
theorem hfen_msOfAX {Λ : Scc.Sem.Layout} {μ} {rd : Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.X64ConsumerS.OwnS} {ar : Spike.Lib.Arena} {I : Spike.Lib.X64ConsumerS.InvS}
    {ab : Option (State → Prop)} {lsize : Spike.Lib.X64Consumer.Lsize} {fs : List TermRun.Frame}
    (har : ar.pub) : ∀ σ0 c, jC4 lbl l σ0 c → ∃ c', FenceRun p
      (Spike.Lib.X64ConsumerA.msOfAX Λ μ p rd G own ar I ab lbl lsize fs).pub .st c c' ∧ jRet lbl l σ0 c' :=
  hfen_rd (Spike.Lib.X64SegWPub.msOfAX_pub (p := p) (lbl := lbl) ▸ har)

/-- **The publication's step is determined by its control** (the bound name, the published atom and the body
are the term's, the value its evaluation, the type `pubTy`'s or `rgnTy`'s of it). -/
theorem pubStep_det {k k' : Kraken.FenceKind} {c c₁ c₂ : Ctl} (h₁ : PubStep k c c₁) (h₂ : PubStep k' c c₂) :
    c₁ = c₂ := by
  obtain ⟨-, -, x, a, e, t, t', ws, h, ha, rfl⟩ := h₁
  obtain ⟨-, -, x', a', e', u, u', ws', h', ha', rfl⟩ := h₂
  rcases h with ⟨ht, hp⟩ | ⟨r, ht, hp⟩ <;> rcases h' with ⟨ht', hp'⟩ | ⟨r', ht', hp'⟩ <;>
    rw [ht] at ht' <;> cases ht' <;> (rw [ha] at ha'; cases ha'; rw [hp] at hp'; cases hp'; rfl)

/-- **`MainWcPS.hpubx`**: the publication from `jC4` lands in `jC5`. -/
theorem hpubx_rd : ∀ σ0 c c₁, jC4 lbl l σ0 c → PubStep .st c c₁ → jC5 lbl l σ0 c₁ := by
  rintro σ0 c c₁ ⟨hB, ini, wo0, wo1, rfl⟩ h
  exact ⟨hB, ini, wo0, wo1, (pubStep_det h (rdCP_pub l ini wo0 wo1))⟩

/-- **`MainWcPS.hlocx`**: from `jC5` the local run to `ret sl` (`jRet`). -/
theorem hlocx_rd : ∀ σ0 c, jC5 lbl l σ0 c → ∃ c', LocalRun p c c' ∧ jRet lbl l σ0 c' := by
  rintro σ0 c ⟨hB, ini, wo0, wo1, rfl⟩
  exact ⟨_, rdC5_run l ini wo0 wo1, hB, ini, wo0, wo1, rfl⟩

/-- **The return's pop at `ret sl`** (no further step): `frH env` popped lands in `JrRL lbl env l` at any state
whose `%rax`, `%rdx`, `%rcx`, `%rsi` are the slice's (`%rax` `.x15`'s base). -/
theorem hedge_rd {env : Env} :
    ∀ σ0 c, jRet lbl l σ0 c → ∀ σ' : FAS, σ'.regs.rax.toBitVec = σ0.regs.rax.toBitVec →
      σ'.regs.rdx.toBitVec = 0#64 → σ'.regs.rcx.toBitVec = 2#64 → σ'.regs.rsi.toBitVec = 13#64 →
      σ'.regs.rbp.toBitVec = σ0.slot (-8) → σ'.regs.rsp.toBitVec = σ0.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ retJH (frH env) (JrRL lbl env l) σ' c' := by
  rintro σ0 c ⟨hB, ini, wo0, wo1, rfl⟩ σ' h0 h1 h2 h3 - -
  refine ⟨_, .refl _, _, _, _, (rdRet_ret l ini wo0 wo1).1, (rdRet_ret l ini wo0 wo1).2.2, rfl, ?_, ?_, ?_, ?_⟩
  · rw [h0]; exact hB.1
  · rw [h1]; rfl
  · rw [h2]; rfl
  · rw [h3]; rfl

end Spike.Lib.X64.HelloPh.RdSrcL1

/-- info: 'Spike.Lib.X64.HelloPh.RdSrcL1.hr0_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdSrcL1.hr0_rd

/-- info: 'Spike.Lib.X64.HelloPh.RdSrcL1.h1_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdSrcL1.h1_rd

/-- info: 'Spike.Lib.X64.HelloPh.RdSrcL1.h2_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdSrcL1.h2_rd

/-- info: 'Spike.Lib.X64.HelloPh.RdSrcL1.hr2_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdSrcL1.hr2_rd

/-- info: 'Spike.Lib.X64.HelloPh.RdSrcL1.h3_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdSrcL1.h3_rd

/-- info: 'Spike.Lib.X64.HelloPh.RdSrcL1.h4_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdSrcL1.h4_rd

/-- info: 'Spike.Lib.X64.HelloPh.RdSrcL1.hfen_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdSrcL1.hfen_rd

/-- info: 'Spike.Lib.X64.HelloPh.RdSrcL1.hedge_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdSrcL1.hedge_rd

/-- info: 'Spike.Lib.X64.HelloPh.RdSrcL1.bAddr0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdSrcL1.bAddr0

/-- info: 'Spike.Lib.X64.HelloPh.RdSrcL1.bAddr8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdSrcL1.bAddr8

/-- info: 'Spike.Lib.X64.HelloPh.RdSrcL1.hfen_msOfAX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdSrcL1.hfen_msOfAX

/-- info: 'Spike.Lib.X64.HelloPh.RdSrcL1.jC5' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdSrcL1.jC5

/-- info: 'Spike.Lib.X64.HelloPh.RdSrcL1.pubStep_det' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdSrcL1.pubStep_det

/-- info: 'Spike.Lib.X64.HelloPh.RdSrcL1.hpubx_rd' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdSrcL1.hpubx_rd

/-- info: 'Spike.Lib.X64.HelloPh.RdSrcL1.hlocx_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdSrcL1.hlocx_rd
