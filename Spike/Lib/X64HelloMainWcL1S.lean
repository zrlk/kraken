/-
**`MainWcPS.hW.sp0` at rodata's own label** (x86-64; the twin of `Spike/Lib/A64HelloMainWcL1S.lean`):
`scc_rt_main`'s `.x2` block `mB1` (the call of `wc_main`) inside `WSHF … []`, at `wc_rodata`'s return invariant
`JrT (JrRL lbl env l) t R'` (the wrapper's continuation `setupCont` with `r` bound to the slice `slW l`, the slice
in `%rax`, `%rcx`, `%rsi`).

The placement is state dependent (so "placed at every state" does not apply): `r`'s three words are at `%rax`,
`%rcx`, `%rsi` before `mB1`'s sixth instruction, and at the cells `-24`, `-40`, `-48` (`-16(%rbp)`, `-32(%rbp)`,
`-40(%rbp)`) from its fifth on (`mB1_regs`), and `me`'s one word is the layout's immediate at `setupCont`
(`HelloImms.hmeC_iRdM` at the root).

- `mB1_regs`: `%rax`, `%rcx`, `%rsi` before each of `mB1`'s first six instructions are the entry's, and the cells
  `-24`, `-40`, `-48` hold them from the fifth on.
- `placed_jrRL`: the continuation is placed at any three places holding the slice and `me`'s immediate.
- `hplB1_L1`: `mB1W_WSHF`'s `hpl` at `JrT (JrRL …)`.
- `sp0_L1`: `MainPostS`'s `sp0` (`RdWfSF.mB1W_WSHF` at `fs = []`, the controls' facts `HelloRdCf.cont_ctl`).
- `valRep_upd`: a representation survives placing a fresh label (for `hmw` at the level's labels).
- an `example`: `hplB1_L1`'s premises at the root's layout, the level's labels and `c0S.env`.

## Differences from the AArch64 version

- `wc_rodata` returns the slice in `%rax`, `%rdx`, `%rcx`, `%rsi` (`Jr1.SlRegs`; AArch64 `x0`–`x3`), `r`'s words
  being at `%rax`, `%rcx`, `%rsi`. `mB1` moves them into `wc_main`'s argument registers through the frame, and its
  sixth load overwrites `%rsi` (and its eighth `%rcx`), so the slice is placed at the registers before the sixth
  instruction and at the cells `-24`, `-40`, `-48` after the fourth store (AArch64: at `x0`, `x2`, `x3`
  throughout). `mB1_regs` states both, and `placed_jrRL` takes the three places as parameters.
- `hplB1_L1` takes the region's bounds `R.lo ≤ -48`, `-16 ≤ R.hi` (the three cells are offsets of `R`); `sp0_L1`
  takes `mB1W_WSHF`'s (`-288`, `8`; AArch64 `-80`, `0` and `hal`).
- The root's layout is `ofPlaceWX hp (iRdM Λ0)` (`HelloImms`; AArch64 `ImmsMe`).
-/
import Spike.Lib.X64HelloMainPostT
import Spike.Lib.X64HelloJr1L
import Spike.Lib.X64HelloRdPostWfSF
import Spike.Lib.X64HelloRdPlS
import Spike.Lib.X64HelloImms
import Spike.Lib.X64HelloC0S

namespace Spike.Lib.X64.HelloPh.MainWcL1S

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (ValRep Place placeVal)
open Scc.Sem.X64 (codeLabel pcOf)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize Placed)
open Spike.Lib.X64ConsumerS (PlacedSE PlacedS)
open Spike.Lib.X64 (AS BlkW arun leave)
open Spike.Lib.X64.HelloPh.WcW (freeNH)
open Spike.Lib.X64.HelloWf (WSHF)
open Spike.Lib.X64.Flow.Hello1 (mB1 mO mS0 mR)
open Spike.Lib.X64.Flow.HelloM (JrT)
open Spike.Lib.X64.Flow.HelloJr1 (JrRL)
open Spike.Lib.X64WakeMainW (M1 placeVal_reg)
open Spike.Lib.X64.WakeSrcCtl (Tbl rep_at placeVal_slot_abs)
open Spike.Lib.X64HelloRdCf (slW)
open Spike.Lib.X64HelloSplit (slTy)
open Spike.Lib (Arena FragS Ctl Region)

set_option linter.unusedSimpArgs false

/-- The abstract run's simp set over `mB1` (`X64HelloHAbW`'s). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Spike.Lib.X64.arun, Spike.Lib.X64.dstep, Spike.Lib.X64.classify, Spike.Lib.X64.RegOnly,
    Spike.Lib.X64.AI.so, Spike.Lib.X64.soReg, Spike.Lib.X64.regDst, Spike.Lib.X64.regRes, Operation.interp,
    Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp,
    AddrExpr.interp, Spike.Lib.X64.SO.get, Spike.Lib.X64.SO.set, Spike.Lib.X64.SO.kill, Spike.Lib.X64.SO.write,
    Spike.Lib.lk, Spike.Lib.rm, Reg.base,
    Spike.Lib.upd_apply, Reg64s.get_low64, Spike.Lib.X64.BlockSpec.AI.step_ld',
    Spike.Lib.X64.BlockSpec.AI.step_st', Spike.Lib.X64.BlockSpec.AI.step_push',
    Spike.Lib.X64.BlockSpec.AI.step_pop', Spike.Lib.X64.BlockSpec.AI.step_reg',
    Spike.Lib.X64.BlockSpec.AI.step_jmp', Spike.Lib.X64.BlockSpec.AI.step_jcc',
    Spike.Lib.X64.BlockSpec.AI.tgt_jmp', Spike.Lib.X64.BlockSpec.AI.tgt_jcc',
    Spike.Lib.X64.BlockSpec.AI.tgt_ld', Spike.Lib.X64.BlockSpec.AI.tgt_st',
    Spike.Lib.X64.BlockSpec.AI.tgt_push', Spike.Lib.X64.BlockSpec.AI.tgt_pop',
    Spike.Lib.X64.BlockSpec.AI.tgt_reg'])

/-! ## `mB1` keeps the slice -/

/-- **The slice through `mB1`**: `%rax` before each instruction is the entry's, `%rcx` and `%rsi` before each of
the first six; the cells `-24`, `-40`, `-48` (`-16(%rbp)`, `-32(%rbp)`, `-40(%rbp)`) hold the entry's `%rax`,
`%rcx`, `%rsi` after the four stores. -/
theorem mB1_regs (lab : String → Int64) (pc : Int64) (σ : AS) :
    ∀ k < mB1.length,
      (arun lab (mB1.take k) ⟨pc, mO, σ⟩).σ.regs.rax = σ.regs.rax ∧
      (k ≤ 5 → (arun lab (mB1.take k) ⟨pc, mO, σ⟩).σ.regs.rcx = σ.regs.rcx ∧
        (arun lab (mB1.take k) ⟨pc, mO, σ⟩).σ.regs.rsi = σ.regs.rsi) ∧
      (4 ≤ k → (arun lab (mB1.take k) ⟨pc, mO, σ⟩).σ.slot (-24) = σ.regs.rax.toBitVec ∧
        (arun lab (mB1.take k) ⟨pc, mO, σ⟩).σ.slot (-40) = σ.regs.rcx.toBitVec ∧
        (arun lab (mB1.take k) ⟨pc, mO, σ⟩).σ.slot (-48) = σ.regs.rsi.toBitVec) := by
  intro k hk
  have hl : mB1.length = 10 := by decide
  rw [hl] at hk
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  rotate_left 10
  · omega
  all_goals simp [mB1]
  all_goals arun_simp

/-! ## The continuation's placement -/

section Pl

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {env : TermRun.Env} {l : WeakMem.AllocLabel}

/-- **The wrapper's continuation on the slice at `l` is placed**: `r`'s words at `p0` (`l`'s place), `p1` (`2`),
`p2` (`13`); `me`'s one word `mw` (`hme`) at the layout's immediate `n` at `setupCont` (`himm`, `hmw`). -/
theorem placed_jrRL {tm : Ty} {mw : TermRun.Word} {n : Nat} {p0 p1 p2 : Place M1.I.RegId}
    (hme : TermRun.lookupE env "me" = some (tm, [mw]))
    (himm : Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some n) (hmw : ValRep lbl mw.val n)
    (h0 : ∃ v, placeVal M1 s p0 = some v ∧ lbl l = some v)
    (h1 : placeVal M1 s p1 = some 2) (h2 : placeVal M1 s p2 = some 13) :
    Placed Λ lbl s ⟨Spike.Lib.SrcCalls.setupCont, ("r", slTy, slW l) :: env, none⟩ := by
  have hfv : Scc.Sem.exprFv Spike.Lib.SrcCalls.setupCont = ["r", "me"] := by decide
  have hr : ∀ ty ws, TermRun.lookupE (("r", slTy, slW l) :: env) "r" = some (ty, ws) → ws = slW l := by
    intro ty ws h; simp [TermRun.lookupE] at h; exact h.2.symm
  have hm : ∀ ty ws, TermRun.lookupE (("r", slTy, slW l) :: env) "me" = some (ty, ws) → ws = [mw] := by
    intro ty ws h
    have e : TermRun.lookupE (("r", slTy, slW l) :: env) "me" = TermRun.lookupE env "me" := by
      simp [TermRun.lookupE]
    rw [e, hme] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  refine Spike.Lib.X64.HelloPh.RdPlS.placed_of_tbl
    [("r", [.one p0, .one p1, .one p2]), ("me", [.imm n])] ?_ ?_ ?_
  · intro x hx ty ws hl
    simp only [hfv, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨_, rfl, by simp [hr ty ws hl, slW]⟩
    · exact ⟨_, rfl, by simp [hm ty ws hl]⟩
  · intro x pls ty ws hpls hl k wp wd hwp hwd
    by_cases e1 : x = "r"
    · subst e1; cases hpls; rw [hr ty ws hl] at hwd
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at h0
      | 1, hwp, hwd => cases hwp; cases hwd; exact ⟨_, h1, by decide, rfl⟩
      | 2, hwp, hwd => cases hwp; cases hwd; exact ⟨_, h2, by decide, rfl⟩
      | _ + 3, hwp, _ => simp at hwp
    by_cases e2 : x = "me"
    · subst e2; cases hpls; rw [hm ty ws hl] at hwd
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact hmw
      | _ + 1, hwp, _ => simp at hwp
    · simp [List.lookup, beq_false_of_ne e1, beq_false_of_ne e2] at hpls
  · intro x hx pls k n' hpls hn
    simp only [hfv, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> cases hpls
    · match k, hn with
      | 0, hn => cases hn
      | 1, hn => cases hn
      | 2, hn => cases hn
      | _ + 3, hn => simp at hn
    · match k, hn with
      | 0, hn => cases hn; exact himm
      | _ + 1, hn => simp at hn

end Pl

/-! ## `hW.sp0` -/

section Sp0

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {env : TermRun.Env} {l : WeakMem.AllocLabel} {exe : _root_.Executable}
  {endPc : Int64} {R R' : Region} {F : MachineData → Prop} {σC : AS} {t : UInt64}

/-- **`mB1W_WSHF`'s `hpl` at `wc_rodata`'s return** (module doc): `mB1` from `JrT (JrRL lbl env l) t R'` is
placed at no frame, the slice at the registers before the sixth instruction and at the cells after the fourth,
`me`'s word `mw` in `env` (`hme`) the layout's immediate at `setupCont` (`himm`, `hmw`). -/
theorem hplB1_L1 (hRlo : R.lo ≤ -48) (hhi : -16 ≤ R.hi) {tm : Ty} {mw : TermRun.Word} {n : Nat}
    (hme : TermRun.lookupE env "me" = some (tm, [mw]))
    (himm : Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some n) (hmw : ValRep lbl mw.val n) :
    BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F
      (mS0 (_root_.Executable.labels exe).label R σC (JrT (JrRL lbl env l) t R')) mB1 := by
  intro s σ c _ _ _ _ _ _ hJ k hk m hA _
  refine ⟨.inl (PlacedS.ofFrames ?_ Spike.Lib.X64.Flow.Hello1.SFactsN.framesPlaced_nil), fun _ h => h⟩
  obtain ⟨σx, ⟨⟨rfl, h0, -, h2, h3⟩, -⟩, rfl⟩ := hJ
  obtain ⟨e0, er, es⟩ := mB1_regs (_root_.Executable.labels exe).label
    ((_root_.Executable.labels exe).label ".Lscc_rt_main.x2") (leave (mR R) (-80) σC σx) k hk
  simp only [mS0] at hA
  have hr := hA.regs
  by_cases hk5 : k ≤ 5
  · obtain ⟨e2, e3⟩ := er hk5
    refine placed_jrRL (p0 := .reg (.r .rax)) (p1 := .reg (.r .rcx)) (p2 := .reg (.r .rsi)) hme himm hmw
      ⟨_, placeVal_reg _ _, ?_⟩ ?_ ?_
    · show lbl l = some (m.regs.rax.toBitVec.toNat)
      rw [hr, e0]; exact h0
    · show some (m.regs.rcx.toBitVec.toNat) = some 2
      rw [hr, e2]; exact congrArg some h2
    · show some (m.regs.rsi.toBitVec.toNat) = some 13
      rw [hr, e3]; exact congrArg some h3
  · obtain ⟨f0, f2, f3⟩ := es (by omega)
    have hoff : ∀ j : Int, j % 8 = 0 → -48 ≤ j → j ≤ -24 → R.Off j := fun j h8 h1 h2 =>
      ⟨h8, by omega, by omega⟩
    refine placed_jrRL (p0 := .slot (R.addr (-24)).toNat) (p1 := .slot (R.addr (-40)).toNat)
      (p2 := .slot (R.addr (-48)).toNat) hme himm hmw
      ⟨_, placeVal_slot_abs (s := { s with st := (m, _) }) hA (hoff _ rfl (by decide) (by decide)), ?_⟩
      ?_ ?_
    · rw [f0]; exact h0
    · rw [placeVal_slot_abs (s := { s with st := (m, _) }) hA (hoff _ rfl (by decide) (by decide)), f2]
      exact congrArg some h2
    · rw [placeVal_slot_abs (s := { s with st := (m, _) }) hA (hoff _ rfl (by decide) (by decide)), f3]
      exact congrArg some h3

end Sp0

section W

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Scc.Sem.Range} {R R' : Region} {F : MachineData → Prop}
  {ar : Arena} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} {X0 : State → Prop}
  {frM : TermRun.Frame} {env : TermRun.Env} {l : WeakMem.AllocLabel} {σC : AS} {t : UInt64}
  (hp : L.prog = SccCode.helloCells) (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo SccCode.helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → Scc.Sem.X64.abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
      some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

include hp hlo hΛ hlab hsite hcl hX0

/-- **`MainPostS`'s `sp0` at rodata's label** (module doc): `scc_rt_main`'s `.x2` block inside `WSHF … []` at
`wc_rodata`'s return invariant `JrT (JrRL lbl env l) t R'`, in `scc_rt_main`'s region `R`. -/
theorem sp0_L1 (hR : R.OK) (hRlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    {tm : Ty} {mw : TermRun.Word} {n : Nat} (hme : TermRun.lookupE env "me" = some (tm, [mw]))
    (himm : L.Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some n) (hmw : ValRep lbl mw.val n) :
    BlkW (WSHF L a ar Spike.Lib.X64HelloSrc.helloSrc Dt Cl Ctx lbl lsize frM X0 []) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (mS0 L.lab R σC (JrT (JrRL lbl env l) t R')) mB1 :=
  Spike.Lib.X64.HelloPh.RdWfSF.mB1W_WSHF (fs := []) (frM := frM) (rS := rS) hp hlo hΛ hlab hsite hcl hX0
    (.inl rfl) hR hRlo hhi
    (fun σ c ⟨⟨hc, _⟩, _⟩ => by
      rw [hc]
      exact ⟨fun _ => (Spike.Lib.X64HelloRdCf.cont_ctl _ none).1, (Spike.Lib.X64HelloRdCf.cont_ctl _ none).2⟩)
    (hplB1_L1 (by omega) (by omega) hme himm hmw)

end W

/-! ## At the root's labels -/

/-- **A value's representation survives placing a fresh label** (`L l = none`). -/
theorem valRep_upd {L : Lbl} {l : WeakMem.AllocLabel} {b : Nat} (hl : L l = none) {v : WeakMem.Val} {n : Nat}
    (h : ValRep L v n) : ValRep (Spike.Lib.X64ConsumerA.upd L l b) v n := by
  cases v with
  | loc a tag =>
    obtain ⟨ht, x, hx, rfl⟩ := h
    refine ⟨ht, x, ?_, rfl⟩
    have hne : a.label ≠ l := fun e => by
      simp only [Scc.Sem.wordAddr, e, hl, Option.map_none] at hx; cases hx
    simpa [Scc.Sem.wordAddr, Spike.Lib.X64ConsumerA.upd, hne] using hx
  | _ => exact h

/-- **Not vacuous**: `hplB1_L1`'s premises at the root's layout `ofPlaceWX hp (iRdM Λ0)`, the level's labels
`upd (L0T Λ) l b` (`l` fresh) and the start's environment `c0S.env` (`me` at main's thread id, `tcb0`). -/
example {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : Spike.Lib.PlaceWX pcfg Λ0 o) {l : WeakMem.AllocLabel} {b : Nat} {exe : _root_.Executable}
    {endPc : Int64} {R R' : Region} {F : MachineData → Prop} {σC : AS} {t : UInt64}
    (hRlo : R.lo ≤ -48) (hhi : -16 ≤ R.hi)
    (hl : Spike.Lib.X64WakeLoadT.L0T (RuntimeLayout.ofPlaceWX hp (Spike.Lib.X64.HelloImms.iRdM Λ0)).Λ l = none) :
    let Λ := (RuntimeLayout.ofPlaceWX hp (Spike.Lib.X64.HelloImms.iRdM Λ0)).Λ
    BlkW (fun s c => PlacedSE Λ (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T Λ) l b) s c [])
      (fun _ _ => False) exe endPc R F
      (mS0 (_root_.Executable.labels exe).label R σC
        (JrT (JrRL (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T Λ) l b)
          Spike.Lib.X64.HelloPh.C0S.c0S.env l) t R')) mB1 :=
  hplB1_L1 hRlo hhi (tm := .tid) rfl (Spike.Lib.X64.HelloImms.hmeC_iRdM hp)
    (valRep_upd hl (Spike.Lib.X64.WakeImmsC0.valRep_me _))

end Spike.Lib.X64.HelloPh.MainWcL1S

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1S.mB1_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1S.mB1_regs

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1S.placed_jrRL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1S.placed_jrRL

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1S.hplB1_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1S.hplB1_L1

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1S.sp0_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1S.sp0_L1

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1S.valRep_upd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1S.valRep_upd
