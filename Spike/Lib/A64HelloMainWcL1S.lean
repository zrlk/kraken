/-
**`MainWcPS.hW.sp0` at rodata's own label** (AArch64, `Level1I`'s `hP` stage 2): `scc_rt_main`'s `.sp0` block `mB1`
(the call of `wc_main`) inside `WSHF … []`, at `wc_rodata`'s
return invariant `JrT (JrRL lbl env l) t R'` (the wrapper's continuation `setupCont` with `r` bound to the slice
`slW l`, the slice in `x0`–`x3`).

The placement is state dependent (so `RdPl.hplB1_WH`'s "placed at every state" does not apply): `r`'s three words
are at `x0`, `x2`, `x3` throughout `mB1` (its stores of `x0`–`x3` keep the registers and its reloads restore them,
`mB1_regs`), and `me`'s one word is the layout's immediate at `setupCont` (`ImmsMe.hmeC_iRdM` at the root).

- `mB1_regs`: `x0`, `x2`, `x3` before each instruction of `mB1` are the entry's.
- `placed_jrRL`: the continuation is placed at `x0`, `x2`, `x3` and `me`'s immediate.
- `hplB1_L1`: `mB1W_WSHF`'s `hpl` at `JrT (JrRL …)`.
- `sp0_L1`: `MainPostSWH.sp0` (`RdWfSF.mB1W_WSHF` at `fs = []`, the controls' facts `HelloRdCf.cont_ctl`).
- `valRep_upd`: a representation survives placing a fresh label (for `hmw` at the level's labels).
- an `example`: `hplB1_L1`'s premises at the root's layout, the level's labels and `c0S.env`.
-/
import Spike.Lib.A64HelloMainWcL1W
import Spike.Lib.A64HelloMainPostT
import Spike.Lib.A64HelloJr1L
import Spike.Lib.A64HelloImmsMe
import Spike.Lib.A64HelloC0S

namespace Spike.Lib.A64.HelloPh.MainWcL1S

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (ValRep)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize Placed)
open Spike.Lib.A64ConsumerS (PlacedSE PlacedS)
open Spike.Lib.A64.Flow (BlkW leave)
open Spike.Lib.A64.HelloPh.WcW (freeNH)
open Spike.Lib.A64.HelloWf (WSHF)
open Spike.Lib.A64.Flow.Hello1 (mB1 mS0 mR)
open Spike.Lib.A64.Flow.HelloM (JrT)
open Spike.Lib.A64.Flow.HelloJr1 (JrRL)
open Spike.Lib.A64WakeMainW (M1 placeVal_x)
open Spike.Lib.WakeSrcCtl (Tbl rep_at)
open Spike.Lib.HelloRdCf (slW)
open Spike.Lib.HelloMainPreSrc (slTy)
open Spike.Lib (Arena FragS Ctl Region)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

set_option linter.unusedSimpArgs false

/-! ## `mB1` keeps `x0`, `x2`, `x3` -/

/-- **`x0`, `x2`, `x3` before each instruction of `mB1`** are the entry's: the stores keep the registers, the
reloads read back what was stored. -/
theorem mB1_regs (lab : Label → Int64) (pc : Int64) (σ : FAS) :
    ∀ k < mB1.length,
      (Spike.Lib.A64.Flow.arun lab (mB1.take k) ⟨pc, ⟨-80, []⟩, σ⟩).σ.regs.getXReg .X0 = σ.regs.getXReg .X0 ∧
      (Spike.Lib.A64.Flow.arun lab (mB1.take k) ⟨pc, ⟨-80, []⟩, σ⟩).σ.regs.getXReg .X2 = σ.regs.getXReg .X2 ∧
      (Spike.Lib.A64.Flow.arun lab (mB1.take k) ⟨pc, ⟨-80, []⟩, σ⟩).σ.regs.getXReg .X3 = σ.regs.getXReg .X3 := by
  intro k hk
  have hl : mB1.length = 10 := by decide
  rw [hl] at hk
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  rotate_left 10
  · omega
  all_goals
    simp [mB1, Spike.Lib.A64.Flow.arun, Spike.Lib.A64.Flow.dstep, Spike.Lib.A64.Flow.classify,
      Spike.Lib.A64.Flow.RegOnly, Spike.Lib.A64.Flow.AI.so,
      Spike.Lib.A64.Flow.regRes, Spike.Lib.A64.Flow.BlockSpec.AI.step_ldr',
      Spike.Lib.A64.Flow.BlockSpec.AI.step_str', Spike.Lib.A64.Flow.BlockSpec.AI.tgt_ldr',
      Spike.Lib.A64.Flow.BlockSpec.AI.tgt_str', Spike.Lib.upd_apply, Reg64s.getXReg, Reg64s.setRegOrZr,
      Reg64s.getRegOrZr, Reg64s.setXReg, Reg64s.setRegOrZr64, Reg64s.getRegOrZr64, RegOrZr.base, RegOrSp.base,
      Spike.Lib.A64.Flow.SO.get, Spike.Lib.A64.Flow.SO.set, Spike.Lib.A64.Flow.SO.kill,
      Spike.Lib.A64.Flow.SO.write, Spike.Lib.A64.Flow.SO.killZ]

/-! ## The continuation's placement -/

section Pl

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {env : TermRun.Env} {l : WeakMem.AllocLabel}

/-- **The wrapper's continuation on the slice at `l` is placed**: `r`'s words at `x0` (`l`'s place), `x2` (`2`),
`x3` (`13`); `me`'s one word `mw` (`hme`) at the layout's immediate `n` at `setupCont` (`himm`, `hmw`). -/
theorem placed_jrRL {tm : Ty} {mw : TermRun.Word} {n : Nat}
    (hme : TermRun.lookupE env "me" = some (tm, [mw]))
    (himm : Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some n) (hmw : ValRep lbl mw.val n)
    (h0 : lbl l = some (s.st.1.regs.getXReg .X0).toBitVec.toNat)
    (h2 : (s.st.1.regs.getXReg .X2).toBitVec.toNat = 2) (h3 : (s.st.1.regs.getXReg .X3).toBitVec.toNat = 13) :
    Placed Λ lbl s ⟨Spike.Lib.SrcCalls.setupCont, ("r", slTy, slW l) :: env, none⟩ := by
  have hfv : Scc.Sem.exprFv Spike.Lib.SrcCalls.setupCont = ["r", "me"] := by decide
  have hr : ∀ ty ws, TermRun.lookupE (("r", slTy, slW l) :: env) "r" = some (ty, ws) → ws = slW l := by
    intro ty ws h; simp [TermRun.lookupE] at h; exact h.2.symm
  have hm : ∀ ty ws, TermRun.lookupE (("r", slTy, slW l) :: env) "me" = some (ty, ws) → ws = [mw] := by
    intro ty ws h
    have e : TermRun.lookupE (("r", slTy, slW l) :: env) "me" = TermRun.lookupE env "me" := by
      simp [TermRun.lookupE]
    rw [e, hme] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  refine Spike.Lib.A64.HelloPh.RdPlS.placed_of_tbl
    [("r", [.one (.reg (.x XReg.X0.idx)), .one (.reg (.x XReg.X2.idx)), .one (.reg (.x XReg.X3.idx))]),
      ("me", [.imm n])] ?_ ?_ ?_
  · intro x hx ty ws hl
    simp only [hfv, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨_, rfl, by simp [hr ty ws hl, slW]⟩
    · exact ⟨_, rfl, by simp [hm ty ws hl]⟩
  · intro x pls ty ws hpls hl k wp wd hwp hwd
    by_cases e1 : x = "r"
    · subst e1; cases hpls; rw [hr ty ws hl] at hwd
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at ⟨_, placeVal_x s .X0, h0⟩
      | 1, hwp, hwd => cases hwp; cases hwd; exact ⟨_, placeVal_x s .X2, by rw [h2]; exact ⟨by decide, rfl⟩⟩
      | 2, hwp, hwd => cases hwp; cases hwd; exact ⟨_, placeVal_x s .X3, by rw [h3]; exact ⟨by decide, rfl⟩⟩
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
  {endPc : Int64} {R R' : Region} {F : MachineData → Prop} {σC : FAS} {t : UInt64}

/-- **`mB1W_WSHF`'s `hpl` at `wc_rodata`'s return** (module doc): `mB1` from `JrT (JrRL lbl env l) t R'` is
placed at no frame, `me`'s word `mw` in `env` (`hme`) the layout's immediate at `setupCont` (`himm`, `hmw`). -/
theorem hplB1_L1 {tm : Ty} {mw : TermRun.Word} {n : Nat}
    (hme : TermRun.lookupE env "me" = some (tm, [mw]))
    (himm : Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some n) (hmw : ValRep lbl mw.val n) :
    BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F
      (mS0 (_root_.Executable.labels exe).label R σC (JrT (JrRL lbl env l) t R')) mB1 := by
  intro s σ c _ _ _ _ _ _ hJ k hk m hA _
  refine ⟨.inl (PlacedS.ofFrames ?_ Spike.Lib.A64.Flow.Hello1.SFactsN.framesPlaced_nil), fun _ h => h⟩
  obtain ⟨σx, ⟨⟨rfl, h0, -, h2, h3⟩, -, -⟩, rfl⟩ := hJ
  obtain ⟨e0, e2, e3⟩ := mB1_regs (_root_.Executable.labels exe).label
    ((_root_.Executable.labels exe).label ".L1_scc_rt_main.sp0") (leave (mR R) (-80) σC σx) k hk
  simp only [mS0] at hA
  have hr := hA.regs
  refine placed_jrRL hme himm hmw ?_ ?_ ?_
  · show lbl l = some (m.regs.getXReg .X0).toBitVec.toNat
    rw [hr, e0]; exact h0
  · show (m.regs.getXReg .X2).toBitVec.toNat = 2
    rw [hr, e2]; exact h2
  · show (m.regs.getXReg .X3).toBitVec.toNat = 13
    rw [hr, e3]; exact h3

end Sp0

section W

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Scc.Sem.Range} {R R' : Region} {F : MachineData → Prop}
  {ar : Arena} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize} {X0 : State → Prop}
  {frM : TermRun.Frame} {env : TermRun.Env} {l : WeakMem.AllocLabel} {σC : FAS} {t : UInt64}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = Spike.Lib.A64.WakePh.lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf Spike.Lib.A64.WakePh.lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

include hp hlo hΛ hlab hsite hcl hX0

/-- **`MainPostSWH.sp0` at rodata's label** (module doc): `scc_rt_main`'s `.sp0` block inside `WSHF … []` at
`wc_rodata`'s return invariant `JrT (JrRL lbl env l) t R'`, in `scc_rt_main`'s region `R`. -/
theorem sp0_L1 (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    {tm : Ty} {mw : TermRun.Word} {n : Nat} (hme : TermRun.lookupE env "me" = some (tm, [mw]))
    (himm : L.Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some n) (hmw : ValRep lbl mw.val n) :
    BlkW (WSHF L a ar Spike.Lib.HelloSrc.helloSrc Dt Cl Ctx lbl lsize frM X0 []) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (mS0 L.lab R σC (JrT (JrRL lbl env l) t R')) mB1 :=
  Spike.Lib.A64.HelloPh.RdWfSF.mB1W_WSHF (fs := []) (frM := frM) (rS := rS) hp hlo hΛ hlab hsite hcl hX0
    (.inl rfl) hR hal hRlo hhi
    (fun σ c ⟨⟨hc, _⟩, _⟩ => by
      rw [hc]
      exact ⟨fun _ => (Spike.Lib.HelloRdCf.cont_ctl _ none).1, (Spike.Lib.HelloRdCf.cont_ctl _ none).2⟩)
    (hplB1_L1 hme himm hmw)

end W

/-! ## At the root's labels -/

/-- **A value's representation survives placing a fresh label** (`L l = none`). -/
theorem valRep_upd {L : Lbl} {l : WeakMem.AllocLabel} {b : Nat} (hl : L l = none) {v : WeakMem.Val} {n : Nat}
    (h : ValRep L v n) : ValRep (Spike.Lib.A64ConsumerA.upd L l b) v n := by
  cases v with
  | loc a tag =>
    obtain ⟨ht, x, hx, rfl⟩ := h
    refine ⟨ht, x, ?_, rfl⟩
    have hne : a.label ≠ l := fun e => by
      simp only [Scc.Sem.wordAddr, e, hl, Option.map_none] at hx; cases hx
    simpa [Scc.Sem.wordAddr, Spike.Lib.A64ConsumerA.upd, hne] using hx
  | _ => exact h

/-- **Not vacuous**: `hplB1_L1`'s premises at the root's layout `ofPlaceW hp (iRdM Λ0)`, the level's labels
`upd (L0T Λ) l b` (`l` fresh) and the start's environment `c0S.env` (`me` at main's thread id, `tcb0`). -/
example {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) {l : WeakMem.AllocLabel} {b : Nat} {exe : _root_.Executable} {endPc : Int64}
    {R R' : Region} {F : MachineData → Prop} {σC : FAS} {t : UInt64}
    (hl : Spike.Lib.WakeLoadT.L0T (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp
      (Spike.Lib.A64.HelloPh.ImmsMe.iRdM Λ0)).Λ l = none) :
    let Λ := (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (Spike.Lib.A64.HelloPh.ImmsMe.iRdM Λ0)).Λ
    BlkW (fun s c => PlacedSE Λ (Spike.Lib.A64ConsumerA.upd (Spike.Lib.WakeLoadT.L0T Λ) l b) s c [])
      (fun _ _ => False) exe endPc R F
      (mS0 (_root_.Executable.labels exe).label R σC
        (JrT (JrRL (Spike.Lib.A64ConsumerA.upd (Spike.Lib.WakeLoadT.L0T Λ) l b)
          Spike.Lib.A64.HelloPh.C0S.c0S.env l) t R')) mB1 :=
  hplB1_L1 (tm := .tid) rfl (Spike.Lib.A64.HelloPh.ImmsMe.hmeC_iRdM hp)
    (valRep_upd hl (Spike.Lib.WakeImmsW.valRep_me _))

end Spike.Lib.A64.HelloPh.MainWcL1S

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1S.mB1_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1S.mB1_regs

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1S.placed_jrRL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1S.placed_jrRL

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1S.hplB1_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1S.hplB1_L1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1S.sp0_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1S.sp0_L1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1S.valRep_upd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1S.valRep_upd
