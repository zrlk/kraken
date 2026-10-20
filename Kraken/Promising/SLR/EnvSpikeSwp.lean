/-
Prototype: one SLR cell of the SWP worker obtained from an
environment judgment.

`wp_ldr_c_env` re-proves `SwpInv.wp_ldr_c` (`CellWP` at position 10, the
counter load `ldr w5, [x1]`) as

1. `exec_treeJ_of_instrStepEnv` at `TreeJ.eraseWPR` (generic: turns an
   `instrStepEnv (SLREnv …)` step of the machine state into the cell's
   `EvTree.EraseWPR` obligation), then
2. `instrStepEnv_ldr_c` (generic in the environment: what `vcgen`'s
   `ldr_env_spec` VC is, `env.ok ∧ ∀ v g', env.step → Q`, stated for one
   step), then
3. the VC in `SLREnv`, which `simp` reads as "every `readSuccs` outcome", and
   the semantic part of `wp_ldr_c` verbatim.

No `SwpTrees.exec_ldr_c` and no `eraseWPR_load`: the event tree of the
promising interpretation is never computed.
-/
import Kraken.Promising.SLR.SwpStore
import Kraken.Promising.SLR.EnvSpikeA64

namespace Kraken.Promising.SLR.SwpInv.EnvSpike

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SwpTrees
open Kraken.Promising.SLR.EnvSpike Kraken.Promising.AArch64.EnvSpike

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

/-- **The counter load, one environment step** (any environment): the
machine-level step of `ldr w5, [x1]` at position 10 from the VC of
`ldr_env_spec` (`X1` unmapped in `dmem`). -/
theorem instrStepEnv_ldr_c {E : SharedEnv} {st : MachineState} (hpc : st.2 = (layout swpWorker).addrOf 10)
    {cc : BitVec 64} (hx1 : st.1.regs.X1.toBitVec = cc) (hdc : Mem.loadInt st.1.dmem cc 4 = none)
    {g : E.State} {R : MachineState × E.State → Prop} (hok : E.ok (.load .plain false cc 4) g)
    (hstep : ∀ v g', E.step (.load .plain false cc 4) g v g' →
      R (({ st.1 with regs := st.1.regs.setXReg .X5 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) },
        (layout swpWorker).addrOf 11), g')) :
    (layout swpWorker).instrStepEnv E (st, g) R := by
  have hc := Kraken.Executable.codeAt_addrOf (p := swpWorker) (i := 10) (d := swpWorker[10]) (by decide)
    (by decide)
  rw [← hpc] at hc
  refine ⟨_, _, _, hc, .inl ?_⟩
  rw [addrOf_step (i := 10) (by decide), ← hpc] at hstep
  simp [swpWorker, Directive.interp, Instr.interp, Operation.interp, Effects.AllEnv,
    MachineData.load, AddrOrLit.interpLoad, AddrExpr.interpLoad,
    AddrExpr.checkSPAlignment, AddrExpr.eval, MachineData.setRegOrZr, Reg64s.getRegOrSp,
    Reg64s.getRegOrSp64, RegOrSp.base, Reg64s.getXReg, hx1, hdc]
  exact ⟨hok, hstep⟩

/-- The worker's ghost plan: only the unlock (`stlr wzr`, a store of `0` to the
lock) is a release with slots; it hands over the counter. (The counter load
does not consult the plan; the split is the `stlr` cell's business and is
left trivial here.) -/
def swpPlan (P : Params) : Plan where
  rel l v := decide (l = P.Lk ∧ v = 0)
  split r _ _ _ _ _ := (r, Res.unit)

/-- **The counter load from the environment** (`wp_ldr_c`, re-proved): the
generic link step at `TreeJ.eraseWPR`, the generic one-step VC of the load,
and the VC in `SLREnv` discharged by `wp_ldr_c`'s own argument. -/
theorem wp_ldr_c_env {P : Params} {A : Arch} {tid : Nat} : CellWP P A tid 10 := by
  intro cl c r g g₀ rF t tree hW ht hF hL hp hph hg₀ hex E hM hWf hpd
  have hn := lt_size_of_get? ht
  have hx3 := hF.x3_at hp (by decide)
  -- (1) the generic link: the cell is one `instrStepEnv (SLREnv …)` step
  refine exec_treeJ_of_instrStepEnv
    (TreeJ.eraseWPR (A := A) (tid := tid) (iv := instrViews t (isa.deps t.st)) (rF := rF) (c := c) (t := t)
      (swpPlan P) hn
      (fun st s => WpPostR (Inv P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t
        st s.1 s.2.1 s.2.2))
    (g := (r, g, ctx₀ t tid c.mem))
    (R := fun x => WpPostR (Inv P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t
      { t.st with st := x.1 } x.2.1 x.2.2.1 x.2.2.2)
    hF.exe hF.decls ?_ (fun _ _ h => h) tree hex
  -- (2) the one-step VC of `ldr` (what `vcgen` produces)
  refine instrStepEnv_ldr_c hp hF.x1 hF.dc trivial ?_
  -- (3) the VC in `SLREnv`: every `readSuccs` outcome; `wp_ldr_c`'s argument from here
  rintro v ⟨r', g', cx'⟩ ⟨rfl, rfl, tr₀, hx⟩
  simp only at hx ⊢
  simp only [Phase] at hph
  obtain ⟨S, k, hh, hm⟩ := hph
  obtain ⟨hmem, hpr⟩ := readSuccs_memProm A _ hx
  obtain ⟨tr, val, heq, -, hrd, hwi, hnp⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  refine WpPostR.noWrite hmem hpr fun t' hst _ hv => ?_
  refine inv_withThread (i := 11) hW ht hst (hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl)
    hL rfl ?_
  simp only [Phase]
  refine ⟨S, k, hh, fun ⟨hcl, E'⟩ => ?_⟩
  obtain ⟨hlk, hgood | hsur⟩ := hm hcl
  · obtain ⟨ts, ⟨⟨hX, hmax⟩, hkS⟩, hts⟩ := hgood
    have hvr : t.views.vrNew ≤ readPre A (instrViews t (isa.deps t.st)) (ctx₀ t tid c.mem) .plain :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    obtain ⟨rfl, rfl⟩ := read_max E' ht hh.1 hX hmax hrd hnp hwi
      (Nat.le_trans hts (Nat.le_trans hvr (Nat.le_max_left _ _)))
    refine ⟨hlk, .inl ⟨tr₀, ⟨⟨hX, hmax⟩, hkS⟩, ?_, ?_⟩⟩
    · have hc : t'.views.coh = (readNext A (instrViews t (isa.deps t.st)) (ctx₀ t tid c.mem) .plain false P.C
          false tr₀ (BitVec.ofNat 128 k)).views.coh := by simpa using congrArg Views.coh hv
      have : t'.views.getCoh P.C = Views.getCoh (readNext A (instrViews t (isa.deps t.st)) (ctx₀ t tid c.mem)
          .plain false P.C false tr₀ (BitVec.ofNat 128 k)).views P.C := by unfold Views.getCoh; rw [hc]
      rw [this]
      simp only [readNext]
      refine Nat.le_trans ?_ (Nat.le_of_eq (Views.getCoh_setCoh t.views P.C P.C _).symm)
      simp only [↓reduceIte]
      exact Nat.le_trans hts (Nat.le_trans hvr (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
    · simp only [Reg64s.setXReg]
      apply BitVec.eq_of_toNat_eq
      simp
  · exact ⟨hlk, .inr hsur⟩

/-- **The counter store, one environment step** (any environment): the
machine-level step of `str w5, [x1]` at position 12 from the VC of
`str_env_spec`. -/
theorem instrStepEnv_str_c {E : SharedEnv} {st : MachineState} (hpc : st.2 = (layout swpWorker).addrOf 12)
    {cc : BitVec 64} (hx1 : st.1.regs.X1.toBitVec = cc) (hdc : Mem.loadInt st.1.dmem cc 4 = none)
    {g : E.State} {R : MachineState × E.State → Prop}
    (hok : E.ok (.store .plain false cc 4 (BitVec.setWidth 128 (BitVec.setWidth 32 st.1.regs.X5.toBitVec))) g)
    (hstep : ∀ b g', E.step (.store .plain false cc 4 (BitVec.setWidth 128 (BitVec.setWidth 32 st.1.regs.X5.toBitVec)))
      g b g' → R ((st.1, (layout swpWorker).addrOf 13), g')) :
    (layout swpWorker).instrStepEnv E (st, g) R := by
  have hc := Kraken.Executable.codeAt_addrOf (p := swpWorker) (i := 12) (d := swpWorker[12]) (by decide)
    (by decide)
  rw [← hpc] at hc
  refine ⟨_, _, _, hc, .inl ?_⟩
  rw [addrOf_step (i := 12) (by decide), ← hpc] at hstep
  simp [swpWorker, Directive.interp, Instr.interp, Operation.interp, Effects.AllEnv,
    MachineData.store, AddrExpr.interpStore,
    AddrExpr.checkSPAlignment, AddrExpr.eval, Reg64s.getRegOrSp,
    Reg64s.getRegOrSp64, RegOrSp.base, Reg64s.getXReg, hx1, hdc]
  exact ⟨hok, hstep false, hstep true⟩

/-- **The counter store from the environment** (`wp_str_c`, re-proved): the
`SLREnv` store with the plan's "pure" mode (the counter is not a release
location); the two outcomes of the environment step are `wp_str_c`'s two
branches (`eraseWPR_store_pure`'s pending and appending cases). -/
theorem wp_str_c_env {P : Params} {A : Arch} {tid : Nat} (hne : P.c ≠ P.l) (hN32 : P.N < 2 ^ 32)
    (hA : A.storeKind .plain ≠ .nt) : CellWP P A tid 12 := by
  intro cl c r g g₀ rF t tree hW ht hF hL hp hph hg₀ hex E hM hWf hpd
  have hn := lt_size_of_get? ht
  have hnd : t.prom.Nodup := hM.promNodup tid t ht
  have hCL : P.Lk ≠ P.C := fun h => hne (by simp [Params.Lk, Params.C] at h; exact h.symm)
  have hx3 := hF.x3_at hp (by decide)
  simp only [Phase] at hph
  obtain ⟨S, k, hh, hm⟩ := hph
  have hq : (r.wr P.C).q = 1 := hh.1
  have hk : k = ((List.range P.N).filter S).length → k + 1 < 2 ^ 32 := fun hk =>
    Nat.lt_of_le_of_lt (hk ▸ count_lt hh) hN32
  have hrel : ∀ v, (swpPlan P).rel P.C v = false := fun v => by
    simp only [swpPlan, decide_eq_false_iff_not, not_and]
    exact fun h => absurd h.symm hCL
  -- (1) the generic link
  refine exec_treeJ_of_instrStepEnv
    (TreeJ.eraseWPR (A := A) (tid := tid) (iv := instrViews t (isa.deps t.st)) (rF := rF) (c := c) (t := t)
      (swpPlan P) hn
      (fun st s => WpPostR (Inv P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t
        st s.1 s.2.1 s.2.2))
    (g := (r, g, ctx₀ t tid c.mem))
    (R := fun x => WpPostR (Inv P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t
      { t.st with st := x.1 } x.2.1 x.2.2.1 x.2.2.2)
    hF.exe hF.decls ?_ (fun _ _ h => h) tree hex
  -- (2) the one-step VC of `str`; `ok`: the pure mode of the plan
  refine instrStepEnv_str_c hp hF.x1 hF.dc
    ⟨rfl, by show 0 < (r.wr P.C).q; rw [hq]; decide, fun _ => hW.2.1 _, fun h => absurd h (by rw [hrel]; decide)⟩ ?_
  -- (3) the two outcomes
  rintro b ⟨r', g', cx'⟩ ⟨rfl, tw, hc, hev, ⟨hpd', hr, hg⟩ | ⟨hpd', ss, -, hafter⟩⟩
  · -- a pending promise of `C` is fulfilled: impossible under the clean flag
    simp only at hc hev hpd' hr hg ⊢
    subst r' g'
    have hget : c.mem.get? tw = some ⟨P.C, BitVec.setWidth 128 (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec), tid⟩ ∧ tw ∈ t.prom ∧ cx'.mem = c.mem := by
      rcases hev.cases with ⟨hm', htw, hg⟩ | ⟨-, rfl⟩
      · exact ⟨hg, htw, hm'⟩
      · obtain ⟨⟨w, hw⟩, -⟩ := E.pend _ hpd'
        exact absurd (Memory.last_le_of_get?_eq_some _ hw) (Nat.not_succ_le_self _)
    obtain ⟨hget, htw, hmem⟩ := hget
    have hcoh : t.views.getCoh P.C < tw :=
      Nat.lt_of_le_of_lt (Nat.le_max_right _ _) (writeSuccs_tw hnd hc hev).1.1
    refine ⟨⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩, fun ts hts hor => ?_,
      fun ts h => (mem_unpend_pend.mp h).1, fun _ h => h, fun w hw => ?_, fun t' ht' _ => ?_⟩
    · refine mem_unpend_pend.mpr ⟨hts, fun he => ?_⟩
      subst he
      rcases hor with h | ⟨i, t'', hi, hti, hpr⟩
      · rw [hev.prom] at h
        exact ((List.Nodup.mem_erase_iff hnd).mp h).1 rfl
      · obtain ⟨w, hw, hwt⟩ := hM.promWf i t'' hti _ hpr
        rw [hget] at hw
        cases hw
        exact hi hwt.symm
    · rw [writtenCx_writeEv hev hw]; show 0 < (r.wr P.C).q; rw [hq]; decide
    · obtain ⟨hpr, hvs⟩ := finishInstr_relKey ht'
      refine inv_withThread_mem (i := 13) hW ht (finishInstr_st ht') (hF.goto rfl rfl rfl)
        (by rw [hmem]; exact hL) rfl ?_ (fun _ h => absurd (hq.symm.trans h) (by decide))
      simp only [Phase]
      refine .inl ⟨S, k, hh, fun ⟨hcl, E'⟩ => ?_⟩
      obtain ⟨hlk, hgood | hsur⟩ := hm hcl
      · exfalso
        obtain ⟨ts, ⟨⟨-, hmax⟩, -⟩, hts, -⟩ := hgood
        have hX : ((total (setRes rF tid r) g c).wr P.C).X (_, tw) :=
          (E'.writes P.C (.inr ⟨tw, _, hget, rfl, .inr hpd'⟩) _).mpr (.inr ⟨_, hget, rfl, rfl, .inr hpd'⟩)
        have hq' : ((setRes rF tid r tid).wr P.C).q = 1 := by rw [setRes_self]; exact hq
        obtain ⟨hth, hsl⟩ := E'.unique_holder hn hq'
        rcases X_total_cases hX with ⟨j, hj, hXj⟩ | ⟨s, hs, hXs⟩
        · by_cases hjt : j = tid
          · subst hjt
            rw [setRes_self] at hXj
            exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans (hmax _ hXj) hts) hcoh)
          · exact ((setRes rF tid r j).wr P.C).zero (hth j hj hjt) _ hXj
        · exact (s.res.wr P.C).zero (hsl s hs) _ hXs
      · exact ⟨hlk, .inr hsur⟩
  · -- the write enters `C`'s write set
    simp only [Plan.after, hrel, Bool.false_eq_true, ite_false, Prod.mk.injEq] at hafter hc hev hpd' ⊢
    obtain ⟨hr, hg⟩ := hafter
    subst r' g'
    obtain ⟨hok, hvw⟩ := writeSuccs_tw hnd hc hev
    have hcoh : t.views.getCoh P.C < tw := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hok.1
    rw [storeGhost_plain]
    refine ⟨Ghost.Le.refl g, fun ts h _ => h, fun ts h => h, fun x h => ?_, fun w hw => ?_, fun t' ht' _ => ?_⟩
    · simpa only [mayWrite, Res.addW_q, Res.addW_acq] using h
    · rw [writtenCx_writeEv hev hw]; show 0 < (r.wr P.C).q; rw [hq]; decide
    · obtain ⟨hpr, hvs⟩ := finishInstr_relKey ht'
      have hvw' : t'.views.vwOld = cx'.views.vwOld := by simpa using congrArg Views.vwOld hvs
      refine inv_withThread_mem (i := 13) hW ht (finishInstr_st ht') (hF.goto rfl rfl rfl) ?_ rfl ?_
        (fun _ h => absurd ((Res.addW_q _ _ _ _).symm.trans h) (by rw [hq]; decide))
      · intro p hp'
        rw [Res.addW_wr_ne _ _ hCL] at hp'
        exact Nat.le_trans (hL p hp') hev.last_le
      simp only [Phase]
      refine .inl ⟨S, k, ?_, fun ⟨hcl, _⟩ => ?_⟩
      · simpa only [Holding, Res.addW_q] using hh
      obtain ⟨hlk, hgood | hsur⟩ := hm hcl
      · obtain ⟨ts, ⟨⟨-, hmax⟩, hkS⟩, hts, hx5⟩ := hgood
        refine ⟨by simpa only [Res.addW_q] using hlk, .inl ⟨tw, ⟨?_, fun p hp' => ?_⟩, hkS, ?_⟩⟩
        · refine (Res.addW_X_self _ _ _ _).mpr (.inr ⟨by rw [hq]; decide, ?_⟩)
          rw [hx5, setWidth_ofNat_32 (hk hkS)]
        · rcases (Res.addW_X_self _ _ _ _).mp hp' with hp' | ⟨-, rfl⟩
          · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans (hmax _ hp') hts) hcoh)
          · exact Nat.le_refl _
        · rw [hvw', hvw]
          have hnt : (A.storeKind StoreKind.plain == StoreKind.nt) = false := by
            revert hA; cases A.storeKind StoreKind.plain <;> decide
          simp only [hnt, Bool.false_eq_true, ↓reduceIte]
          exact Nat.le_max_right _ _
      · exact ⟨by simpa only [Res.addW_q] using hlk, .inr (by simpa only [Res.addW_q] using hsur)⟩

end Kraken.Promising.SLR.SwpInv.EnvSpike
