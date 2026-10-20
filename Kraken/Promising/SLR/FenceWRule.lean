/-
**The fence-released MP writer's rule**: a
`ThreadRuleRXG (GHyb rel)` for `fwriterMp` (`SLR/FenceWTrees.lean`) whose
`prepay` covers `GHyb`'s second disjunct, and its `NPSafeP (GHyb rel)`
corollaries (frames `K2₀` and `K2Scope AllocIds`).

The rule is the existing MP writer's (`SLR/MpWriter.lean`, `SLR/MpRule.lean`,
`Mp.mpRuleW`) with the flag store moved from `stlr` to the plain `str` after
`dmb ish`. Only two facts about the flag store change:

- **The timestamp bound.** `release_split_mp` needs the flag message above
  `vwOld` (the data write lies at or below it). `stlr`'s pre-view takes
  `relPre ⊇ vwOld`; for the plain store, a fresh append is above
  `vwNew ⊔ vCAP ⊇ relPre` under `Views.FenceRel` (`writeSuccs_fresh_vwOld_F`),
  and a fence-aware fulfilment is above `relPre`
  (`writeSuccs_relF_relPre`). The invariant carries `FenceRel` at position 4
  (`PhaseF`), established by the `dmb ish` cell (`wpF_dmb`).
- **The prepay guard.** `prepay` is asked at
  `GHyb rel = G₀ ∨ (RelFulfilsLiveF ∧ impure message)` instead of `G₀`
  (`relFulfilsF_posF`): no instruction of the writer stores with a release, so
  the `G₀` disjunct never holds (`relFulfils_posF_G₀`: a plain store never
  satisfies the `G₀` store case when `A.plainStore ≠ .rel`); the second
  disjunct is a fence-aware fulfilment by
  the data store (position 2, excluded: its message is at `Dt`, pure for
  `rel`) or by the flag store (position 4: prepay exactly as for `stlr`,
  `fw_prepay`).

The erasure side of the flag store is the `stlr` proof with `.plain` for
`.rel`: `EvTree.eraseWPR_store_rel`, `Erase.fresh_of_impure`,
`EvTree.eraseWPRD_store_pendOrDead` do not look at the store kind.
-/
import Kraken.Promising.SLR.FenceWTrees
import Kraken.Promising.SLR.MpRule
import Kraken.Promising.SLR.NPSafePHyb

namespace Kraken.Promising.SLR.FenceW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.Mp

/-- `omega` on `Time`/`View`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Machine facts -/

/-- **A fresh append under `FenceRel` lies above `vwOld`**, whatever the
store kind (the fence-aware `SpinCommon.writeSuccs_fresh_vwOld`). -/
theorem writeSuccs_fresh_vwOld_F {A : Arch} {tid : Nat} {iv : InstrViews} {c : Ctx} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} {c' : Ctx}
    (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra) (hF : c.views.FenceRel)
    (hm : c'.mem = (c.mem.append ⟨l, v, tid⟩).1) : c.views.vwOld < c.mem.last + 1 := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · exfalso
    split at h
    · obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
      simp only [Option.some.injEq] at h
      subst h
      have hm' : c.mem = (c.mem.append ⟨l, v, tid⟩).1 := hm
      have h2 := Memory.get?_append_last c.mem ⟨l, v, tid⟩
      rw [← hm'] at h2
      have := c.mem.last_le_of_get?_eq_some h2
      omega_t
    · cases h
  · split at h
    rename_i _ mem' t hok
    rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨hok', rfl⟩ := h
    have ht : t = c.mem.last + 1 := (congrArg Prod.snd hok).symm
    subst ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok'
    obtain ⟨hb, -⟩ := hok'
    simp only [Views.FenceRel, Views.relPre] at hF
    generalize (if (A.storeKind k == StoreKind.rel) = true then
      max (max c.views.vrOld c.views.vrOldNR) c.views.vwOld
      else if (A.storeKind k == StoreKind.nt) = true then max c.views.vrOld c.views.vrOldNR else 0) = e at hb
    simp only [Memory.last] at hb ⊢
    omega_t

variable [layout : _root_.Layout]

/-! ## The cells from a state with no own pending promise -/

/-- A writer cell proof from a state with no own pending promise (lifted by
`fw_lift`). -/
def CellF (P : Params) (A : Arch) (tid : Nat) (i : Nat) : Prop :=
  ∀ {cl' : Prop} {c : Config isa} {r : Res} {g : Ghost} (rF : Nat → Res) (t : Thread isa)
    (tree : EvTree isa.State), WorldW P g → c.threads[tid]? = some t → FrameF P t.st →
    AtPos fwriterMp t.st i → PhaseF P i (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec) t.views r →
    isa.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → (∀ ts ∈ t.prom, ts ∉ g.pend) →
    tree.EraseWPR A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvF P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem)

/-- A writer cell proof in the `ThreadRuleRX` (dead-branch) form. -/
def CellFX (P : Params) (A : Arch) (tid : Nat) (i : Nat) : Prop :=
  ∀ {cl' : Prop} {c : Config isa} {r : Res} {g : Ghost} (rF : Nat → Res) (t : Thread isa)
    (tree : EvTree isa.State), WorldW P g → c.threads[tid]? = some t → FrameF P t.st →
    AtPos fwriterMp t.st i → PhaseF P i (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec) t.views r → PrepaidPromF P tid i t c.mem r →
    isa.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → OwnPendF P tid c r g →
    tree.EraseWPRD A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvXF P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem)

/-- **The lift** (`liftOb_invXOf`; `InvXF` is an `InvXOf` invariant). -/
theorem fw_lift {P : Params} {A : Arch} {tid : Nat} : LiftObG A tid (InvF P tid) (InvXF P tid) :=
  liftOb_invXOf A tid (InvF P tid)
    (fun t _ r g ts => AtPos fwriterMp t.st 4 ∧ (r.wr P.Dt).q = 0 ∧ ∀ ts' ∈ t.prom, ts' ∈ g.pend → ts' = ts)

section Cells

variable [hw : Executable.ValidLayout (layout fwriterMp)]

/-- `mov w2, #1` (position 0 → 1). -/
theorem wpF_mov2 {P : Params} {A : Arch} {tid : Nat} : CellF P A tid 0 := by
  intro cl' c r g rF t tree hW ht hF hp hph hex _ _ _
  rw [exec_f_mov2 t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ _ => ?_
  refine invF_withThread (i := 1) hW ht hst (hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl)
    rfl ?_ (fun h => absurd h (by decide))
  simp only [PhaseF] at hph ⊢
  exact ⟨hph, by simp [Reg64s.setXReg]⟩

/-- `mov w3, #1` (position 1 → 2). -/
theorem wpF_mov3 {P : Params} {A : Arch} {tid : Nat} : CellF P A tid 1 := by
  intro cl' c r g rF t tree hW ht hF hp hph hex _ _ _
  rw [exec_f_mov3 t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ _ => ?_
  refine invF_withThread (i := 2) hW ht hst (hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl)
    rfl ?_ (fun h => absurd h (by decide))
  simp only [PhaseF] at hph ⊢
  exact ⟨hph.1, by simpa [Reg64s.setXReg] using hph.2, by simp [Reg64s.setXReg]⟩

/-- **The data store** `str w2, [x1]` (position 2 → 3; `Mp.wpW_str`). -/
theorem wpF_str {P : Params} {A : Arch} {tid : Nat} (hA : A.storeKind .plain ≠ .nt) : CellF P A tid 2 := by
  intro cl' c r g rF t tree hW ht hF hp hph hex E hM hpd
  have hn := lt_size_of_get? ht
  have hnd : t.prom.Nodup := hM.promNodup tid t ht
  rw [exec_f_str t.st (hF.at hp (by decide)) hF.x1 hF.dd] at hex
  cases hex
  simp only [PhaseF] at hph
  obtain ⟨⟨hq, h0, hWq, hFq⟩, hx2, hx3⟩ := hph
  rw [hx2, one_128]
  refine EvTree.eraseWPR_store_pure hn (by rw [hq]; decide) (hW.2 _) ?_ ?_
  · intro cx' tw _ hev hpd'
    exfalso
    rcases hev.cases with ⟨-, htw, -⟩ | ⟨-, rfl⟩
    · exact hpd tw htw hpd'
    · exact Nat.not_succ_le_self _ (E.pend_le hpd')
  · intro cx' tw hc hev _
    obtain ⟨-, hvw⟩ := writeSuccs_tw hnd hc hev
    rw [storeGhost_plain]
    simp only [EvTree.EraseWPR]
    refine ⟨Ghost.Le.refl g, fun ts h _ => h, fun ts h => h, fun x h => ?_, fun w hw => ?_, fun t' ht' _ => ?_⟩
    · simpa only [mayWrite, Res.addW_q, Res.addW_acq] using h
    · rw [writtenCx_writeEv hev hw]; show 0 < (r.wr P.Dt).q; rw [hq]; decide
    · obtain ⟨-, hvs⟩ := finishInstr_relKey ht'
      have hvw' : t'.views.vwOld = cx'.views.vwOld := by simpa using congrArg Views.vwOld hvs
      refine invF_withThread (i := 3) hW ht (finishInstr_st ht') (hF.goto rfl rfl rfl) rfl ?_
        (fun h => absurd h (by decide))
      simp only [PhaseF, Own1, Res.addW_q]
      refine ⟨⟨hq, ⟨tw, (Res.addW_X_self _ _ _ _).mpr (.inr ⟨by rw [hq]; decide, rfl⟩), fun p hp' => ?_, ?_⟩,
        hWq, hFq⟩, hx3⟩
      · rcases (Res.addW_X_self _ _ _ _).mp hp' with hp' | ⟨-, rfl⟩
        · rw [h0 p hp']; exact Nat.zero_le _
        · exact Nat.le_refl _
      · rw [hvw', hvw]
        have hnt : (A.storeKind StoreKind.plain == StoreKind.nt) = false := by
          revert hA; cases A.storeKind StoreKind.plain <;> decide
        simp only [hnt, Bool.false_eq_true, ↓reduceIte]
        exact Nat.le_max_right _ _

/-- **`dmb ish`** (position 3 → 4): no memory event; the views become
`FenceRel` (`vwNew` rises above `relPre`) and `vwOld` is kept, so `Own1`
survives. -/
theorem wpF_dmb {P : Params} {A : Arch} {tid : Nat} : CellF P A tid 3 := by
  intro cl' c r g rF t tree hW ht hF hp hph hex _ _ _
  rw [exec_f_dmb t.st (hF.at hp (by decide))] at hex
  cases hex
  simp only [EvTree.EraseWPR]
  obtain ⟨hm, hpr⟩ := fenceStep_mem_prom (ctx₀ t tid c.mem) .sy
  refine WpPostR.noWrite hm hpr fun t' hst _ hv => ?_
  have h1 : t'.views.vrOld = t.views.vrOld := by simpa [fenceStep] using congrArg Views.vrOld hv
  have h2 : t'.views.vrOldNR = t.views.vrOldNR := by simpa [fenceStep] using congrArg Views.vrOldNR hv
  have h3 : t'.views.vwOld = t.views.vwOld := by simpa [fenceStep] using congrArg Views.vwOld hv
  have h4 : t'.views.vwNew = max t.views.vwNew (max (max t.views.vrOld t.views.vrOldNR)
      (max t.views.vwOld t.views.vwOldNT)) := by simpa [fenceStep] using congrArg Views.vwNew hv
  refine invF_withThread (i := 4) hW ht hst (hF.goto rfl rfl rfl) rfl ?_ (fun _ h => ?_)
  · simp only [PhaseF, Own1] at hph ⊢
    refine ⟨.inl ?_, hph.2, ?_⟩
    · rw [h3]; exact hph.1
    · simp only [Views.FenceRel, Views.relPre]
      rw [h1, h2, h3, h4]
      omega_t
  · simp only [PhaseF, Own1] at hph
    rw [hph.1.1] at h
    exact absurd h (by decide)

end Cells

/-! ## The flag store -/

section FlagStore

variable [hw : Executable.ValidLayout (layout fwriterMp)]

omit hw in
/-- **The flag store from `Own1`** (`Mp.wpW_stlr_own` with a plain,
fence-released store). -/
theorem wpF_strf_own {P : Params} {A : Arch} {tid : Nat} (hL : MpLocs P) {cl' : Prop} {c : Config isa}
    {r : Res} {g : Ghost} (rF : Nat → Res) (t : Thread isa) (hW : WorldW P g) (ht : c.threads[tid]? = some t)
    (hF : FrameF P t.st) (hown : Own1 P t.views r) (hFR : t.views.FenceRel)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hM : c.MachInv) (hnp : ∀ ts ∈ t.prom, ts ∉ g.pend) :
    (EvTree.store .plain false P.Fl 1#128 fun _ => .done (A64Trees.goto t.st t.st.st.1
        ((layout fwriterMp).addrOf 5))).EraseWPR
      A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvF P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  have hn := lt_size_of_get? ht
  have hpos : 0 < (r.wr P.Fl).q := hown.2.2.2
  refine EvTree.eraseWPR_store_rel hn hpos ?_ ?_
  · intro cx' tw _ hev hpd
    exfalso
    rcases hev.cases with ⟨-, htw, -⟩ | ⟨-, rfl⟩
    · exact hnp tw htw hpd
    · exact Nat.not_succ_le_self _ (E.pend_le hpd)
  · intro cx' tw hc hev hpd _
    obtain ⟨hm', htw⟩ := E.fresh_of_impure ht rfl rfl hev hpd (flag_impure hW)
    have hvw : t.views.vwOld < tw := htw ▸ writeSuccs_fresh_vwOld_F hc hFR hm'
    obtain ⟨R, r', hres, hR0, hGB, -, hWq, -⟩ := release_split_mp hL hown hvw
    refine ⟨fun hin => ?_, htw ▸ not_claimed_new E _, R, r', ?_, hres, fun ss hss hprod => ?_⟩
    · obtain ⟨w, hw, -⟩ := hM.promWf tid t ht tw hin
      exact Nat.not_succ_le_self _ (htw ▸ c.mem.last_le_of_get?_eq_some hw)
    · rw [hW.1]; exact fun _ => hGB
    have hdisj : ∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key := fun s hs s' hs' he => by
      have h1 := E.slot_key_le hs
      rw [he, hss.key s' hs', htw] at h1
      exact Nat.not_succ_le_self _ h1
    have hgle : g.Le (storeGhost g P.Fl tw true ss) := ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩
    simp only [EvTree.EraseWPR]
    refine ⟨hgle, fun ts h _ => h, fun ts h => h, fun y h => mayWrite_release hres hprod hR0 hdisj h,
      fun w hw => ?_, fun t' ht' _ => ?_⟩
    · rw [writtenCx_fresh rfl hev hm' htw hw]; exact hpos
    · exact invF_withThread (i := 5) (hW.mono hgle) ht (finishInstr_st ht') (hF.goto rfl rfl rfl) rfl
        (by simp only [PhaseF]; exact hWq) (fun h => absurd h (by decide))

omit hw in
/-- **The flag store from `Prepaid`** (`Mp.wpW_stlr_prepaid`). -/
theorem wpF_strf_prepaid {P : Params} {A : Arch} {tid : Nat} {cl' : Prop} {c : Config isa} {r : Res}
    {g : Ghost} (rF : Nat → Res) (t : Thread isa)
    (hW : WorldW P g) (ht : c.threads[tid]? = some t) (hF : FrameF P t.st) (hpre : Prepaid P r)
    (hts : ∃ ts ∈ t.prom, c.mem.get? ts = some ⟨P.Fl, 1#128, tid⟩)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hM : c.MachInv)
    (huniq : ∀ ts ∈ t.prom, ts ∈ g.pend → ∀ ts' ∈ t.prom, ts' ∈ g.pend → ts' = ts) :
    (EvTree.store .plain false P.Fl 1#128 fun _ => .done (A64Trees.goto t.st t.st.st.1
        ((layout fwriterMp).addrOf 5))).EraseWPRD
      A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvXF P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  have hn := lt_size_of_get? ht
  have hnd : t.prom.Nodup := hM.promNodup tid t ht
  refine EvTree.eraseWPRD_store_pendOrDead hn ?_ ?_
  · intro cx' tw _ hev hpd
    have hget : c.mem.get? tw = some ⟨P.Fl, 1#128, tid⟩ ∧ tw ∈ t.prom ∧ cx'.mem = c.mem := by
      rcases hev.cases with ⟨hm', htw, hg⟩ | ⟨-, rfl⟩
      · exact ⟨hg, htw, hm'⟩
      · exact absurd (E.pend_le hpd) (Nat.not_succ_le_self _)
    obtain ⟨hget, htw, hmem⟩ := hget
    have hgle : g.Le (unpend g tw) := ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩
    simp only [EvTree.EraseWPRD]
    refine ⟨hgle, fun ts hts hor => ?_, fun ts h => (mem_unpend_pend.mp h).1, fun _ h => h, fun w hw => ?_,
      fun t' ht' _ => ⟨?_, ?_, ?_⟩⟩
    · refine mem_unpend_pend.mpr ⟨hts, fun he => ?_⟩
      subst he
      rcases hor with h | ⟨i, t'', hi, hti, hpr⟩
      · rw [hev.prom] at h
        exact ((List.Nodup.mem_erase_iff hnd).mp h).1 rfl
      · obtain ⟨w, hw, hwt⟩ := hM.promWf i t'' hti _ hpr
        rw [hget] at hw
        cases hw
        exact hi hwt.symm
    · rw [writtenCx_writeEv hev hw]; exact hpre.2.2
    · exact invF_withThread (i := 5) (hW.mono hgle) ht (finishInstr_st ht') (hF.goto rfl rfl rfl) rfl
        (by simp only [PhaseF]; exact hpre.2.1) (fun h => absurd h (by decide))
    · intro ts h
      show ts ≤ cx'.mem.last
      rw [hmem]; exact E.pend_le (mem_unpend_pend.mp h).1
    · intro t'' ht'' ts h1 h2
      exfalso
      rw [Config.withThread_get? _ _ _ hn] at ht''
      simp only [ite_true, Option.some.injEq] at ht''
      subst ht''
      rw [(finishInstr_relKey ht').1, hev.prom] at h1
      obtain ⟨hne, h1⟩ := (List.Nodup.mem_erase_iff hnd).mp h1
      exact hne (huniq tw htw hpd ts h1 (mem_unpend_pend.mp h2).1)
  · intro cx' tw hc hev hpd _ _
    obtain ⟨hm', htw⟩ := E.fresh_of_impure ht rfl rfl hev hpd (flag_impure hW)
    obtain ⟨ts, hts, hget⟩ := hts
    have hle : ts ≤ c.mem.last := c.mem.last_le_of_get?_eq_some hget
    refine ⟨ts, ?_, _, writeSuccs_get? hc hget, ?_⟩
    · rw [hev.prom]
      exact (List.mem_erase_of_ne fun he => Nat.not_succ_le_self _ (htw ▸ he ▸ hle)).mpr hts
    · rcases (mem_writeSuccs A tid).mp hc with ⟨_, _, _, _, _, _, _, _, heq⟩ | ⟨_, heq⟩
      · exfalso
        rw [heq] at hm'
        have := congrArg Memory.last hm'
        simp only [afterWrite, Memory.last_append] at this
        exact Nat.succ_ne_self _ this.symm
      · rw [heq, afterWrite_getCoh]
        simp only [↓reduceIte]
        exact Nat.le_trans (Nat.le_succ_of_le hle) (Nat.le_max_right _ _)

/-- **The flag store** `str w3, [x0]` (position 4 → 5). -/
theorem wpF_strf {P : Params} {A : Arch} {tid : Nat} (hL : MpLocs P) : CellFX P A tid 4 := by
  intro cl' c r g rF t tree hW ht hF hp hph hpp hex E hM hOP
  rw [exec_f_strf t.st (hF.at hp (by decide)) hF.x0 hF.df] at hex
  cases hex
  simp only [PhaseF] at hph
  obtain ⟨hph, hx3, hFR⟩ := hph
  rw [hx3, one_128]
  rcases hph with hown | hpre
  · have hnp : ∀ ts ∈ t.prom, ts ∉ g.pend := fun ts hts hpd' => by
      have h0 := (hOP t ht ts hts hpd').2.1
      rw [hown.1] at h0
      exact absurd h0 (by decide)
    exact fw_lift rF t _ ht E hM hnp (wpF_strf_own hL rF t hW ht hF hown hFR E hM hnp)
  · exact wpF_strf_prepaid rF t hW ht hF hpre (hpp rfl hpre.1) E hM
      fun ts hts hpd' ts' hts' hpd'' => (hOP t ht ts hts hpd').2.2 ts' hts' hpd''

end FlagStore

/-! ## Environment and own pending promises -/

/-- **`InvF` across an environment extension**: the thread keeps its state
and views (hence `FenceRel`); the memory grows. -/
theorem invF_env {P : Params} {tid : Nat} {cl : Prop} {c c₁ : Config isa} {r : Res}
    {g g₁ : Ghost} (h : InvF P tid cl c r g) (he : EnvExt tid c c₁) (hle : g.Le g₁) : InvF P tid cl c₁ r g₁ := by
  obtain ⟨hW, t, ht, hF, i, hp, hph, hpp⟩ := h
  obtain ⟨-, hpre, hth⟩ := he
  obtain ⟨ps, ht₁, -⟩ := hth t ht
  refine ⟨hW.mono hle, _, ht₁, hF, i, hp, hph, fun h4 hq => ?_⟩
  obtain ⟨ts, hts, hget⟩ := hpp h4 hq
  exact ⟨ts, List.mem_append_left _ hts, Memory.get?_of_prefix hpre hget⟩

/-- **`OwnPendF` at the extension** (`Mp.ownPendW_transport`). -/
theorem ownPendF_transport {P : Params} {tid : Nat} {cl : Prop} {c₀ c : Config isa} {r : Res}
    {g₀ g : Ghost} (h : InvXF P tid cl c₀ r g₀) (he : EnvExt tid c₀ c) {t : Thread isa}
    (ht : c.threads[tid]? = some t) (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) : OwnPendF P tid c r g := by
  obtain ⟨⟨-, t₀, ht₀, -⟩, hPI, hOP⟩ := h
  obtain ⟨-, -, hth⟩ := he
  obtain ⟨ps, ht₁, hps⟩ := hth t₀ ht₀
  intro t' ht' ts hts hpd
  rw [ht] at ht'
  cases ht'
  rw [ht₁] at ht
  cases ht
  have h0 := hnp ts hts hpd
  rcases List.mem_append.mp hts with h | h
  · obtain ⟨h4, hq, hu⟩ := hOP t₀ ht₀ ts h h0
    refine ⟨h4, hq, fun ts' hts' hpd' => ?_⟩
    have h0' := hnp ts' hts' hpd'
    rcases List.mem_append.mp hts' with h' | h'
    · exact hu ts' h' h0'
    · exact absurd (hPI ts' h0') (Nat.not_le.mpr (hps ts' h'))
  · exact absurd (hPI ts h0) (Nat.not_le.mpr (hps ts h))

/-! ## The prepayment -/

section Prepay

variable [hw : Executable.ValidLayout (layout fwriterMp)]

/-- **The `G₀` disjunct is impossible**: no instruction of the writer is a
release store (`A.plainStore ≠ .rel`). -/
theorem relFulfils_posF_G₀ {P : Params} {A : Arch} {tid : Nat} (hA : A.plainStore ≠ .rel)
    {t : Thread isa} {mem : Memory} {ts : Time} {i : Nat}
    (hF : FrameF P t.st) (hp : AtPos fwriterMp t.st i) (hi : i ≤ 5)
    (h : t.RelFulfilsLive A tid ts mem) : False := by
  obtain ⟨tree, hex, hrf⟩ := h
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_f_mov2 t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_f_mov3 t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_f_str t.st (hF.at hp (by decide)) hF.x1 hF.dd] at hex; cases hex
    simp [EvTree.RelFulfilsLive, Arch.storeKind, hA] at hrf
  · rw [exec_f_dmb t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_f_strf t.st (hF.at hp (by decide)) hF.x0 hF.df] at hex; cases hex
    simp [EvTree.RelFulfilsLive, Arch.storeKind, hA] at hrf
  · rw [exec_end_f hF hp] at hex; cases hex

/-- **Which instructions fulfil a promise fence-aware** (`Mp.relFulfils_posW`
for `GF`): the data store (position 2, a message at `Dt`) or the flag store
(position 4, a flag message of the value of `W3` above `vwOld`, every other
outstanding flag promise above it). -/
theorem relFulfilsF_posF {P : Params} {A : Arch} {tid : Nat}
    {t : Thread isa} {mem : Memory} {ts : Time} {i : Nat}
    (hF : FrameF P t.st) (hp : AtPos fwriterMp t.st i) (hi : i ≤ 5)
    (hb : ∀ p ∈ t.prom, p ≤ mem.last) (h : t.RelFulfilsLiveF A tid ts mem) :
    (i = 2 ∧ ∃ w, mem.get? ts = some w ∧ w.loc = P.Dt) ∨
    (i = 4 ∧ (∃ w, mem.get? ts = some w ∧ w.loc = P.Fl ∧
        w.val = BitVec.setWidth 128 (BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec)) ∧ t.views.vwOld < ts ∧
      ∀ p ∈ t.prom, p ≠ ts → ∀ w, mem.get? p = some w → w.loc = P.Fl → ts < p) := by
  obtain ⟨tree, hex, hrf⟩ := h
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_f_mov2 t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLiveF] at hrf
  · rw [exec_f_mov3 t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLiveF] at hrf
  · rw [exec_f_str t.st (hF.at hp (by decide)) hF.x1 hF.dd] at hex; cases hex
    simp only [EvTree.RelFulfilsLiveF, or_false] at hrf
    obtain ⟨cx', hc, ⟨-, hin, hout⟩, hnd⟩ := hrf
    obtain ⟨⟨w, hw, hl, -⟩, -, -⟩ := SpinCommon.writeSuccs_fulfil_live hc hb hin hout hnd
    exact .inl ⟨rfl, w, hw, hl⟩
  · rw [exec_f_dmb t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLiveF] at hrf
  · rw [exec_f_strf t.st (hF.at hp (by decide)) hF.x0 hF.df] at hex; cases hex
    simp only [EvTree.RelFulfilsLiveF, or_false] at hrf
    obtain ⟨cx', hc, ⟨hk, hin, hout⟩, hnd⟩ := hrf
    obtain ⟨hw, -, hlive⟩ := SpinCommon.writeSuccs_fulfil_live hc hb hin hout hnd
    have hlt := writeSuccs_relF_relPre A tid _ hc hk hin hout
    refine .inr ⟨rfl, hw, ?_, hlive⟩
    simp only [Views.relPre] at hlt
    omega_t
  · rw [exec_end_f hF hp] at hex; cases hex

/-- **The prepay obligation** of the fence-released writer at the guard
`GHyb rel`, for every `rel` under which the data word is pure: the only
prepayable promise is the flag message fulfilled by the fence-released
`str w3, [x0]` (position 4); from `Own1` the release split at `|M| + 1`
(`Erase.prepay_exempt`), from `Prepaid` a second prepayment would leave the
first prepaid promise dead (`Mp.mp_prepay`). -/
theorem fw_prepay {P : Params} {A : Arch} {tid : Nat} (hL : MpLocs P) (hA : A.plainStore ≠ .rel)
    {rel : Loc → Pred} (hrelD : ∀ v, Pred.Pure (rel P.Dt) v)
    {cl : Prop} {c₀ c : Config isa} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t₁ : Thread isa)
    (w : Msg) (h : InvXF P tid cl c₀ r g₀) (he : EnvExt tid c₀ c) (hle : g₀.Le g) (ht : c.threads[tid]? = some t₁)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hM : c.MachInv)
    (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hG : GHyb rel A tid (c.mem.append { w with tid }).2 { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }
      (c.mem.append { w with tid }).1) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvXF P tid (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  have htw : (c.mem.append { w with tid }).2 = c.mem.last + 1 := rfl
  rw [htw] at hG ⊢
  have hOP := ownPendF_transport h he ht hnp
  obtain ⟨hW, t, ht', hF, i, hp, hph, hpp⟩ := invF_env h.1 he hle
  rw [ht] at ht'
  obtain rfl : t₁ = t := Option.some.inj ht'
  have hn := lt_size_of_get? ht
  have hi5 : i ≤ 5 := by rcases PhaseF.pos hph with h | h | h | h | h | h <;> omega
  have hb : ∀ p ∈ t₁.prom ++ [c.mem.last + 1], p ≤ (c.mem.append { w with tid }).1.last := fun p hp' => by
    rw [Memory.last_append]
    rcases List.mem_append.mp hp' with h1 | h1
    · obtain ⟨w', hw', -⟩ := hM.promWf tid t₁ ht p h1
      exact Nat.le_succ_of_le (c.mem.last_le_of_get?_eq_some hw')
    · rw [List.mem_singleton.mp h1]; exact Nat.le_refl _
  -- the guard: never `G₀`; a fence-aware fulfilment of an impure message
  obtain ⟨hrel, wi, hwi, himp⟩ : { t₁ with prom := t₁.prom ++ [c.mem.last + 1] }.RelFulfilsLiveF A tid
      (c.mem.last + 1) (c.mem.append { w with tid }).1 ∧ ∃ wi, (c.mem.append { w with tid }).1.get? (c.mem.last + 1) =
        some wi ∧ ¬ Pred.Pure (rel wi.loc) wi.val := by
    rcases hG with hG | hG
    · exact (relFulfils_posF_G₀ (P := P) (t := { t₁ with prom := t₁.prom ++ [c.mem.last + 1] }) hA hF hp hi5
        hG).elim
    · exact hG
  rcases relFulfilsF_posF (P := P) (t := { t₁ with prom := t₁.prom ++ [c.mem.last + 1] }) hF hp hi5 hb hrel with
    ⟨-, w', hw', hwl⟩ | ⟨rfl, ⟨w', hw', hwl, hwv⟩, hvw, hlive⟩
  · -- the data store: its message is at `Dt`, pure for `rel`
    rw [hwi] at hw'
    obtain rfl := Option.some.inj hw'
    exact absurd (hwl ▸ hrelD wi.val) himp
  simp only [PhaseF] at hph
  obtain ⟨hph, hx3, hFR⟩ := hph
  rw [Memory.get?_append_last] at hw'
  obtain rfl := Option.some.inj hw'
  obtain ⟨wl, wv, wt⟩ := w
  simp only at hwl hwv
  rw [hx3, one_128] at hwv
  subst hwl hwv
  rcases hph with hown | hpre
  case inr =>
    obtain ⟨ts, hts, hget⟩ := hpp rfl hpre.1
    have hle : ts ≤ c.mem.last := c.mem.last_le_of_get?_eq_some hget
    have h1 := hlive ts (List.mem_append_left _ hts) (fun he => Nat.not_succ_le_self _ (he ▸ hle)) _
      (by rw [Memory.get?_append_of_le _ _ _ hle]; exact hget) rfl
    exact absurd h1 (Nat.not_lt.mpr (Nat.le_succ_of_le hle))
  have hnp0 : ∀ ts ∈ t₁.prom, ts ∉ g.pend := fun ts hts hpd => by
    have h0 := (hOP t₁ ht ts hts hpd).2.1
    rw [hown.1] at h0
    exact absurd h0 (by decide)
  have hpos : 0 < (r.wr P.Fl).q := hown.2.2.2
  obtain ⟨R, r', hres, hR0, hGB, hD', hWq', hFq'⟩ := release_split_mp hL hown hvw
  have hR : (g.rel P.Fl).P 1#128 (c.mem.append ⟨P.Fl, 1#128, tid⟩).1 (c.mem.last + 1) R := by
    rw [hW.1]; exact fun _ => hGB
  obtain ⟨ss, hss, hprod⟩ := Erase.slotsFor E hR
  have hres' : r'.op (Res.prod (ss.map (·.res))) = r.addW P.Fl (1#128, c.mem.last + 1) := by
    rw [hprod]; exact hres
  have E' := Erase.prepay_exempt (w := ⟨P.Fl, 1#128, wt⟩) E ht trivial (ss := ss) (r' := r')
    (by rw [setRes_self]; exact hpos) hss (by rw [setRes_self]; exact hres')
  rw [setRes_setRes] at E'
  have hgle : g.Le (prepayGhost g P.Fl (c.mem.last + 1) ss) :=
    ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩
  have hdisj : ∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key := fun s hs s' hs' he' => by
    have h1 := E.slot_key_le hs
    rw [he', hss.key s' hs'] at h1
    exact Nat.not_succ_le_self _ h1
  refine ⟨r', _, E', hgle, List.mem_cons_self .., fun ts h => List.mem_cons_of_mem _ h,
    fun ts h => (List.mem_cons.mp h).elim .inr .inl, ⟨?_, ?_, ?_⟩,
    fun y h => mayWrite_release (x := P.Fl) (tw := c.mem.last + 1) hres hprod hR0 hdisj h,
    prepay_K2 hss, prepay_K1 hss hres'⟩
  · refine invF_withThread (i := 4) (t' := { t₁ with prom := t₁.prom ++ [c.mem.last + 1] }) (hW.mono hgle)
      ht rfl hF hp ?_ fun _ _ => ⟨c.mem.last + 1, List.mem_append_right _ (List.mem_singleton_self _),
        Memory.get?_append_last _ _⟩
    simp only [PhaseF]
    exact ⟨.inr ⟨hD', hWq', hFq'⟩, hx3, hFR⟩
  · intro ts h
    show ts ≤ (c.mem.append _).1.last
    rw [Memory.last_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (E.pend_le h)
  · intro t'' ht'' ts h1 h2
    rw [Config.withThread_get? _ _ _ hn] at ht''
    simp only [ite_true, Option.some.injEq] at ht''
    subst ht''
    have key : ∀ x ∈ t₁.prom ++ [c.mem.last + 1], x ∈ (prepayGhost g P.Fl (c.mem.last + 1) ss).pend →
        x = c.mem.last + 1 := fun x hx hxp => by
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_cons.mp hxp with h | h
        · exact h
        · exact absurd h (hnp0 x hx)
      · exact List.mem_singleton.mp hx
    exact ⟨hp, hD', fun ts' h1' h2' => (key ts' h1' h2').trans (key ts h1 h2).symm⟩

end Prepay

/-! ## The rule -/

section Rule

variable [hw : Executable.ValidLayout (layout fwriterMp)]

/-- Away from position 4 the writer has no own pending promise. -/
theorem noPendF {P : Params} {tid : Nat} {c : Config isa} {r : Res} {g : Ghost} {t : Thread isa}
    (hOP : OwnPendF P tid c r g) (ht : c.threads[tid]? = some t) {i : Nat} (hi : i ≤ 5)
    (hp : AtPos fwriterMp t.st i) (h4 : i ≠ 4) : ∀ ts ∈ t.prom, ts ∉ g.pend :=
  fun ts hts hpd => h4 (atPosF_inj hi (by decide) hp (hOP t ht ts hts hpd).1)

/-- **`done`**: a halted writer is at the end, holding all of `W`. -/
theorem invF_done {P : Params} {tid rd : Nat} {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvF P tid cl c r g) (hd : c.Done tid) : MpPost P rd c r g := by
  obtain ⟨-, t, ht, hF, i, hp, hph, -⟩ := h
  obtain ⟨t', ht', hhalt, -⟩ := hd
  rw [ht] at ht'
  obtain rfl : t = t' := Option.some.inj ht'
  have hnone : isa.exec t.st = none := by simpa [Thread.halted] using hhalt
  rcases PhaseF.pos hph with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_f_mov2 t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_f_mov3 t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_f_str t.st (hF.at hp (by decide)) hF.x1 hF.dd] at hnone; cases hnone
  · rw [exec_f_dmb t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_f_strf t.st (hF.at hp (by decide)) hF.x0 hF.df] at hnone; cases hnone
  · exact .inl hph

/-- **The fence-released writer's rule** at the hybrid guard `GHyb rel`, for
every `rel` under which the data word is pure (in `mp_fence`, the initial
ghost's `(mpGhost P).rel`). Its `prepay` covers `GHyb`'s second disjunct:
the fence-released flag store of the impure flag message. -/
def fwRuleG (P : Params) (A : Arch) (tid rd : Nat) (hL : MpLocs P) (hA : A.storeKind .plain ≠ .nt)
    (hA' : A.plainStore ≠ .rel) (rel : Loc → Pred) (hrelD : ∀ v, Pred.Pure (rel P.Dt) v) :
    ThreadRuleRXG (I := isa) (GHyb rel) A (MpPost P rd) tid where
  Inv := InvXF P tid
  done := fun h he hle _ hd => invF_done (invF_env h.1 he hle) hd
  wp := fun {cl} {c₀} {c} {r} {g₀} {g} rF t tree h he hle ht hex E hinv _ hnp => by
    have hOP := ownPendF_transport h he ht hnp
    obtain ⟨hW, t', ht', hF, i, hp, hph, hpp⟩ := invF_env h.1 he hle
    rw [ht] at ht'
    obtain rfl : t = t' := Option.some.inj ht'
    have hpos := PhaseF.pos hph
    have hi5 : i ≤ 5 := by omega
    have hno := noPendF hOP ht hi5 hp
    rcases hpos with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fw_lift rF t tree ht E hinv (hno (by decide))
        (wpF_mov2 rF t tree hW ht hF hp hph hex E hinv (hno (by decide)))
    · exact fw_lift rF t tree ht E hinv (hno (by decide))
        (wpF_mov3 rF t tree hW ht hF hp hph hex E hinv (hno (by decide)))
    · exact fw_lift rF t tree ht E hinv (hno (by decide))
        (wpF_str hA rF t tree hW ht hF hp hph hex E hinv (hno (by decide)))
    · exact fw_lift rF t tree ht E hinv (hno (by decide))
        (wpF_dmb rF t tree hW ht hF hp hph hex E hinv (hno (by decide)))
    · exact wpF_strf hL rF t tree hW ht hF hp hph hpp hex E hinv hOP
    · rw [exec_end_f hF hp] at hex; cases hex
  prepay := fun rF t₁ w h he hle ht E hinv hnp hG => fw_prepay hL hA' hrelD rF t₁ w h he hle ht E hinv hnp hG

/-- **The fence-released writer is `NPSafeP (GHyb rel)`** (frame `K2₀`). -/
theorem fw_npSafeP_hyb (P : Params) (A : Arch) (tid rd : Nat) (hL : MpLocs P) (hA : A.storeKind .plain ≠ .nt)
    (hA' : A.plainStore ≠ .rel) (rel : Loc → Pred) (hrelD : ∀ v, Pred.Pure (rel P.Dt) v) (n m : Nat) {cl : Prop}
    {c : Config isa} {r : Res} {g : Ghost} (h : InvXF P tid cl c r g) :
    NPSafeP (model isa) A (MpPost P rd) tid (GHyb rel) (K2₀ (model isa)) n m cl c r g :=
  NPSafeP.of_ruleRXG (fwRuleG P A tid rd hL hA hA' rel hrelD) n m cl c r g h

/-- `fw_npSafeP_hyb` in option (S)'s frame `K2Scope AllocIds`
(`theorem1IIPure_of_relWritesF`). -/
theorem fw_npSafeP_hyb_S (P : Params) (A : Arch) (tid rd : Nat) (hL : MpLocs P) (hA : A.storeKind .plain ≠ .nt)
    (hA' : A.plainStore ≠ .rel) (rel : Loc → Pred) (hrelD : ∀ v, Pred.Pure (rel P.Dt) v) (n m : Nat) {cl : Prop}
    {c : Config isa} {r : Res} {g : Ghost} (h : InvXF P tid cl c r g) :
    NPSafeP (model isa) A (MpPost P rd) tid (GHyb rel) (K2Scope (model isa) AllocIds) n m cl c r g :=
  (fw_npSafeP_hyb P A tid rd hL hA hA' rel hrelD n m h).toAllocIds

end Rule

end Kraken.Promising.SLR.FenceW

#print axioms Kraken.Promising.SLR.FenceW.fw_prepay
#print axioms Kraken.Promising.SLR.FenceW.fw_npSafeP_hyb
#print axioms Kraken.Promising.SLR.FenceW.fw_npSafeP_hyb_S
