/-
The MP writer's resource cells: the data store `str w2, [x1]` (position
1 → 2), the flag release `stlr w3, [x0]` (position 3 → 4), the lift of a
cell proof from a state with no own pending promise to the `ThreadRuleRX`
form (`mp_lift`, an instance of the generic `liftOb_invXOf`), and the prepay
obligation (`mp_prepay`, of the generic form `PrepayObG`).

- **Data store**: `Dt`'s release predicate is pure (`WorldW`), so the shape
  is `EvTree.eraseWPR_store_pure`. The writer holds all of `Dt` with only
  the initial write, so `(1, tw)` becomes the maximal write, below the new
  `vwOld` (a non-NT store). A pending fulfilment is impossible: the writer
  has no own pending promise before position 3.
- **The release split** (`release_split_mp`): the flag message `(Fl, 1, tw)`
  takes all of `Dt` (`Res.take`, `relFracMp`), whose maximal write `(1, ts)`
  has `ts ≤ vwOld < tw` — the flag's predicate `φ` at a non-zero value
  (`Good`). The writer keeps `W` and its share of `Fl` (`Res.leave`).
- **Flag release** from `Own1` (`EvTree.eraseWPR_store_rel`, then `mp_lift`)
  or from `Prepaid` (`EvTree.eraseWPRD_store_pendOrDead`: the pending
  fulfilment of the prepaid promise reaches position 4; a fresh write would
  overtake the prepaid promise, a dead branch). Templates: `SwpStlr`.
- **Prepay**: only the `stlr` fulfils a promise with a release store
  (`relFulfils_posW`; the data store is plain, `A.plainStore ≠ .rel`); from
  `Own1`, the release split at `|M| + 1` and `Erase.prepay_exempt`; from
  `Prepaid`, a second prepayment would leave the first prepaid promise dead.
  Template: `SwpPrepay`.

The reader has no prepay obligation of substance: none of its instructions
stores, so `Thread.RelFulfilsLive` is false by inspection of its trees and it
uses the plain `ThreadRuleR` (`SLR/MpRule.lean`).
-/
import Kraken.Promising.SLR.MpCells
import Kraken.Promising.SLR.RuleObligationsX
import Kraken.Promising.SLR.StoreHelpers
import Kraken.Promising.SLR.SpinRelease
import Kraken.Promising.SLR.ThreadRuleXLift

namespace Kraken.Promising.SLR.Mp

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees

variable [layout : _root_.Layout]

/-! ## World facts -/

omit layout in
theorem WorldW.mono {P : Params} {g g₁ : Ghost} (h : WorldW P g) (hle : g.Le g₁) : WorldW P g₁ :=
  ⟨by rw [hle.rel]; exact h.1, fun v => by rw [hle.rel]; exact h.2 v⟩

omit layout in
/-- The flag's predicate is impure at the written value `1`. -/
theorem flag_impure {P : Params} {g : Ghost} (hW : WorldW P g) : ¬ Pred.Pure (g.rel P.Fl) 1#128 := by
  rw [hW.1]; exact flagPred_impure (by decide)

omit layout in
theorem one_128 : BitVec.setWidth 128 (1 : BitVec 32) = 1#128 := by decide

/-! ## The data store -/

section WriterCells

variable [hw : Executable.ValidLayout (layout mpWriter)]

/-- **The data store** `str w2, [x1]` (position 1 → 2). -/
theorem wpW_str {P : Params} {A : Arch} {tid : Nat} (hA : A.storeKind .plain ≠ .nt) : CellW P A tid 1 := by
  intro cl' c r g rF t tree hW ht hF hp hph hex E hM hpd
  have hn := lt_size_of_get? ht
  have hnd : t.prom.Nodup := hM.promNodup tid t ht
  rw [exec_w_str t.st (hF.at hp (by decide)) hF.x1 hF.dd] at hex
  cases hex
  simp only [PhaseW] at hph
  obtain ⟨⟨hq, h0, hWq, hFq⟩, hx2⟩ := hph
  rw [hx2, one_128]
  refine EvTree.eraseWPR_store_pure hn (by rw [hq]; decide) (hW.2 _) ?_ ?_
  · -- a pending fulfilment: the writer has no own pending promise here
    intro cx' tw _ hev hpd'
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
      refine invW_withThread (i := 2) hW ht (finishInstr_st ht') (hF.goto rfl rfl rfl) rfl ?_
        (fun h => absurd h (by decide))
      simp only [PhaseW, Own1, Res.addW_q]
      refine ⟨hq, ⟨tw, (Res.addW_X_self _ _ _ _).mpr (.inr ⟨by rw [hq]; decide, rfl⟩), fun p hp' => ?_, ?_⟩,
        hWq, hFq⟩
      · rcases (Res.addW_X_self _ _ _ _).mp hp' with hp' | ⟨-, rfl⟩
        · rw [h0 p hp']; exact Nat.zero_le _
        · exact Nat.le_refl _
      · rw [hvw', hvw]
        have hnt : (A.storeKind StoreKind.plain == StoreKind.nt) = false := by
          revert hA; cases A.storeKind StoreKind.plain <;> decide
        simp only [hnt, Bool.false_eq_true, ↓reduceIte]
        exact Nat.le_max_right _ _

end WriterCells

/-! ## The release split -/

/-- The fraction the flag message takes: all of `Dt`. -/
def relFracMp (Dt : Loc) (x : Loc) : Rat := if x = Dt then 1 else 0

omit layout in
/-- **The release split**: the flag message `(Fl, 1, tw)` carries all of
`Dt` (`Good` at `tw`); the writer keeps `W` and its share of `Fl`. -/
theorem release_split_mp {P : Params} (hL : MpLocs P) {r : Res} {vs : Views} (h : Own1 P vs r) {tw : Time}
    (hvw : vs.vwOld < tw) :
    ∃ R r' : Res, r'.op R = r.addW P.Fl (1#128, tw) ∧ (∀ y ι, R.acq y ι = 0) ∧ Good P.Dt tw R ∧
      (r'.wr P.Dt).q = 0 ∧ 1 ≤ (r'.wr P.W).q ∧ 0 < (r'.wr P.Fl).q := by
  obtain ⟨hq, ⟨ts, hX, hmax, hts⟩, hWq, hFq⟩ := h
  have hf0 : ∀ x, 0 ≤ relFracMp P.Dt x := fun x => by unfold relFracMp; split <;> decide
  have hfle : ∀ x, relFracMp P.Dt x ≤ ((r.addW P.Fl (1#128, tw)).wr x).q := fun x => by
    rw [Res.addW_q]; unfold relFracMp; split
    · next he => rw [he, hq]; decide
    · exact (r.wr x).nonneg
  have hDt : (r.addW P.Fl (1#128, tw)).wr P.Dt = r.wr P.Dt := Res.addW_wr_ne _ _ (Ne.symm hL.fl_dt)
  have hfD : relFracMp P.Dt P.Dt = 1 := by simp [relFracMp]
  have hfW : relFracMp P.Dt P.W = 0 := by simp [relFracMp, hL.wd]
  have hfF : relFracMp P.Dt P.Fl = 0 := by simp [relFracMp, hL.fl_dt]
  refine ⟨_, _, Res.leave_op_take _ _ hf0 hfle, fun _ _ => rfl, ⟨by rw [Res.take_q, hfD], ts, ?_, fun p hp => ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [Res.take_X_pos _ _ _ (by rw [hfD]; decide), hDt]; exact hX
  · rw [Res.take_X_pos _ _ _ (by rw [hfD]; decide), hDt] at hp; exact hmax p hp
  · exact Nat.le_of_lt (Nat.lt_of_le_of_lt hts hvw)
  · rw [Res.leave_q, hfD, Res.addW_q, hq]; grind
  · rw [Res.leave_q, hfW, Res.addW_q]; grind
  · rw [Res.leave_q, hfF, Res.addW_q]; grind

/-! ## The obligations of the writer's `ThreadRuleRX` -/

/-- A writer cell proof directly in the `ThreadRuleRX` (dead-branch) form. -/
def CellWX (P : Params) (A : Arch) (tid : Nat) (i : Nat) : Prop :=
  ∀ {cl' : Prop} {c : Config isa} {r : Res} {g : Ghost} (rF : Nat → Res) (t : Thread isa)
    (tree : EvTree isa.State), WorldW P g → c.threads[tid]? = some t → FrameW P t.st →
    AtPos mpWriter t.st i → PhaseW P i (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec) t.views r → PrepaidProm P tid i t c.mem r →
    isa.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → OwnPendW P tid c r g →
    tree.EraseWPRD A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvXW P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem)

/-! ## The lift -/

/-- **The lift** of a writer cell proof from a state with no own pending
promise: `InvXW` is an `InvXOf` invariant, so the generic `liftOb_invXOf`
(`SLR/RuleObligationsX.lean`) applies. -/
theorem mp_lift {P : Params} {A : Arch} {tid : Nat} : LiftObG A tid (InvW P tid) (InvXW P tid) :=
  liftOb_invXOf A tid (InvW P tid)
    (fun t _ r g ts => AtPos mpWriter t.st 3 ∧ (r.wr P.Dt).q = 0 ∧ ∀ ts' ∈ t.prom, ts' ∈ g.pend → ts' = ts)

/-! ## The flag release -/

section WriterRelease

variable [hw : Executable.ValidLayout (layout mpWriter)]

omit hw in
/-- **The flag release from `Own1`**, as a `CellW`-style erasure WP. -/
theorem wpW_stlr_own {P : Params} {A : Arch} {tid : Nat} (hL : MpLocs P) {cl' : Prop} {c : Config isa}
    {r : Res} {g : Ghost} (rF : Nat → Res) (t : Thread isa) (hW : WorldW P g) (ht : c.threads[tid]? = some t)
    (hF : FrameW P t.st) (hown : Own1 P t.views r)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hM : c.MachInv) (hnp : ∀ ts ∈ t.prom, ts ∉ g.pend) :
    (EvTree.store .rel false P.Fl 1#128 fun _ => .done (goto t.st t.st.st.1 ((layout mpWriter).addrOf 4))).EraseWPR
      A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvW P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  have hn := lt_size_of_get? ht
  have hpos : 0 < (r.wr P.Fl).q := hown.2.2.2
  refine EvTree.eraseWPR_store_rel hn hpos ?_ ?_
  · -- a pending write: neither an own (unpended) promise nor fresh
    intro cx' tw _ hev hpd
    exfalso
    rcases hev.cases with ⟨-, htw, -⟩ | ⟨-, rfl⟩
    · exact hnp tw htw hpd
    · exact Nat.not_succ_le_self _ (E.pend_le hpd)
  · intro cx' tw hc hev hpd _
    obtain ⟨hm', htw⟩ := E.fresh_of_impure ht rfl rfl hev hpd (flag_impure hW)
    have hvw : t.views.vwOld < tw := htw ▸ SpinCommon.writeSuccs_fresh_vwOld hc rfl hm'
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
    · exact invW_withThread (i := 4) (hW.mono hgle) ht (finishInstr_st ht') (hF.goto rfl rfl rfl) rfl
        (by simp only [PhaseW]; exact hWq) (fun h => absurd h (by decide))

omit hw in
/-- **The flag release from `Prepaid`**, directly in the dead-branch form
(template `wp_stlr_prepaid`). -/
theorem wpW_stlr_prepaid {P : Params} {A : Arch} {tid : Nat} {cl' : Prop} {c : Config isa} {r : Res}
    {g : Ghost} (rF : Nat → Res) (t : Thread isa)
    (hW : WorldW P g) (ht : c.threads[tid]? = some t) (hF : FrameW P t.st) (hpre : Prepaid P r)
    (hts : ∃ ts ∈ t.prom, c.mem.get? ts = some ⟨P.Fl, 1#128, tid⟩)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hM : c.MachInv)
    (huniq : ∀ ts ∈ t.prom, ts ∈ g.pend → ∀ ts' ∈ t.prom, ts' ∈ g.pend → ts' = ts) :
    (EvTree.store .rel false P.Fl 1#128 fun _ => .done (goto t.st t.st.st.1 ((layout mpWriter).addrOf 4))).EraseWPRD
      A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvXW P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  have hn := lt_size_of_get? ht
  have hnd : t.prom.Nodup := hM.promNodup tid t ht
  refine EvTree.eraseWPRD_store_pendOrDead hn ?_ ?_
  · -- the pending fulfilment
    intro cx' tw _ hev hpd
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
    · exact invW_withThread (i := 4) (hW.mono hgle) ht (finishInstr_st ht') (hF.goto rfl rfl rfl) rfl
        (by simp only [PhaseW]; exact hpre.2.1) (fun h => absurd h (by decide))
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
  · -- every other write is fresh and overtakes the prepaid promise
    intro cx' tw hc hev hpd _ _
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

/-- **The flag release** `stlr w3, [x0]` (position 3 → 4). -/
theorem wpW_stlr {P : Params} {A : Arch} {tid : Nat} (hL : MpLocs P) : CellWX P A tid 3 := by
  intro cl' c r g rF t tree hW ht hF hp hph hpp hex E hM hOP
  rw [exec_w_stlr t.st (hF.at hp (by decide)) hF.x0 hF.df] at hex
  cases hex
  simp only [PhaseW] at hph
  obtain ⟨hph, hx3⟩ := hph
  rw [hx3, one_128]
  rcases hph with hown | hpre
  · have hnp : ∀ ts ∈ t.prom, ts ∉ g.pend := fun ts hts hpd' => by
      have h0 := (hOP t ht ts hts hpd').2.1
      rw [hown.1] at h0
      exact absurd h0 (by decide)
    exact mp_lift rF t _ ht E hM hnp (wpW_stlr_own hL rF t hW ht hF hown E hM hnp)
  · exact wpW_stlr_prepaid rF t hW ht hF hpre (hpp rfl hpre.1) E hM
      fun ts hts hpd' ts' hts' hpd'' => (hOP t ht ts hts hpd').2.2 ts' hts' hpd''

end WriterRelease

/-! ## Environment and own pending promises -/

/-- **`InvW` across an environment extension**: the thread keeps its state
and views; the memory grows (the prepaid promise stays a message). -/
theorem invW_env {P : Params} {tid : Nat} {cl : Prop} {c c₁ : Config isa} {r : Res}
    {g g₁ : Ghost} (h : InvW P tid cl c r g) (he : EnvExt tid c c₁) (hle : g.Le g₁) : InvW P tid cl c₁ r g₁ := by
  obtain ⟨hW, t, ht, hF, i, hp, hph, hpp⟩ := h
  obtain ⟨-, hpre, hth⟩ := he
  obtain ⟨ps, ht₁, -⟩ := hth t ht
  refine ⟨hW.mono hle, _, ht₁, hF, i, hp, hph, fun h3 hq => ?_⟩
  obtain ⟨ts, hts, hget⟩ := hpp h3 hq
  exact ⟨ts, List.mem_append_left _ hts, Memory.get?_of_prefix hpre hget⟩

/-- **`OwnPendW` at the extension** (template `ownPend_transport`). -/
theorem ownPendW_transport {P : Params} {tid : Nat} {cl : Prop} {c₀ c : Config isa} {r : Res}
    {g₀ g : Ghost} (h : InvXW P tid cl c₀ r g₀) (he : EnvExt tid c₀ c) {t : Thread isa}
    (ht : c.threads[tid]? = some t) (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) : OwnPendW P tid c r g := by
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
  · obtain ⟨h3, hq, hu⟩ := hOP t₀ ht₀ ts h h0
    refine ⟨h3, hq, fun ts' hts' hpd' => ?_⟩
    have h0' := hnp ts' hts' hpd'
    rcases List.mem_append.mp hts' with h' | h'
    · exact hu ts' h' h0'
    · exact absurd (hPI ts' h0') (Nat.not_le.mpr (hps ts' h'))
  · exact absurd (hPI ts h0) (Nat.not_le.mpr (hps ts h))

/-! ## The prepayment -/

section WriterPrepay

variable [hw : Executable.ValidLayout (layout mpWriter)]

/-- **Only the flag release fulfils a promise with a release store**
(template `relFulfils_pos`), and it fulfils a flag message of the value of
`W3` above `vwOld`; a live run leaves every other outstanding flag promise
above `ts`. -/
theorem relFulfils_posW {P : Params} {A : Arch} {tid : Nat} (hA : A.plainStore ≠ .rel)
    {t : Thread isa} {mem : Memory} {ts : Time} {i : Nat}
    (hF : FrameW P t.st) (hp : AtPos mpWriter t.st i) (hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)
    (hb : ∀ p ∈ t.prom, p ≤ mem.last) (h : t.RelFulfilsLive A tid ts mem) :
    i = 3 ∧ (∃ w, mem.get? ts = some w ∧ w.loc = P.Fl ∧
        w.val = BitVec.setWidth 128 (BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec)) ∧ t.views.vwOld < ts ∧
      ∀ p ∈ t.prom, p ≠ ts → ∀ w, mem.get? p = some w → w.loc = P.Fl → ts < p := by
  obtain ⟨tree, hex, hrf⟩ := h
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · rw [exec_w_mov2 t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_w_str t.st (hF.at hp (by decide)) hF.x1 hF.dd] at hex; cases hex
    simp [EvTree.RelFulfilsLive, Arch.storeKind, hA] at hrf
  · rw [exec_w_mov3 t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_w_stlr t.st (hF.at hp (by decide)) hF.x0 hF.df] at hex; cases hex
    simp only [EvTree.RelFulfilsLive, or_false] at hrf
    obtain ⟨cx', hc, ⟨hk, hin, hout⟩, hnd⟩ := hrf
    obtain ⟨hw, hok, hlive⟩ := SpinCommon.writeSuccs_fulfil_live hc hb hin hout hnd
    exact ⟨rfl, hw, SpinCommon.writeOk_rel_vwOld hk hok, hlive⟩
  · rw [exec_end_w hF hp] at hex; cases hex

/-- **The prepay obligation** of the writer. -/
theorem mp_prepay {P : Params} {A : Arch} {tid : Nat} (hL : MpLocs P) (hA : A.plainStore ≠ .rel) :
    PrepayObG A tid (InvXW P tid) := by
  intro cl c₀ c r g₀ g rF t₁ w h he hle ht E hM hnp hrel
  have htw : (c.mem.append { w with tid }).2 = c.mem.last + 1 := rfl
  rw [htw] at hrel ⊢
  have hOP := ownPendW_transport h he ht hnp
  obtain ⟨hW, t, ht', hF, i, hp, hph, hpp⟩ := invW_env h.1 he hle
  rw [ht] at ht'
  obtain rfl : t₁ = t := Option.some.inj ht'
  have hn := lt_size_of_get? ht
  have hb : ∀ p ∈ t₁.prom ++ [c.mem.last + 1], p ≤ (c.mem.append { w with tid }).1.last := fun p hp' => by
    rw [Memory.last_append]
    rcases List.mem_append.mp hp' with h1 | h1
    · obtain ⟨w', hw', -⟩ := hM.promWf tid t₁ ht p h1
      exact Nat.le_succ_of_le (c.mem.last_le_of_get?_eq_some hw')
    · rw [List.mem_singleton.mp h1]; exact Nat.le_refl _
  obtain ⟨rfl, ⟨w', hw', hwl, hwv⟩, hvw, hlive⟩ := relFulfils_posW (P := P)
    (t := { t₁ with prom := t₁.prom ++ [c.mem.last + 1] }) hA hF hp (PhaseW.pos hph) hb hrel
  simp only [PhaseW] at hph
  obtain ⟨hph, hx3⟩ := hph
  rw [Memory.get?_append_last] at hw'
  obtain rfl := Option.some.inj hw'
  obtain ⟨wl, wv, wt⟩ := w
  simp only at hwl hwv
  rw [hx3, one_128] at hwv
  subst hwl hwv
  rcases hph with hown | hpre
  case inr =>
    -- a second prepayment: the fresh release at `|M| + 1` would leave the
    -- prepaid promise `ts ≤ |M|` dead
    obtain ⟨ts, hts, hget⟩ := hpp rfl hpre.1
    have hle : ts ≤ c.mem.last := c.mem.last_le_of_get?_eq_some hget
    have h1 := hlive ts (List.mem_append_left _ hts) (fun he => Nat.not_succ_le_self _ (he ▸ hle)) _
      (by rw [Memory.get?_append_of_le _ _ _ hle]; exact hget) rfl
    exact absurd h1 (Nat.not_lt.mpr (Nat.le_succ_of_le hle))
  -- from `Own1`: no own promise is pending
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
  · -- `InvW`: `Prepaid` at position 3
    refine invW_withThread (i := 3) (t' := { t₁ with prom := t₁.prom ++ [c.mem.last + 1] }) (hW.mono hgle)
      ht rfl hF hp ?_ fun _ _ => ⟨c.mem.last + 1, List.mem_append_right _ (List.mem_singleton_self _),
        Memory.get?_append_last _ _⟩
    simp only [PhaseW]
    exact ⟨.inr ⟨hD', hWq', hFq'⟩, hx3⟩
  · -- `PendIn`
    intro ts h
    show ts ≤ (c.mem.append _).1.last
    rw [Memory.last_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (E.pend_le h)
  · -- `OwnPendW`: the promise is the only own pending one
    intro t'' ht'' ts h1 h2
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

end WriterPrepay

end Kraken.Promising.SLR.Mp
