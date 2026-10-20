/-
The swap of the x64 spinlock worker (`xchgl %eax,(%rdi)`, position 5 → 6),
`HardCellsX.xchg : CellWPX P A tid 5` (`SLR/X64SpinRule.lean`). The x64 twin
of `wp_swpa` (`SLR/SwpAcquire.lean`), with the ISA-neutral helpers of
`SLR/SpinAcquire.lean`.

The swap is an `acqRel` RMW writing the low word `eax = 1`, at which
`lockPred` is pure, so the write attaches no slots
(`EvTree.eraseWPR_rmw_pendClaim`). Under TSO the write is a release, so it
may have been promised and prepaid (`OwnPend`): **both branches are real**.

- **Pending branch**: the swap fulfils the own pending promise `tw`
  (unpending it, `ErAt.fulfilPend`) and claims the message read. No other
  pending mark is lost (`tw` is held by no one afterwards), and no own
  pending promise remains (`OwnPend`'s uniqueness).
- **Non-pending branch**: the swap writes fresh or fulfils a non-pending
  promise and claims the message read. An own pending promise `ts` (prepaid
  `⟨Lk, 1⟩`) left behind lies below the write (`OwnPend`: every other own
  promise of `Lk` is above `ts`; a fresh write is above every message), so
  it is overtaken and the resulting thread has a dead promise, for which
  `WpPostR` asks nothing.

In both branches (`xchg_post`): reading a non-zero low word, the thread
stays `Fresh` (fractions only grow), with `LkFwd` (its forwarding item for
`Lk` is from this exclusive write); reading a zero low word, the claimed
slots contain the pool (`World.lock_claim'`), and the thread is `Holding`
(`holding_of_pool`), with the counter relation under `Good`
(`counterGood_of_good`) below `vrNew`: the read is not forwarded (`LkFwd`),
so the acquire read raises `vrNew` to the message's timestamp.

The proof is an `EraseWPR` proof (no dead branch is needed), turned into the
`EraseWPRD` form by `EvTree.EraseWPR.toD`.
-/
import Kraken.Promising.SLR.X64SpinRule
import Kraken.Promising.SLR.SpinAcquire
import Kraken.Promising.SLR.StoreHelpers
import Kraken.Promising.SLR.PromiseFulfil

namespace Kraken.Promising.SLR.X64SpinInv

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

omit layout hv in
/-- A write event's timestamp is below the written location's `coh`
afterwards. -/
theorem writeSuccs_coh_tw {A : Arch} {tid : Nat} {iv : InstrViews} {cx cx' : Ctx} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} {tw : Time} (hn : cx.prom.Nodup)
    (hc : cx' ∈ writeSuccs A tid iv cx k xcl l v tr extra) (hev : WriteEv tid cx cx' l v tr tw) :
    tw ≤ cx'.views.getCoh l := by
  rcases (mem_writeSuccs A tid).mp hc with ⟨t, ht, w, hw, -, -, -, hok, rfl⟩ | ⟨hok, rfl⟩
  · rcases hev.cases with ⟨-, htw, -⟩ | ⟨hm, -⟩
    · obtain rfl : t = tw := erase_inj hn htw hev.prom
      rw [afterWrite_getCoh]
      simp only [↓reduceIte]
      exact Nat.le_max_right _ _
    · exfalso
      have := congrArg Memory.last hm
      simp only [afterWrite, Memory.last_append] at this
      exact Nat.succ_ne_self _ this.symm
  · rcases hev.cases with ⟨hm, -, -⟩ | ⟨-, rfl⟩
    · exfalso
      have := congrArg Memory.last hm
      simp only [afterWrite, Memory.last_append] at this
      exact Nat.succ_ne_self _ this
    · rw [afterWrite_getCoh]
      simp only [↓reduceIte]
      exact Nat.le_max_right _ _

omit layout hv in
/-- The context after an RMW's write is ordered after it. -/
theorem rmwAfter_dord (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (cx : Ctx) :
    cx.DOrd (rmwAfter A k noRet l cx) := by
  unfold rmwAfter
  split
  · exact (Ctx.DOrd.rmwPost A cx k noRet l).trans (Ctx.DOrd.fenceStep _ _)
  · exact Ctx.DOrd.rmwPost A cx k noRet l

omit hv in
/-- **`Inv` after a step of thread `tid`** with new memory `m`. -/
theorem inv_withThread_xchg {P : Params} {tid : Nat} {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    {t t' : Thread isa} {m : Memory} (hW : World P.sys g) (ht : c.threads[tid]? = some t) {s : State}
    (hst : t'.st = s) (hF : Frame P s) (hL : LockWritesIn P.sys r m) {i : Nat} (hp : AtPos s i)
    (hph : Phase P tid cl i (eaxOf s) (ecxOf s) s.st.1.status.zf t'.views r)
    (hpp : PrepaidProm P tid cl i t' m r := by
      exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩) :
    Inv P tid cl (c.withThread tid t' m) r g := by
  have hn := lt_size_of_get? ht
  exact ⟨hW, t', by rw [Config.withThread_get? c t' m hn, ite_eq_left rfl], hst ▸ hF, hL, i, hst ▸ hp,
    hst ▸ hph, hpp⟩

omit hv in
/-- **After the swap's write**, in either branch: `WpPostR InvX` at the
continuation, for any ghost `g'` that grows `g`, keeps the pending marks of
outstanding promises, adds none, keeps `mayWrite`, and leaves no own pending
promise un-overtaken. -/
theorem xchg_post {P : Params} {A : Arch} {tid : Nat} (hLC : P.Lk ≠ P.C) (hxo : A.fwdXclOnlyPlain = true) {cl : Prop} {c : Config isa}
    {r : Res} {g g' : Ghost} {rF : Nat → Res} {t : Thread isa}
    (hW : World P.sys g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st) (hL : LockWritesIn P.sys r c.mem)
    (hfr : FreshN P tid r) (hfw : LkFwd P t.views)
    (E : Erase (setRes rF tid r) g (fun _ => True) c)
    {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs A (instrViews t (isa.deps t.st)) (fenceOptCtx A (ctx₀ t tid c.mem))
      (A.rmwKind .acqRel).loadKind false P.Lk false)
    {cx' : Ctx} {tw : Time}
    (hc : cx' ∈ writeSuccs A tid (instrViews t (isa.deps t.st)) x.2.2 (A.rmwKind .acqRel).storeKind true P.Lk
      (BitVec.setWidth 128 (eaxOf t.st)) (some x.1) (x.2.2.loadViews.getLastD 0))
    (hev : WriteEv tid x.2.2 cx' P.Lk (BitVec.setWidth 128 (eaxOf t.st)) (some x.1) tw)
    (hrd : x.2.2.mem.read? P.Lk x.1 = some x.2.1) (hun : ¬ g.Claimed (P.Lk, x.1))
    (hle : g.Le g') (hsub : ∀ ts ∈ g'.pend, ts ∈ g.pend)
    (hkeep : ∀ ts, ts ∈ g.pend →
      (ts ∈ cx'.prom ∨ ∃ (i : Nat) (t' : Thread isa), i ≠ tid ∧ c.threads[i]? = some t' ∧ ts ∈ t'.prom) →
      ts ∈ g'.pend)
    (hmw : ∀ y, mayWrite ((r.op (Res.prod ((claimedSlots g P.Lk x.1).map (fun s : Slot => s.res)))).addW P.Lk
      (BitVec.setWidth 128 (eaxOf t.st), tw)) g' y → mayWrite r g y)
    (hown : ∀ ts ∈ cx'.prom, ts ∈ g'.pend → cx'.Overtaken) :
    WpPostR (InvX P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t
      (goto t.st { t.st.st.1 with regs := t.st.st.1.regs.set (.low .rax .W32) (BitVec.setWidth 32 x.2.1) }
        ((layout spinWorker).addrOf 6))
      ((r.op (Res.prod ((claimedSlots g P.Lk x.1).map (fun s : Slot => s.res)))).addW P.Lk
        (BitVec.setWidth 128 (eaxOf t.st), tw)) g'
      (rmwAfter A .acqRel false P.Lk cx') := by
  have hn := lt_size_of_get? ht
  obtain ⟨hfr, htid⟩ := hfr
  have hN0 : 0 < P.N := by omega
  have hpos : 0 < (r.wr P.Lk).q := by have := one_div_pos hN0; have := hfr.2.2; grind
  obtain ⟨hm1, hp1⟩ := fenceOptCtx_memProm A (ctx₀ t tid c.mem)
  obtain ⟨hm2, hp2⟩ := readSuccs_memProm A _ hx
  obtain ⟨hm3, hp3⟩ := rmwAfter_memProm A .acqRel false P.Lk cx'
  have hfw' : ∀ f, (fenceOptCtx A (ctx₀ t tid c.mem)).views.getFwd P.Lk = some f → f.xcl = true := by
    intro f hf; rw [fenceOptCtx_getFwd] at hf; exact hfw f hf
  have hrv := readSuccs_acq_le hx rfl rfl fun f hf _ => ⟨hfw' f hf, hxo⟩
  have hlast : c.mem.last ≤ (rmwAfter A .acqRel false P.Lk cx').mem.last := by
    rw [hm3]
    have := hev.last_le; rw [hm2, hm1] at this; exact this
  refine ⟨hle, fun ts h h' => hkeep ts h (by rw [hp3] at h'; exact h'), hsub, hmw, fun w hw => ?_,
    fun t' ht' hdead => ⟨?_, ?_, ?_⟩⟩
  · rw [writtenCx_writeEv' (hm2.trans hm1) (hp2.trans hp1) hev hm3 hp3 hw]
    exact hpos
  · -- `Inv` at position 6
    obtain ⟨hpr', hvs⟩ := finishInstr_relKey ht'
    refine inv_withThread_xchg (i := 6) (hW.mono hle) ht (finishInstr_st ht') (hF.goto (by simp) (by simp) rfl)
      ?_ rfl ?_
    · have htw : tw ≤ (rmwAfter A .acqRel false P.Lk cx').mem.last := by
        rw [hm3]
        rcases hev.cases with ⟨hm', -, hg⟩ | ⟨hm', rfl⟩
        · rw [hm']; exact Memory.last_le_of_get?_eq_some _ hg
        · rw [hm', Memory.last_append]; exact Nat.le_refl _
      have hposT : 0 < ((total (setRes rF tid r) g c).wr P.Lk).q := by
        unfold total threadsRes
        exact Res.pos_op.mpr (.inl (Res.pos_prod_of_mem (List.mem_map.mpr ⟨tid, List.mem_range.mpr hn, rfl⟩)
          (by rw [setRes_self]; exact hpos)))
      intro p hp'
      rcases (Res.addW_X_self _ _ _ _).mp hp' with hp' | ⟨-, rfl⟩
      · rcases hp' with hp' | hp'
        · exact Nat.le_trans (hL p hp') hlast
        · have hX : ((total (setRes rF tid r) g c).wr P.Lk).X p := by
            unfold total; rw [slotsRes_claimed g P.Lk x.1]; exact .inr (.inl hp')
          rcases (E.writes P.Lk (.inl hposT) p).mp hX with ⟨h0, -⟩ | ⟨w, hw, -⟩
          · rw [h0]; exact Nat.zero_le _
          · exact Nat.le_trans (Memory.last_le_of_get?_eq_some _ hw) hlast
      · exact htw
    · have hvr : x.1 ≤ t'.views.vrNew := by
        have h1 : t'.views.vrNew = (rmwAfter A .acqRel false P.Lk cx').views.vrNew := by
          simpa using congrArg Views.vrNew hvs
        rw [h1]
        exact Nat.le_trans hrv.1 (Nat.le_trans (Nat.le_of_eq (writeSuccs_vrNew hc).symm) (rmwAfter_vrNew _ _ _ _))
      simp only [Phase, eaxOf, get_set_low_rax]
      split
      · rename_i hz
        have hrd' : c.mem.read? P.Lk x.1 = some x.2.1 := by rw [hm2, hm1] at hrd; exact hrd
        obtain ⟨R, R', hprod, hgb⟩ := World.lock_claim' (P := P.sys) hW E hrd' hz hun
        have hval := E.valid_claim hn P.Lk x.1
        simp only [Res.prod] at hprod hval ⊢
        rw [hprod] at hval ⊢
        have hlk : 1 / (P.N : Rat) ≤ (((r.op (R.op R')).addW P.Lk
            (BitVec.setWidth 128 (eaxOf t.st), tw)).wr P.Lk).q := by
          rw [Res.addW_q]; exact Rat.le_trans hfr.2.2 (Perm.le_op_left _ _)
        rcases hgb with ⟨k, S, ts, hpool, hX, hmax, hk, hts⟩ | ⟨hRL, S, hpool⟩
        · exact ⟨S, k, holding_of_pool (P := P.sys) htid hN0 hfr hval hpool, fun _ =>
            ⟨hlk, .inl ⟨ts, counterGood_of_good (P := P.sys) hLC hval hpool.1 hX hmax hk, Nat.le_trans hts hvr⟩⟩⟩
        · refine ⟨S, 0, holding_of_pool (P := P.sys) htid hN0 hfr hval hpool, fun _ => ⟨hlk, .inr ?_⟩⟩
          rw [Res.addW_q]
          change _ < (r.wr P.Lk).q + ((R.wr P.Lk).q + (R'.wr P.Lk).q)
          have := hfr.2.2; have := (R'.wr P.Lk).nonneg; grind
      · have hge : ∀ y, (r.wr y).q ≤ (((r.op (Res.prod ((claimedSlots g P.Lk x.1).map
            (fun s : Slot => s.res)))).addW P.Lk (BitVec.setWidth 128 (eaxOf t.st), tw)).wr y).q :=
          fun y => by rw [Res.addW_q]; exact Perm.le_op_left _ _
        refine ⟨⟨⟨Rat.le_trans hfr.1 (hge _), Rat.le_trans hfr.2.1 (hge _), Rat.le_trans hfr.2.2 (hge _)⟩, htid⟩,
          ?_⟩
        intro f hf
        have h5 : t'.views.fwdb = (rmwAfter A .acqRel false P.Lk cx').views.fwdb := by
          simpa using congrArg Views.fwdb hvs
        have : (rmwAfter A .acqRel false P.Lk cx').views.getFwd P.Lk = some f := by
          simpa only [Views.getFwd, h5] using hf
        rw [rmwAfter_getFwd] at this
        exact writeSuccs_getFwd_xcl hc f this
  · -- the pending marks are messages
    intro ts h
    show ts ≤ (rmwAfter A .acqRel false P.Lk cx').mem.last
    exact Nat.le_trans (E.pend_le (hsub ts h)) hlast
  · -- no own pending promise is left alive
    intro t'' ht'' ts hts hpd
    exfalso
    rw [Config.withThread_get? _ _ _ hn] at ht''
    simp only [ite_true, Option.some.injEq] at ht''
    subst ht''
    rw [(finishInstr_relKey ht').1, hp3] at hts
    have ho := ((hown ts hts hpd).dord (rmwAfter_dord A .acqRel false P.Lk cx')).finish ht'
    rw [ho] at hdead
    cases hdead

/-- **The swap** (`xchgl %eax,(%rdi)`, position 5 → 6). -/
theorem wp_xchg {P : Params} {A : Arch} {tid : Nat} (hLC : P.Lk ≠ P.C) (hxo : A.fwdXclOnlyPlain = true) :
    CellWPX P A tid 5 := by
  intro cl c r g g₀ rF t tree hW ht hF hL hp hph hpp hg₀ hex E hM hWf hnp hOP
  have hn := lt_size_of_get? ht
  have hnd : t.prom.Nodup := hM.promNodup tid t ht
  rw [exec_xchg t.st (hF.at hp (by decide)) hF.rdi hF.dl] at hex
  cases hex
  simp only [Phase] at hph
  obtain ⟨hfr, hfw, heax⟩ := hph
  have hN0 : 0 < P.N := by have := hfr.2; omega
  have hpos : 0 < (r.wr P.Lk).q := by have := one_div_pos hN0; have := hfr.1.2.2; grind
  obtain ⟨hm1, hp1⟩ := fenceOptCtx_memProm A (ctx₀ t tid c.mem)
  refine EvTree.EraseWPR.toD (fun _ _ _ _ h => h) _ _ _ _ ?_
  refine EvTree.eraseWPR_rmw_pendClaim hn (fun x _ h => by simp at h) ?_ ?_
  · -- the pending branch: fulfil the own prepaid promise
    intro x hx new hop cx' tw hc hev hpd hrd hun
    obtain rfl := Option.some.inj hop
    obtain ⟨hm2, hp2⟩ := readSuccs_memProm A _ hx
    have hfw' : ∀ f, (fenceOptCtx A (ctx₀ t tid c.mem)).views.getFwd P.Lk = some f → f.xcl = true := by
      intro f hf; rw [fenceOptCtx_getFwd] at hf; exact hfw f hf
    have hrv := readSuccs_acq_le hx rfl rfl fun f hf _ => ⟨hfw' f hf, hxo⟩
    have hget : c.mem.get? tw = some ⟨P.Lk, BitVec.setWidth 128 (eaxOf t.st), tid⟩ ∧ tw ∈ t.prom := by
      rcases hev.cases with ⟨-, htw, hg⟩ | ⟨-, rfl⟩
      · rw [hm2, hm1] at hg; rw [hp2, hp1] at htw; exact ⟨hg, htw⟩
      · have := E.pend_le hpd; rw [hm2, hm1] at *; exact absurd this (Nat.not_succ_le_self _)
    obtain ⟨hget, htw⟩ := hget
    refine ⟨hpos, fun _ => ?_, ?_⟩
    · have h1 : x.2.2.views.vwNew ≤ (rmwAfter A .acqRel false ⟨P.l, 4⟩ cx').views.vwNew :=
        ((writeSuccs_vmono A tid hc).trans (rmwAfter_vmono A .acqRel false ⟨P.l, 4⟩ cx')).vwNew
      simp only [Views.wfloor]; omega_t
    · refine xchg_post hLC hxo hW ht hF hL hfr hfw E hx hc hev hrd hun
        ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩ (fun ts h => (mem_unpend_pend.mp h).1)
        (fun ts hts hor => ?_) (fun y h => mayWrite_claim (tw := tw) h) (fun ts hts hpd' => ?_)
      · refine mem_unpend_pend.mpr ⟨hts, fun he => ?_⟩
        subst he
        rcases hor with h | ⟨i, t'', hi, hti, hpr⟩
        · rw [hev.prom, hp2, hp1] at h
          exact ((List.Nodup.mem_erase_iff hnd).mp h).1 rfl
        · obtain ⟨w, hw, hwt⟩ := hM.promWf i t'' hti _ hpr
          rw [hget] at hw
          cases hw
          exact hi hwt.symm
      · exfalso
        obtain ⟨hpd'', hne⟩ := mem_unpend_pend.mp hpd'
        rw [hev.prom, hp2, hp1] at hts
        exact hne ((hOP t ht tw htw hpd).2.1 ts ((List.Nodup.mem_erase_iff hnd).mp hts).2 hpd'')
  · -- the non-pending branch
    intro x hx new hop cx' tw hc hev hpd hrd hun _
    obtain rfl := Option.some.inj hop
    obtain ⟨hm2, hp2⟩ := readSuccs_memProm A _ hx
    have hfw' : ∀ f, (fenceOptCtx A (ctx₀ t tid c.mem)).views.getFwd P.Lk = some f → f.xcl = true := by
      intro f hf; rw [fenceOptCtx_getFwd] at hf; exact hfw f hf
    have hrv := readSuccs_acq_le hx rfl rfl fun f hf _ => ⟨hfw' f hf, hxo⟩
    have hnew : BitVec.setWidth 32 (BitVec.setWidth 128 (eaxOf t.st)) ≠ 0 := by
      rw [setWidth_32_128, heax]; decide
    refine ⟨false, [], (r.op (Res.prod ((claimedSlots g P.Lk x.1).map (fun s : Slot => s.res)))).addW P.Lk
      (BitVec.setWidth 128 (eaxOf t.st), tw), hpos, fun h => absurd h (by decide), fun _ => ⟨rfl, ?_⟩,
      by simp [Res.op_unit], fun _ => rfl, fun _ => ?_, ?_⟩
    · rw [hW.1]; exact lockPred_pure hnew
    · have h1 : x.2.2.views.vwNew ≤ (rmwAfter A .acqRel false ⟨P.l, 4⟩ cx').views.vwNew :=
        ((writeSuccs_vmono A tid hc).trans (rmwAfter_vmono A .acqRel false ⟨P.l, 4⟩ cx')).vwNew
      simp only [Views.wfloor]; omega_t
    · refine xchg_post hLC hxo hW ht hF hL hfr hfw E hx hc hev hrd hun
        ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩ (fun ts h => h) (fun ts h _ => h)
        (fun y h => mayWrite_claim h) (fun ts hts hpd' => ?_)
      -- an own pending promise left behind is overtaken by the write
      have hts' : ts ∈ t.prom := by
        rw [hev.prom, hp2, hp1] at hts; exact List.mem_of_mem_erase hts
      have hne : ts ≠ tw := fun he => hpd (he ▸ hpd')
      obtain ⟨hpos5, -, habove⟩ := hOP t ht ts hts' hpd'
      have hget : c.mem.get? ts = some ⟨P.Lk, BitVec.setWidth 128 (eaxOf t.st), tid⟩ := by
        rcases hpos5 with ⟨-, hg⟩ | ⟨h10, -⟩ | ⟨h11, -⟩
        · exact hg
        · exact absurd (atPos_eq_rel (i := 5) (by decide) (by decide) hp h10) (by decide)
        · exact absurd (atPos_eq_rel (i := 5) (by decide) (by decide) hp h11) (by decide)
      have hlt : ts < tw := by
        rcases hev.cases with ⟨-, htw, hg⟩ | ⟨-, rfl⟩
        · rw [hm2, hm1] at hg; rw [hp2, hp1] at htw
          exact habove tw htw (Ne.symm hne) _ _ hg hget rfl
        · rw [hm2, hm1]
          exact Nat.lt_succ_of_le (Memory.last_le_of_get?_eq_some _ hget)
      have hcoh := writeSuccs_coh_tw (by rw [hp2, hp1]; exact hnd) hc hev
      refine ⟨ts, hts, _, writeSuccs_get? hc (by rw [hm2, hm1]; exact hget), ?_⟩
      exact Nat.le_trans (Nat.le_of_lt hlt) hcoh

end Kraken.Promising.SLR.X64SpinInv
