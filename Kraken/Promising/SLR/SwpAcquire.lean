/-
The acquiring swap of the SWP spinlock worker (`swpa w3, w2, [x0]`, position
3 → 4) for `ThreadRuleRX` (`CellWPN P A tid 3`, `SLR/SwpRuleX.lean`).

The swap is an acquire RMW writing the low word of `W3 = 1` (`Frame.x3`), at
which `lockPred` is pure, so the write attaches no slots
(`EvTree.eraseWPR_rmw_pendClaim`, non-pending branch at `rel = false`):

- the pending branch is impossible: away from position 13 the thread has no
  pending promise (`CellWPN`'s hypothesis), and a fresh write is above every
  pending mark (`Erase.pend`);
- the thread claims the update slots of the message read and adds its own
  write to the lock's write set;
- reading a non-zero low word, `Fresh` persists (fractions only grow);
- reading a zero low word, the claimed slots contain the pool (`Good` at the
  message's timestamp, or `Bad`: `World.lock_claim'`), and the thread is
  `Holding`: validity (`Erase.valid_claim`) bounds the counter permission by
  `1` and forces `S tid = false` (the thread holds `F tid`). The read is not
  forwarded (`LkMem`: a write of the lock above its forwarding item, an own
  `swpa` write, is at or below `coh`), so the acquire read raises `vrNew`
  (and `vwNew`) to the message's timestamp, above the counter's maximal write
  under `Good`.
-/
import Kraken.Promising.SLR.SwpRuleX
import Kraken.Promising.SLR.SwpStore
import Kraken.Promising.SLR.SpinAcquire

namespace Kraken.Promising.SLR.SwpInv

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SwpTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## The swap

The view, claim and holding facts are the ISA-neutral ones of
`SLR/SpinAcquire.lean` (namespace `SpinCommon`), used at `P.sys`. -/

open SpinCommon (fenceOptCtx_getFwd fenceOptCtx_getCoh rmwAfter_getFwd rmwAfter_getCoh rmwAfter_vrNew
  writeSuccs_vrNew writeSuccs_getFwd_msg readSuccs_ne_of_writeIn readSuccs_acq_le mayWrite_claim writtenCx_writeEv'
  setWidth_32_128 one_div_pos)

/-- **The acquiring swap** (`swpa w3, w2, [x0]`, position 3 → 4). -/
theorem wp_swpa {P : Params} {A : Arch} {tid : Nat} (htid : tid < P.N) (hN0 : 0 < P.N) (hLC : P.Lk ≠ P.C) :
    CellWPN P A tid 3 := by
  intro cl c r g g₀ rF t tree hW ht hF hL hp hph hla hg₀ hex E hM hWf hnp
  have hn := lt_size_of_get? ht
  have hx3 := hF.x3_at hp (by decide)
  rw [exec_swpa t.st (hF.at hp (by decide)) hF.x0 hF.dl] at hex
  cases hex
  simp only [Phase] at hph
  obtain ⟨hfr, hfw⟩ := hph
  have hpos : 0 < (r.wr P.Lk).q := by have := one_div_pos hN0; have := hfr.2.2; grind
  obtain ⟨hm1, hp1⟩ := fenceOptCtx_memProm A (ctx₀ t tid c.mem)
  refine EvTree.eraseWPR_rmw_pendClaim hn (fun x _ h => by simp at h) ?_ ?_
  · -- a pending write: impossible away from position 13
    intro x hx new _ cx' tw _ hev hpd _ _
    exfalso
    obtain ⟨hm2, hp2⟩ := readSuccs_memProm A _ hx
    rcases hev.cases with ⟨-, htw, -⟩ | ⟨-, rfl⟩
    · rw [hp2, hp1] at htw
      exact hnp tw htw hpd
    · obtain ⟨⟨w, hw⟩, -⟩ := E.pend _ hpd
      have := Memory.last_le_of_get?_eq_some _ hw
      rw [hm2, hm1] at this
      exact Nat.not_succ_le_self _ this
  · intro x hx new hop cx' tw hc hev hpd hrd hun' _
    obtain rfl := Option.some.inj hop
    obtain ⟨hm2, hp2⟩ := readSuccs_memProm A _ hx
    have hun := hun'
    -- not forwarded: a later write of the lock is at or below `coh` (`LkMem`)
    have hrv := readSuccs_acq_le hx rfl rfl fun f hf htf => by
      rw [fenceOptCtx_getFwd] at hf
      refine absurd htf.symm (readSuccs_ne_of_writeIn hx ?_)
      rw [hm1, fenceOptCtx_getCoh]; exact (hla f hf).2 (.inr (.inl rfl))
    have hnew : BitVec.setWidth 32 (BitVec.setWidth 128 (BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec)) ≠ 0 := by
      rw [setWidth_32_128, hx3]; decide
    refine ⟨false, [], (r.op (Res.prod ((claimedSlots g P.Lk x.1).map (·.res)))).addW P.Lk
      (BitVec.setWidth 128 (BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec), tw), hpos, fun h => absurd h (by decide), fun _ => ⟨rfl, ?_⟩, by simp [Res.op_unit],
      fun _ => rfl, fun _ => ?_, ?_⟩
    · rw [hW.1]; exact lockPred_pure hnew
    · have h1 : x.2.2.views.vwNew ≤ (rmwAfter A .acq false ⟨P.l, 4⟩ cx').views.vwNew :=
        ((writeSuccs_vmono A tid hc).trans (rmwAfter_vmono A .acq false _ cx')).vwNew
      simp only [Views.wfloor]; omega_t
    · simp only [EvTree.EraseWPR]
      refine ⟨⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩, fun ts h _ => h, fun ts h => h,
        fun y h => mayWrite_claim h, fun w hw => ?_, fun t' ht' _ => ?_⟩
      · rw [writtenCx_writeEv' (hm2.trans hm1) (hp2.trans hp1) hev (rmwAfter_memProm A _ _ _ _).1
          (rmwAfter_memProm A _ _ _ _).2 hw]
        exact hpos
      · obtain ⟨hpr', hvs⟩ := finishInstr_relKey ht'
        -- the lock's forwarding item is the swap's write of `1`, at `coh`
        have hfw4 : ∀ f, t'.views.getFwd P.Lk = some f →
            (rmwAfter A .acq false ⟨P.l, 4⟩ cx').mem.get? f.time = some ⟨P.Lk, 1#128, tid⟩ ∧
              f.time ≤ t'.views.getCoh P.Lk := fun f hf => by
          have h5 : t'.views.fwdb = (rmwAfter A .acq false ⟨P.l, 4⟩ cx').views.fwdb := by
            simpa using congrArg Views.fwdb hvs
          have h2 : t'.views.coh = (rmwAfter A .acq false ⟨P.l, 4⟩ cx').views.coh := by
            simpa using congrArg Views.coh hvs
          have : (rmwAfter A .acq false ⟨P.l, 4⟩ cx').views.getFwd P.Lk = some f := by
            simpa only [Views.getFwd, h5] using hf
          rw [rmwAfter_getFwd] at this
          have hm := writeSuccs_getFwd_msg hc f this
          have hcoh : t'.views.getCoh P.Lk = (rmwAfter A .acq false ⟨P.l, 4⟩ cx').views.getCoh P.Lk := by
            simp only [Views.getCoh, h2]
          rw [(rmwAfter_memProm A _ _ _ _).1, hcoh, rmwAfter_getCoh, hm.1]
          exact ⟨by rw [hx3]; rfl, hm.2⟩
        refine inv_withThread_mem (i := 4) (hW.mono ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩) ht
          (finishInstr_st ht') (hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl) ?_ rfl ?_
          (hla := fun f hf => ⟨fun _ => ⟨_, (hfw4 f hf).1, rfl, rfl⟩, fun h => by simp at h⟩)
        · have hlast : c.mem.last ≤ (rmwAfter A .acq false ⟨P.l, 4⟩ cx').mem.last := by
            rw [(rmwAfter_memProm A _ _ _ _).1]
            have := hev.last_le; rw [hm2, hm1] at this; exact this
          have htw : tw ≤ (rmwAfter A .acq false ⟨P.l, 4⟩ cx').mem.last := by
            rw [(rmwAfter_memProm A _ _ _ _).1]
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
        · have hx2 : BitVec.setWidth 32 (t.st.st.1.regs.setXReg XReg.X2
              (BitVec.setWidth 64 (BitVec.setWidth 32 x.2.1))).X2.toBitVec = BitVec.setWidth 32 x.2.1 := by
            simp only [Reg64s.setXReg]; apply BitVec.eq_of_toNat_eq; simp
          have hvr : x.1 ≤ t'.views.vrNew := by
            have h1 : t'.views.vrNew = (rmwAfter A .acq false ⟨P.l, 4⟩ cx').views.vrNew := by
              simpa using congrArg Views.vrNew hvs
            rw [h1]
            exact Nat.le_trans hrv.1 (Nat.le_trans (Nat.le_of_eq (writeSuccs_vrNew hc).symm) (rmwAfter_vrNew _ _ _ _))
          simp only [Phase, hx2]
          split
          · rename_i hz
            have hrd' : c.mem.read? P.Lk x.1 = some x.2.1 := by rw [hm2, hm1] at hrd; exact hrd
            obtain ⟨R, R', hprod, hgb⟩ := SpinCommon.World.lock_claim' (P := P.sys) hW E hrd' hz hun
            have hval := E.valid_claim hn P.Lk x.1
            rw [hprod] at hval ⊢
            have hlk : 1 / (P.N : Rat) ≤ (((r.op (R.op R')).addW P.Lk
                (BitVec.setWidth 128 (BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec), tw)).wr P.Lk).q := by
              rw [Res.addW_q]; exact Rat.le_trans hfr.2.2 (Perm.le_op_left _ _)
            rcases hgb with ⟨k, S, ts, hpool, hX, hmax, hk, hts⟩ | ⟨hRL, S, hpool⟩
            · exact ⟨S, k, SpinCommon.holding_of_pool (P := P.sys) htid hN0 hfr hval hpool, fun _ =>
                ⟨hlk, .inl ⟨ts, SpinCommon.counterGood_of_good (P := P.sys) hLC hval hpool.1 hX hmax hk, Nat.le_trans hts hvr⟩⟩⟩
            · refine ⟨S, 0, SpinCommon.holding_of_pool (P := P.sys) htid hN0 hfr hval hpool, fun _ => ⟨hlk, .inr ?_⟩⟩
              rw [Res.addW_q]
              change _ < (r.wr P.Lk).q + ((R.wr P.Lk).q + (R'.wr P.Lk).q)
              have := hfr.2.2; have := (R'.wr P.Lk).nonneg; grind
          · have hge : ∀ y, (r.wr y).q ≤ (((r.op (Res.prod ((claimedSlots g P.Lk x.1).map (·.res)))).addW P.Lk
                (BitVec.setWidth 128 (BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec), tw)).wr y).q :=
              fun y => by rw [Res.addW_q]; exact Perm.le_op_left _ _
            refine ⟨⟨Rat.le_trans hfr.1 (hge _), Rat.le_trans hfr.2.1 (hge _), Rat.le_trans hfr.2.2 (hge _)⟩, ?_⟩
            exact fun f hf => (hfw4 f hf).2

end Kraken.Promising.SLR.SwpInv
