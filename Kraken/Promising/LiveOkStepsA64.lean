/-
**AArch64: every AArch64 instruction tree is total.**

`ISA.ExecTotal` instances for `AArch64.isa` and `isaLSE2`: every tree the
adapter `toEv` builds has an outcome from every bounded, promise-free context
(`EvTree.Total`, `LiveOkSteps.lean`). Every node is covered by the generic
closure lemmas except `CASP` (`caspTree`), whose dead branches are
`choose 0`: there the run is built by hand (`caspTree_total`). Reading the
last writes `o₁`, `o₂` of the two halves, the failure branch (`succ = 0`, no
writes) is live unless both halves match, in which case the success branch
is: its first half writes to the first location, which is not the second
(`Decls.resolve_ok_addr`, `MemWidth.add_bytesv_ne`), so the second half
still reads `o₂` and the guard holds.

With these instances `Live.NoStuck.stuckHasDeadPromise_of_faultFreeSem`
applies to every AArch64 program with a semantic fault-freedom theorem
(`LiveOkStepsA64Locks.lean` for the published ones).
-/
import Kraken.Promising.AArch64
import Kraken.Promising.LiveOkSteps

namespace Kraken.Promising.AArch64

open Kraken Kraken.Promising

variable {A : Arch} {tid : Nat} {iv : InstrViews}

/-- The two halves of a pair start at different addresses (a local copy of
`Kraken.AArch64.EnvWP`'s `MemWidth.add_bytesv_ne`, which lives behind the WP
library). -/
private theorem add_bytesv_ne (addr : BitVec 64) (w : MemWidth) : addr + w.bytesv ≠ addr := by
  cases w <;> simp [MemWidth.bytesv] <;> bv_omega

/-- The locations of the two halves of a pair differ. -/
private theorem halves_ne {ds : Decls} {addr : BitVec 64} {w : MemWidth} {l1 l2 : Loc}
    (h1 : ds.resolve addr w.bytes = .ok l1) (h2 : ds.resolve (addr + w.bytesv) w.bytes = .ok l2) : l1 ≠ l2 := by
  intro e
  have e1 := Decls.resolve_ok_addr h1
  have e2 := Decls.resolve_ok_addr h2
  rw [e] at e1
  exact add_bytesv_ne addr w (e2.symm.trans e1)

/-- **`CASP` is total**: see the module docstring. -/
theorem caspTree_total {σ : Type} {ds : Decls} {k : RmwKind} {addr : BitVec 64} {w : MemWidth}
    {cmp1 cmp2 new1 new2 : w.type} {ret : w.type → w.type → EvTree σ} (h : ∀ o1 o2, (ret o1 o2).Total A tid iv) :
    (caspTree ds k addr cmp1 cmp2 new1 new2 ret).Total A tid iv := by
  intro c hc hp hiv
  rcases h1 : ds.resolve addr w.bytes with m1 | l1
  · -- the first half faults
    simp only [caspTree, EvTree.access, h1]
    refine EvTree.exists_run_choose 0 (EvTree.exists_run_choose 0 ?_)
    simp only [Fin.isValue, Fin.val_zero, beq_self_eq_true, ite_true]
    exact ⟨_, List.mem_singleton.mpr rfl⟩
  rcases h2 : ds.resolve (addr + w.bytesv) w.bytes with m2 | l2
  · -- the second half faults: `succ = 0`, no write
    simp only [caspTree, EvTree.access, h1, h2]
    refine EvTree.exists_run_choose 0 (EvTree.exists_run_choose 0 ?_)
    simp only [Fin.isValue, Fin.val_zero, beq_self_eq_true, ite_true, Nat.reduceBEq, Bool.false_eq_true, ite_false]
    refine EvTree.exists_run_rmw hc hp hiv fun c' _ _ _ _ => ?_
    exact ⟨_, List.mem_singleton.mpr rfl⟩
  have hne := halves_ne h1 h2
  simp only [caspTree, EvTree.access, h1, h2]
  by_cases hm : ((c.mem.finalVal l1).setWidth w.bits == cmp1 && (c.mem.finalVal l2).setWidth w.bits == cmp2) = true
  · -- both halves match: `succ = 1`
    refine EvTree.exists_run_choose 1 (EvTree.exists_run_choose 0 ?_)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, beq_self_eq_true, ite_true]
    obtain ⟨hm1, hm2⟩ := Bool.and_eq_true_iff.mp hm
    refine EvTree.exists_run_rmw hc hp hiv fun c' hb' hp' hiv' hmem' => ?_
    simp only [hm1, ite_true, Option.map_some] at hmem'
    have hfv : c'.mem.finalVal l2 = c.mem.finalVal l2 := by
      rw [hmem', Live.TicketStep.finalVal_append]; exact ite_eq_right hne
    refine EvTree.exists_run_rmw hb' hp' hiv' fun c'' hb'' hp'' hiv'' _ => ?_
    rw [hfv, hm, Bool.true_beq]
    exact h _ _ c'' hb'' hp'' hiv''
  · -- some half mismatches: `succ = 0`, no write
    refine EvTree.exists_run_choose 0 (EvTree.exists_run_choose 0 ?_)
    simp only [Fin.isValue, Fin.val_zero, beq_self_eq_true, ite_true, Nat.reduceBEq, Bool.false_eq_true, ite_false]
    refine EvTree.exists_run_rmw hc hp hiv fun c' hb' hp' hiv' hmem' => ?_
    simp only [Option.map_none] at hmem'
    refine EvTree.exists_run_rmw hb' hp' hiv' fun c'' hb'' hp'' hiv'' _ => ?_
    rw [hmem', Bool.eq_false_iff.mpr hm]
    exact h _ _ c'' hb'' hp'' hiv''

/-- **Every AArch64 event tree is total.** -/
theorem toEv_total (ds : Decls) (e : Effects) : (toEv ds e).Total A tid iv := by
  induction e with
  | done a => exact .done _
  | unimplemented msg => exact .fault _
  | unaligned_sp sp => exact .fault _
  | nonmem_load dmem addr w ret ih => exact .access fun _ => .load fun _ => ih _ _
  | nonmem_store dmem addr v ret ih => exact .access fun _ => .store fun _ => ih _
  | sync_load k xcl dmem addr w ret ih => exact .access fun _ => .load fun _ => ih _ _
  | sync_store k xcl dmem addr v ret ih => exact .access fun _ => .store fun _ => ih _ _
  | rmw k noRet dmem addr w op ret ih => exact .access fun _ => .rmw fun _ => ih _ _
  | sync_load_pair k xcl dmem addr w ret ih =>
    simp only [toEv]
    split
    · exact .access fun _ => .load fun _ => ih _ _ _
    · exact .access fun _ => .load fun _ => .access fun _ => .load fun _ => ih _ _ _
  | sync_store_pair k xcl dmem addr v1 v2 ret ih =>
    simp only [toEv]
    split
    · exact .access fun _ => .store fun _ => ih _ _
    · refine .access fun _ => .store fun ok => ?_
      cases ok
      · exact ih _ _
      · exact .access fun _ => .store fun _ => ih _ _
  | rmw_pair k dmem addr cmp1 cmp2 new1 new2 ret ih => exact caspTree_total fun _ _ => ih _ _ _
  | fence k ok ih => exact .fence (ih ())
  | @undefined α inst ret ih =>
    cases inst with
    | bool => exact .choose (by decide) fun _ => ih _
    | bitvec w => exact .fault _
    | statusFlags => exact .fault _
  | require_read_access addr w ok ih => exact ih ()
  | require_write_access addr w ok ih => exact ih ()
  | require_exec_access p ok ih => exact ih ()

/-- **`toEvCASP`'s trees are total.** -/
theorem toEvCASP_total (ds : Decls) (e : Effects) : (toEvCASP ds e).Total A tid iv := by
  induction e
  case require_read_access _ _ _ ih => exact ih ()
  case require_write_access _ _ _ ih => exact ih ()
  case require_exec_access _ _ ih => exact ih ()
  case rmw_pair k dmem addr w cmp1 cmp2 new1 new2 ret _ =>
    cases w
    case W64 =>
      simp only [toEvCASP]
      split
      · exact .access fun _ => .rmw fun _ => toEv_total _ _
      · exact toEv_total _ _
    all_goals exact toEv_total _ _
  all_goals exact toEv_total _ _

/-- **Every instruction tree of `AArch64.isa` is total.** -/
instance : isa.ExecTotal where
  total A tid iv s tree h := by
    simp only [isa, exec] at h
    split at h
    · cases h
    · cases h; exact .map _ (toEv_total _ _)

/-- **Every instruction tree of `isaLSE2` is total.** -/
instance : isaLSE2.ExecTotal where
  total A tid iv s tree h := by
    simp only [isaLSE2, execLSE2] at h
    split at h
    · cases h
    · split at h
      · cases h; exact .map _ (toEv_total _ _)
      · split at h
        · cases h; exact .map _ (toEvCASP_total _ _)
        · simp only [exec] at h
          split at h
          · cases h
          · cases h; exact .map _ (toEv_total _ _)

end Kraken.Promising.AArch64
