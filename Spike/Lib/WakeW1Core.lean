/-
**The two-thread core after a step of the worker**. ISA-generic.

- `Inv2Core.core1_same`: a step of thread 1 that leaves both memories,
  the promise sets and the memory relation's bookkeeping alone (a silent
  step, a fence, a runtime load, a kernel return) keeps the core, given
  thread 1's own facts at the new state.
- `Inv2Core.core1_append`: a step of thread 1 appending its message in its
  footprint keeps the core: thread 0's facts by the rely
  (`Spike.Lib.Inv2Rely`), `T_le`, `S_le` and `bnd0` by the memories'
  growth (the source one kept or one message pushed), the
  memory-only facts from the new message's; the memory relation, promise
  bookkeeping, source side and thread 1's own facts are hypotheses (the
  row's).
-/
import Spike.Lib.Inv2Rely

namespace Spike.Lib.Inv2Core

open Kraken.Promising Scc.Sem

variable {I : ISA} {Λ : Scc.Sem.Layout} {R : SpawnRec} {P : Inv2Params I} {G : Loc → Val → Prop}
  {own : Nat → List (Loc × Val)} {tm : Memory} {t0 t1 : Thread I} {sm : WeakMem.Memory}
  {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}

/-- **A step of thread 1 with both memories unchanged** keeps the core:
thread 1's promises (target and source) are unchanged, and its bound,
cover, source cover, owned words and no-promise fact hold at the new
state; thread 0's owned words are unchanged. -/
theorem core1_same (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {t1' : Thread I}
    {s1' : TermRun.TTh} {own' : Nat → List (Loc × Val)} (ho0 : own' 0 = own 0)
    (hp : t1'.prom = t1.prom) (hsp : s1'.promises = s1.promises) (hb : t1'.Bnd tm.last)
    (hc : CohCoversL t1'.views t1'.prom tm (P.cov 1))
    (hsc : ∀ k m, sm[k]? = some m → P.frzS m.loc → k ≤ s1'.vs.coh m.loc)
    (hown : ExtRows.OwnOk (own' 1) tm t1'.prom) (hdisj : ∀ L v v', (L, v) ∈ own 0 → (L, v') ∈ own' 1 → False)
    (hocov : ∀ L v, (L, v) ∈ own' 1 → P.cov 1 L) (hnp : P.noProm t1'.st → t1'.prom = []) :
    Inv2Core Λ R P G own' tm t0 t1' sm s0 s1' ts tp sp :=
  { h with
    tp_prom := fun k hk => by rw [hp]; exact h.tp_prom k hk
    prom_tp := fun k w hk => by rw [hp] at hk; exact h.prom_tp k w hk
    sp_prom := fun k => by rw [hsp]; exact h.sp_prom k
    bnd1 := hb
    cov1 := hc
    scov1 := hsc
    own0 := by rw [ho0]; exact h.own0
    own1 := hown
    own_disj := by rw [ho0]; exact hdisj
    own_cov := fun i L v hi hm => by
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [ho0] at hm; exact h.own_cov 0 L v hi hm
      · exact hocov L v hm
    prom1 := by rw [hp]; exact h.prom1
    noProm1 := hnp }

/-- **A step of thread 1 appending its message `w`** (a store, a runtime
write or a promise), in its footprint, to the target memory: thread 0's
facts come from the rely (`Spike.Lib.Inv2Rely`), the memory-only facts
from the new message's; the memory relation, the promise bookkeeping, the
source side (`sm'`, `s1'`) and thread 1's own facts are the row's. -/
theorem core1_append (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {w : Msg} {t1' : Thread I}
    {sm' : WeakMem.Memory} {s1' : TermRun.TTh} {ts' : Nat → Option Nat} {tp' sp' : List Nat}
    {own' : Nat → List (Loc × Val)} (ho0 : own' 0 = own 0) (hwt : w.tid = 1) (hf : P.foot 1 w.loc)
    (hsm : sm' = sm ∨ ∃ m, sm' = sm.push m)
    (hmem : MemRelP Λ R.lbl R.lsize ts' (tm.append w).1 sm' tp' [] sp')
    (htp : ∀ k ∈ tp', k ∈ t0.prom ∨ k ∈ t1'.prom)
    (hpt : ∀ k w', (k ∈ t0.prom ∨ k ∈ t1'.prom) → (tm.append w).1.get? k = some w' →
      InLabel R.lbl R.lsize w'.loc → k ∈ tp')
    (hsp : ∀ k, k ∈ sp' ↔ k ∈ s0.promises ∨ k ∈ s1'.promises)
    (hb8 : w.loc.bytes = 8) (hin : Consumer1.LocIn Λ.shared w.loc) (hfit : w.val.toNat < 2 ^ 64)
    (hG : G w.loc w.val)
    (hb : t1'.Bnd (tm.append w).1.last) (hc : CohCoversL t1'.views t1'.prom (tm.append w).1 (P.cov 1))
    (hfS : ∀ k m, sm'[k]? = some m → R.S ≤ k → ¬ P.frzS m.loc)
    (hsc0 : ∀ k m, sm'[k]? = some m → P.frzS m.loc → k ≤ s0.vs.coh m.loc)
    (hsc1 : ∀ k m, sm'[k]? = some m → P.frzS m.loc → k ≤ s1'.vs.coh m.loc)
    (hown : ExtRows.OwnOk (own' 1) (tm.append w).1 t1'.prom)
    (hdisj : ∀ L v v', (L, v) ∈ own 0 → (L, v') ∈ own' 1 → False)
    (hocov : ∀ L v, (L, v) ∈ own' 1 → P.cov 1 L)
    (hpr : ∀ k ∈ t1'.prom, R.T < k ∧ ∃ w', (tm.append w).1.get? k = some w' ∧ w'.tid = 1)
    (hnp : P.noProm t1'.st → t1'.prom = []) :
    Inv2Core Λ R P G own' (tm.append w).1 t0 t1' sm' s0 s1' ts' tp' sp' := by
  have hlast : (tm.append w).1.last = tm.last + 1 := Kraken.Promising.Memory.last_append tm w
  have hf' : P.foot w.tid w.loc := hwt ▸ hf
  exact
  { mem := hmem
    tp_prom := htp
    prom_tp := hpt
    sp_prom := hsp
    narrow := Inv1.narrow_append h.narrow hb8
    memIn := Consumer1.memIn_append hin h.memIn
    fits := ⟨fits_append h.fits.1 hfit, initFits_append h.fits.2 w⟩
    memInv := h.memInv.append hG
    bnd0 := h.bnd0.mono (by rw [hlast]; exact Nat.le_succ _)
    bnd1 := hb
    cov0 := Inv2Rely.Inv2Core.cov_append h h.cov0 (by decide) (by decide) (by decide) hf
    cov1 := hc
    frz_cov := h.frz_cov
    frzT := Inv2Rely.Inv2Core.frzT_append h (by omega) hf'
    frzS := hfS
    scov0 := hsc0
    scov1 := hsc1
    pre_tid := Inv2Rely.Inv2Core.pre_tid_append h h.T_le w
    post_foot := Inv2Rely.Inv2Core.post_foot_append h (.inr hwt) hf'
    foot_cov := h.foot_cov
    own0 := by
      rw [ho0]
      exact Inv2Rely.Inv2Core.own_append h h.own0 (by decide) (by decide) (by decide) hf
    own1 := hown
    own_disj := by rw [ho0]; exact hdisj
    own_cov := fun i L v hi hm => by
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [ho0] at hm; exact h.own_cov 0 L v hi hm
      · exact hocov L v hm
    prom0 := Inv2Rely.Inv2Core.prom_append h.prom0 w
    prom1 := hpr
    noProm0 := h.noProm0
    noProm1 := hnp
    T_le := by rw [hlast]; exact Nat.le_succ_of_le h.T_le
    S_le := by
      rcases hsm with rfl | ⟨m, rfl⟩
      · exact h.S_le
      · rw [Array.size_push]; exact Nat.le_succ_of_le h.S_le }

/-- info: 'Spike.Lib.Inv2Core.core1_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms core1_same

/-- info: 'Spike.Lib.Inv2Core.core1_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms core1_append

end Spike.Lib.Inv2Core
