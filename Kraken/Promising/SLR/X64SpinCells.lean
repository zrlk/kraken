/-
The cell rules of the x64 spinlock worker for `ThreadRuleR.wp`: for each
position, from the invariant's facts at that position
(`SLR/X64SpinInv.lean`), the erasure WP with bounded reach of the cell's
event tree (`SLR/X64SpinTrees.lean`) with postcondition `WpPostR (Inv P tid)`
at the continuation flag. The x64 twin of `SLR/SwpCells.lean`.

This file: the plumbing (`Frame` across a step, `Inv` after a step,
`Phase.congr_views`, `Phase.pos`) and the cells that touch no resource: the
lock load (1), the tests (2, 6), the branches (3, 7), `movl $1` (4), the
increment (9) and `jmp done` (12). The resource cells (the swap, 5; the
counter load, 8, and store, 10; the unlock, 11) and the prepay are the fields
of `X64SpinRule.HardCells`.
-/
import Kraken.Promising.SLR.X64SpinInv
import Kraken.Promising.SLR.RuleShapes
import Kraken.Promising.SLR.SpinAcquire

namespace Kraken.Promising.SLR.X64SpinInv

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

omit layout hv in
/-- Writing a low part of `%rax` or `%rcx` keeps `%rdi` and `%rsi`. -/
@[simp] theorem get64_set_low_rax_rdi (s : Reg64s) (v : BitVec 32) :
    (s.set (.low .rax .W32) v).get64 .rdi = s.get64 .rdi := by
  simp [Reg64s.set, Reg64s.set64, Reg64s.get64]

omit layout hv in
@[simp] theorem get64_set_low_rax_rsi (s : Reg64s) (v : BitVec 32) :
    (s.set (.low .rax .W32) v).get64 .rsi = s.get64 .rsi := by
  simp [Reg64s.set, Reg64s.set64, Reg64s.get64]

omit layout hv in
@[simp] theorem get64_set_low_rcx_rdi (s : Reg64s) (v : BitVec 32) :
    (s.set (.low .rcx .W32) v).get64 .rdi = s.get64 .rdi := by
  simp [Reg64s.set, Reg64s.set64, Reg64s.get64]

omit layout hv in
@[simp] theorem get64_set_low_rcx_rsi (s : Reg64s) (v : BitVec 32) :
    (s.set (.low .rcx .W32) v).get64 .rsi = s.get64 .rsi := by
  simp [Reg64s.set, Reg64s.set64, Reg64s.get64]

omit hv in
/-- `Frame` across a step that keeps `%rdi`, `%rsi` and the private memory. -/
theorem Frame.goto {P : Params} {st : State} (h : Frame P st) {m : MachineData} {pc : Int64}
    (h0 : m.regs.get64 .rdi = st.st.1.regs.get64 .rdi) (h1 : m.regs.get64 .rsi = st.st.1.regs.get64 .rsi)
    (hd : m.dmem = st.st.1.dmem) :
    Frame P (goto st m pc) :=
  ⟨h.exe, h.decls, h.endPc, by simp [h0, h.rdi], by simp [h1, h.rsi], by simp [hd, h.dl],
    by simp [hd, h.dc]⟩

/-- The step context of a cell: `At` from `Frame` and the position
(positions below `13` are not the end: position `13` is the label `done`, at
the end address). -/
theorem Frame.at {P : Params} {st : State} (h : Frame P st) {i : Nat} (hp : AtPos st i) (hi : i < 13) :
    At st i := by
  refine ⟨h.exe, h.decls, hp, ?_⟩
  rw [hp, h.endPc, addrOf_label (i := 13) (l := "done") rfl]
  simp only [beq_eq_false_iff_ne, ne_eq]
  exact Executable.addrOf_ne_of_valid (layout spinWorker) (k := i) (n := 13) hi
    (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [spinWorker]) (by
      intro l z
      rw [Layout.apply_snd, Layout.frag_getElem?]
      simp [spinWorker])

omit hv in
/-- **`Inv` after a step of thread `tid`** that leaves the memory alone. -/
theorem inv_withThread {P : Params} {tid : Nat} {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    {t t' : Thread isa} (hW : World P.sys g) (ht : c.threads[tid]? = some t) {s : State} (hst : t'.st = s)
    (hF : Frame P s) (hL : LockWritesIn P.sys r c.mem) {i : Nat} (hp : AtPos s i)
    (hph : Phase P tid cl i (eaxOf s) (ecxOf s) s.st.1.status.zf t'.views r)
    (hpp : PrepaidProm P tid cl i t' c.mem r := by
      exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩) :
    Inv P tid cl (c.withThread tid t' c.mem) r g := by
  have hn := lt_size_of_get? ht
  refine ⟨hW, t', by rw [Config.withThread_get? c t' c.mem hn, ite_eq_left rfl], hst ▸ hF, ?_, i, hst ▸ hp,
    hst ▸ hph, by simpa [Config.withThread] using hpp⟩
  simpa [Config.withThread] using hL

omit layout hv in
/-- `Phase` reads the views only through `vrNew`, `coh`, `vwOld` and the
forwarding items, which an instruction that changes only `vCAP` keeps. -/
theorem Phase.congr_views {P : Params} {tid : Nat} {cl : Prop} {i : Nat} {eax ecx : BitVec 32} {zf : Bool}
    {r : Res} {vs vs' : Views} (h : ({ vs' with vCAP := 0 } : Views) = { vs with vCAP := 0 }) :
    Phase P tid cl i eax ecx zf vs' r = Phase P tid cl i eax ecx zf vs r := by
  have h1 : vs'.vrNew = vs.vrNew := by simpa using congrArg Views.vrNew h
  have h2 : vs'.coh = vs.coh := by simpa using congrArg Views.coh h
  have h3 : vs'.vwOld = vs.vwOld := by simpa using congrArg Views.vwOld h
  have h4 : vs'.getCoh P.C = vs.getCoh P.C := by simp [Views.getCoh, h2]
  have h5 : vs'.fwdb = vs.fwdb := by simpa using congrArg Views.fwdb h
  have h6 : LkFwd P vs' = LkFwd P vs := by simp only [LkFwd, Views.getFwd, h5]
  unfold Phase
  rw [h1, h3, h4, h6]

omit layout hv in
/-- The positions of `Phase`. -/
theorem Phase.pos {P : Params} {tid : Nat} {cl : Prop} {i : Nat} {eax ecx : BitVec 32} {zf : Bool}
    {vs : Views} {r : Res} (h : Phase P tid cl i eax ecx zf vs r) :
    i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
      i = 12 ∨ i = 14 := by
  revert h
  unfold Phase
  split <;> intro h <;> first | omega | exact h.elim

/-! ## Stable cells -/

section Cells

variable {P : Params} {tid : Nat} {cl cl' : Prop} {c : Config isa} {r : Res} {g : Ghost} {t : Thread isa}
  {A : Arch} {iv : InstrViews} {rF : Nat → Res} {tree : EvTree State}

omit layout hv in
/-- `Held` survives a weaker clean flag and an unchanged read view. -/
theorem Held.weaken {vr : View} (hcl : cl' → cl) (h : Held P tid cl vr r) : Held P tid cl' vr r := by
  obtain ⟨S, k, hh, hm⟩ := h
  exact ⟨S, k, hh, fun h => hm (hcl h)⟩

/-- `movl (%rdi),%eax` (position 1 → 2, `Fresh`): a load, nothing changes but
`%eax` and the views. -/
theorem wp_load_lock (hW : World P.sys g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st)
    (hL : LockWritesIn P.sys r c.mem)
    (hp : AtPos t.st 1)
    (hph : Phase P tid cl 1 (eaxOf t.st) (ecxOf t.st) t.st.st.1.status.zf t.views r)
    (hex : isa.exec t.st = some tree) :
    tree.EraseWPR A tid iv rF (fun _ => True) c t (WpPostR (Inv P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  rw [exec_load_lock t.st (hF.at hp (by decide)) hF.rdi hF.dl] at hex
  cases hex
  refine EvTree.eraseWPR_load fun x hx => ?_
  obtain ⟨hm, hpr⟩ := readSuccs_memProm A iv hx
  refine WpPostR.noWrite hm hpr fun t' hst _ hv => ?_
  refine inv_withThread (hW := hW) (i := 2) ht hst (hF.goto (by simp) (by simp) rfl) hL rfl ?_
  simp only [Phase] at hph ⊢
  refine ⟨hph.1, fun f hf => hph.2 f ?_⟩
  have h5 : t'.views.fwdb = x.2.2.views.fwdb := by simpa using congrArg Views.fwdb hv
  simpa only [Views.getFwd, h5, readSuccs_fwdb A iv hx] using hf

/-- `testl %eax,%eax` (position 2 → 3, `Fresh`), both values of `AF`. -/
theorem wp_test (hW : World P.sys g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st)
    (hL : LockWritesIn P.sys r c.mem)
    (hp : AtPos t.st 2)
    (hph : Phase P tid cl 2 (eaxOf t.st) (ecxOf t.st) t.st.st.1.status.zf t.views r)
    (hex : isa.exec t.st = some tree) :
    tree.EraseWPR A tid iv rF (fun _ => True) c t (WpPostR (Inv P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  rw [exec_test t.st (hF.at hp (by decide))] at hex
  cases hex
  intro i
  refine WpPostR.silent fun t' hst _ hv => ?_
  rw [← Phase.congr_views hv] at hph
  refine inv_withThread (hW := hW) (i := 3) ht hst (hF.goto rfl rfl rfl) hL rfl ?_
  simp only [Phase] at hph ⊢
  exact hph

/-- `jne worker` (position 3 → 4 or 1, `Fresh`). -/
theorem wp_jne_spin (hW : World P.sys g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st)
    (hL : LockWritesIn P.sys r c.mem)
    (hp : AtPos t.st 3)
    (hph : Phase P tid cl 3 (eaxOf t.st) (ecxOf t.st) t.st.st.1.status.zf t.views r)
    (hex : isa.exec t.st = some tree) :
    tree.EraseWPR A tid iv rF (fun _ => True) c t (WpPostR (Inv P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  rw [exec_jne_spin t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ hv => ?_
  rw [← Phase.congr_views hv] at hph
  have hF' := hF.goto (m := t.st.st.1) (pc := if t.st.st.1.status.zf then (layout spinWorker).addrOf 4
    else (layout spinWorker).addrOf 1) rfl rfl rfl
  simp only [Phase] at hph
  by_cases hz : t.st.st.1.status.zf
  · refine inv_withThread (hW := hW) (i := 4) ht hst hF' hL (by simp [AtPos, hz]) ?_
    simp only [Phase]
    exact hph
  · refine inv_withThread (hW := hW) (i := 1) ht hst hF' hL (by simp [AtPos, hz]) ?_
    simp only [Phase]
    exact hph

/-- `movl $1,%eax` (position 4 → 5, `Fresh`). -/
theorem wp_mov_one (hW : World P.sys g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st)
    (hL : LockWritesIn P.sys r c.mem)
    (hp : AtPos t.st 4)
    (hph : Phase P tid cl 4 (eaxOf t.st) (ecxOf t.st) t.st.st.1.status.zf t.views r)
    (hex : isa.exec t.st = some tree) :
    tree.EraseWPR A tid iv rF (fun _ => True) c t (WpPostR (Inv P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  rw [exec_mov_one t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ hv => ?_
  rw [← Phase.congr_views hv] at hph
  refine inv_withThread (hW := hW) (i := 5) ht hst (hF.goto (by simp) (by simp) rfl) hL rfl ?_
  simp only [Phase] at hph ⊢
  refine ⟨hph.1, hph.2, ?_⟩
  simp only [eaxOf]
  simp only [Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.take, BitVec.drop]

/-- `testl %eax,%eax` (position 6 → 7): `ZF` records whether the swap read
`0`, so the phase at 7 (`Held` if `ZF`, else `Fresh`) is the phase at 6. -/
theorem wp_test2 (hcl : cl' → cl) (hW : World P.sys g) (ht : c.threads[tid]? = some t)
    (hF : Frame P t.st) (hL : LockWritesIn P.sys r c.mem) (hp : AtPos t.st 6)
    (hph : Phase P tid cl 6 (eaxOf t.st) (ecxOf t.st) t.st.st.1.status.zf t.views r)
    (hex : isa.exec t.st = some tree) :
    tree.EraseWPR A tid iv rF (fun _ => True) c t (WpPostR (Inv P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  rw [exec_test2 t.st (hF.at hp (by decide))] at hex
  cases hex
  intro i
  refine WpPostR.silent fun t' hst _ hv => ?_
  rw [← Phase.congr_views hv] at hph
  refine inv_withThread (hW := hW) (i := 7) ht hst (hF.goto rfl rfl rfl) hL rfl ?_
  simp only [Phase, zf_from_result] at hph ⊢
  by_cases hz : eaxOf t.st = 0
  · simp only [hz, ↓reduceIte] at hph
    have : (t.st.st.1.regs.get (.low .rax .W32) == 0#32) = true := by simpa using hz
    simp only [this, ↓reduceIte]
    exact hph.weaken hcl
  · simp only [hz, ↓reduceIte] at hph
    have : (t.st.st.1.regs.get (.low .rax .W32) == 0#32) = false := by simpa using hz
    simp only [this]
    exact hph

/-- `jne worker` (position 7 → 8 holding with `ZF`, → 1 `Fresh`). -/
theorem wp_jne_retry (hcl : cl' → cl) (hW : World P.sys g) (ht : c.threads[tid]? = some t)
    (hF : Frame P t.st) (hL : LockWritesIn P.sys r c.mem) (hp : AtPos t.st 7)
    (hph : Phase P tid cl 7 (eaxOf t.st) (ecxOf t.st) t.st.st.1.status.zf t.views r)
    (hex : isa.exec t.st = some tree) :
    tree.EraseWPR A tid iv rF (fun _ => True) c t (WpPostR (Inv P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  rw [exec_jne_retry t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ hv => ?_
  rw [← Phase.congr_views hv] at hph
  have hF' := hF.goto (m := t.st.st.1) (pc := if t.st.st.1.status.zf then (layout spinWorker).addrOf 8
    else (layout spinWorker).addrOf 1) rfl rfl rfl
  simp only [Phase] at hph
  by_cases hz : t.st.st.1.status.zf
  · refine inv_withThread (hW := hW) (i := 8) ht hst hF' hL (by simp [AtPos, hz]) ?_
    simp only [Phase]
    simp only [hz, ↓reduceIte] at hph
    exact hph.weaken hcl
  · refine inv_withThread (hW := hW) (i := 1) ht hst hF' hL (by simp [AtPos, hz]) ?_
    simp only [Phase]
    simp only [hz] at hph
    exact hph

/-- `jmp done` (position 12 → 14). -/
theorem wp_jmp_done (hcl : cl' → cl) (hW : World P.sys g) (ht : c.threads[tid]? = some t)
    (hF : Frame P t.st) (hL : LockWritesIn P.sys r c.mem) (hp : AtPos t.st 12)
    (hph : Phase P tid cl 12 (eaxOf t.st) (ecxOf t.st) t.st.st.1.status.zf t.views r)
    (hex : isa.exec t.st = some tree) :
    tree.EraseWPR A tid iv rF (fun _ => True) c t (WpPostR (Inv P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  rw [exec_jmp_done t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ _ => ?_
  refine inv_withThread (hW := hW) (i := 14) ht hst (hF.goto rfl rfl rfl) hL rfl ?_
  simp only [Phase] at hph ⊢
  exact ⟨hph.1, fun h => hph.2 (hcl h)⟩

omit layout hv in
/-- Reading back the low word of `%rax` after writing it. -/
@[simp] theorem get_set_low_rax (s : Reg64s) (v : BitVec 32) :
    (s.set (.low .rax .W32) v).get (.low .rax .W32) = v := by
  simp only [Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset]
  apply BitVec.eq_of_toNat_eq
  simpa [BitVec.take, BitVec.drop] using v.isLt

omit layout hv in
/-- Reading back the low word of `%rcx` after writing it. -/
@[simp] theorem get_set_low_rcx (s : Reg64s) (v : BitVec 32) :
    (s.set (.low .rcx .W32) v).get (.low .rcx .W32) = v := by
  simp only [Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset]
  apply BitVec.eq_of_toNat_eq
  simpa [BitVec.take, BitVec.drop] using v.isLt

/-- `addl $1,%ecx` (position 9 → 10): `%ecx` becomes `k + 1`. -/
theorem wp_add (hcl : cl' → cl) (hW : World P.sys g) (ht : c.threads[tid]? = some t)
    (hF : Frame P t.st) (hL : LockWritesIn P.sys r c.mem) (hp : AtPos t.st 9)
    (hph : Phase P tid cl 9 (eaxOf t.st) (ecxOf t.st) t.st.st.1.status.zf t.views r)
    (hex : isa.exec t.st = some tree) :
    tree.EraseWPR A tid iv rF (fun _ => True) c t (WpPostR (Inv P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  rw [exec_add t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ hv => ?_
  rw [← Phase.congr_views hv] at hph
  simp only [Phase] at hph
  -- clean and without surplus, the counter's writes are below `coh C`
  have hpp : PrepaidProm P tid cl' 10 t' c.mem r := ⟨fun _ h hq p hp hlt => by
    exfalso
    obtain ⟨S, k, -, hm⟩ := hph
    obtain ⟨-, ⟨ts, ⟨⟨-, hmax⟩, -⟩, hc, -⟩ | hsur⟩ := hm (hcl h)
    · exact absurd (Nat.le_trans (hmax p hp) hc) (Nat.not_le.mpr hlt)
    · exact absurd hsur (Rat.not_lt.mpr hq), fun h => absurd h (by decide)⟩
  refine inv_withThread (hW := hW) (i := 10) ht hst (hF.goto (by simp) (by simp) rfl) hL rfl ?_ hpp
  simp only [Phase]
  obtain ⟨S, k, hh, hm⟩ := hph
  refine ⟨S, k, hh, fun h => ?_⟩
  obtain ⟨hq, hm⟩ := hm (hcl h)
  refine ⟨hq, hm.imp (fun ⟨ts, hg, hc, hx⟩ => ⟨ts, hg, hc, ?_⟩) .inl⟩
  simp only [ecxOf, get_set_low_rcx] at hx ⊢
  rw [hx]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.add_mod, Nat.add_comm]

end Cells

end Kraken.Promising.SLR.X64SpinInv
