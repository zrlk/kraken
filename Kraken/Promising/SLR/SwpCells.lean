/-
The cell rules of the SWP spinlock worker for `ThreadRuleR.wp`: for each
position, from the invariant's facts at that position (`SLR/SwpInv.lean`),
the erasure WP with bounded reach of the cell's event tree
(`SLR/SwpTrees.lean`) with postcondition `WpPostR (Inv P tid)` at the
continuation flag.

This file: the plumbing (`Frame` across a step, `Inv` after a step) and the
silent cells (`mov`, `cbz`, `cbnz`, `b try`, `add`, `b done`).
-/
import Kraken.Promising.SLR.SwpInv
import Kraken.Promising.SLR.RuleShapes
import Kraken.Promising.SLR.SpinAcquire

namespace Kraken.Promising.SLR.SwpInv

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SwpTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

omit hv in
/-- `Frame` across a step that keeps `X0`, `X1` and the private memory, with
`W3 = 1` afterwards (by default from a hypothesis `W3 = 1` in context,
through `setXReg` of other registers: `Frame.x3_at`). -/
theorem Frame.goto {P : Params} {st : State} (h : Frame P st) {m : MachineData} {pc : Int64}
    (h0 : m.regs.X0 = st.st.1.regs.X0) (h1 : m.regs.X1 = st.st.1.regs.X1) (hd : m.dmem = st.st.1.dmem)
    (h3 : BitVec.setWidth 32 m.regs.X3.toBitVec = 1 := by
      first | assumption | (simp only [Reg64s.setXReg]; assumption)) :
    Frame P (goto st m pc) :=
  ⟨h.exe, h.decls, h.endPc, by simp [h0, h.x0], by simp [h1, h.x1], by simp [hd, h.dl],
    by simp [hd, h.dc], .inr h3⟩

/-- The step context of a cell: `At` from `Frame` and the position (positions
below `15` are not the end: position `15` is the label `done`, at the end
address). -/
theorem Frame.at {P : Params} {st : State} (h : Frame P st) {i : Nat} (hp : AtPos st i) (hi : i < 15) :
    At st i := by
  refine ⟨h.exe, h.decls, hp, ?_⟩
  rw [hp, h.endPc, addrOf_label (i := 15) (l := "done") rfl]
  simp only [beq_eq_false_iff_ne, ne_eq]
  exact Executable.addrOf_ne_of_valid (layout swpWorker) (k := i) (n := 15) hi
    (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker]) (by
      intro l z
      rw [Layout.apply_snd, Layout.frag_getElem?]
      simp [swpWorker])

/-- Position 1 has an address of its own among the later positions. -/
theorem addrOf_ne_1 {i : Nat}
    (hi : i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 16) :
    (layout swpWorker).addrOf i ≠ (layout swpWorker).addrOf 1 := by
  have h : ∀ n, 1 < n → ((layout swpWorker).2[n - 1]?).isSome →
      (∀ l z, (layout swpWorker).2[n - 1]? ≠ some (Directive.label l, z)) →
      (layout swpWorker).addrOf n ≠ (layout swpWorker).addrOf 1 := fun n hn hs hd =>
    (Executable.addrOf_ne_of_valid (layout swpWorker) (k := 1) (n := n) hn hs hd).symm
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [addrOf_label (i := 2) (l := "try") rfl]
    exact h 2 (by decide) (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
      (by intro l z; rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
  · exact h 4 (by decide) (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
      (by intro l z; rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
  · rw [addrOf_label (i := 5) (l := "spin") rfl]
    exact h 5 (by decide) (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
      (by intro l z; rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
  · exact h 7 (by decide) (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
      (by intro l z; rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
  · exact h 8 (by decide) (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
      (by intro l z; rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
  · rw [addrOf_label (i := 9) (l := "cs") rfl]
    exact h 9 (by decide) (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
      (by intro l z; rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
  · exact h 11 (by decide) (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
      (by intro l z; rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
  · exact h 12 (by decide) (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
      (by intro l z; rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
  · exact h 13 (by decide) (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
      (by intro l z; rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
  · exact h 14 (by decide) (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
      (by intro l z; rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
  · rw [addrOf_label (i := 15) (l := "done") rfl]
    exact h 15 (by decide) (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])
      (by intro l z; rw [Layout.apply_snd, Layout.frag_getElem?]; simp [swpWorker])

/-- `W3 = 1` at every position past the first instruction. -/
theorem Frame.x3_at {P : Params} {st : State} (h : Frame P st) {i : Nat} (hp : AtPos st i)
    (hi : i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 16) :
    BitVec.setWidth 32 st.st.1.regs.X3.toBitVec = 1 :=
  h.x3.resolve_left fun h1 => addrOf_ne_1 hi (hp.symm.trans h1)

omit hv in
/-- **`Inv` after a step of thread `tid`** that leaves the memory alone. -/
theorem inv_withThread {P : Params} {tid : Nat} {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    {t t' : Thread isa} (hW : World P g) (ht : c.threads[tid]? = some t) {s : State} (hst : t'.st = s) (hF : Frame P s)
    (hL : LockWritesIn P r c.mem) {i : Nat} (hp : AtPos s i)
    (hph : Phase P tid cl i (BitVec.setWidth 32 s.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 s.st.1.regs.X5.toBitVec) t'.views r)
    (hpp : PrepaidProm P tid i t' c.mem r := by intro h; exact absurd h (by decide))
    (hla : LkMem P i (BitVec.setWidth 32 s.st.1.regs.X2.toBitVec) t'.views c.mem := by
      exact fun _ _ => ⟨fun h => absurd h (by decide), fun h => by simp at h⟩) :
    Inv P tid cl (c.withThread tid t' c.mem) r g := by
  have hn := lt_size_of_get? ht
  refine ⟨hW, t', by rw [Config.withThread_get? c t' c.mem hn, ite_eq_left rfl], hst ▸ hF, ?_, i, hst ▸ hp,
    hst ▸ hph, hpp, by simpa [Config.withThread, hst] using hla⟩
  simpa [Config.withThread] using hL

omit layout hv in
/-- `Phase` reads the views only through `vrNew`, `coh` and `vwOld`, which an
instruction that changes only `vCAP` keeps. -/
theorem Phase.congr_views {P : Params} {tid : Nat} {cl : Prop} {i : Nat} {x2 x5 : BitVec 32} {r : Res}
    {vs vs' : Views} (h : ({ vs' with vCAP := 0 } : Views) = { vs with vCAP := 0 }) :
    Phase P tid cl i x2 x5 vs' r = Phase P tid cl i x2 x5 vs r := by
  have h1 : vs'.vrNew = vs.vrNew := by simpa using congrArg Views.vrNew h
  have h2 : vs'.coh = vs.coh := by simpa using congrArg Views.coh h
  have h3 : vs'.vwOld = vs.vwOld := by simpa using congrArg Views.vwOld h
  have h4 : vs'.getCoh P.C = vs.getCoh P.C := by simp [Views.getCoh, h2]
  have h5 : vs'.fwdb = vs.fwdb := by simpa using congrArg Views.fwdb h
  have h6 : LkFwd P vs' = LkFwd P vs := by simp only [LkFwd, Views.getFwd, Views.getCoh, h5, h2]
  unfold Phase
  rw [h1, h3, h4, h6]

omit layout hv in
/-- `LkMem` reads the views only through the forwarding items and `coh`. -/
theorem LkMem.congr_views {P : Params} {i : Nat} {x2 : BitVec 32} {m : Memory} {vs vs' : Views}
    (h : ({ vs' with vCAP := 0 } : Views) = { vs with vCAP := 0 }) : LkMem P i x2 vs' m = LkMem P i x2 vs m := by
  have h2 : vs'.coh = vs.coh := by simpa using congrArg Views.coh h
  have h5 : vs'.fwdb = vs.fwdb := by simpa using congrArg Views.fwdb h
  simp only [LkMem, Views.getFwd, Views.getCoh, h5, h2]

omit layout hv in
/-- `LkMem` at another position whose requirements are among the old ones. -/
theorem LkMem.goto {P : Params} {i i' : Nat} {x2 x2' : BitVec 32} {vs : Views} {m : Memory}
    (h : LkMem P i x2 vs m) (h1 : i' ∈ [1, 3, 4, 6, 7, 8] → i ∈ [1, 3, 4, 6, 7, 8])
    (h2 : i' = 1 ∨ i' = 3 ∨ i' = 8 ∨ (i' = 7 ∧ x2' = 0) → i = 1 ∨ i = 3 ∨ i = 8 ∨ (i = 7 ∧ x2 = 0)) :
    LkMem P i' x2' vs m :=
  fun f hf => ⟨fun h' => (h f hf).1 (h1 h'), fun h' => (h f hf).2 (h2 h')⟩

/-! ## Silent cells -/

/-- Label positions share the next position's address. -/
theorem addr_3 : (layout swpWorker).addrOf 3 = (layout swpWorker).addrOf 2 :=
  addrOf_label (i := 2) (l := "try") rfl

theorem addr_6 : (layout swpWorker).addrOf 6 = (layout swpWorker).addrOf 5 :=
  addrOf_label (i := 5) (l := "spin") rfl

section Silent

variable {P : Params} {tid : Nat} {cl cl' : Prop} {c : Config isa} {r : Res} {g : Ghost} {t : Thread isa}
  {A : Arch} {iv : InstrViews} {rF : Nat → Res} {tree : EvTree State}

/-- `mov w3, #1` (position 1 → 3, `Fresh`). -/
theorem wp_mov (hW : World P g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st) (hL : LockWritesIn P r c.mem)
    (hp : AtPos t.st 1) (hph : Phase P tid cl 1 (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec) t.views r)
    (hla : LkMem P 1 (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec) t.views c.mem)
    (hex : isa.exec t.st = some tree) :
    tree.EraseWPR A tid iv rF (fun _ => True) c t (WpPostR (Inv P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  rw [exec_mov t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ hv => ?_
  rw [← Phase.congr_views hv] at hph
  rw [← LkMem.congr_views hv] at hla
  refine inv_withThread (i := 3) hW ht hst (hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl
    (by simp [Reg64s.setXReg])) hL addr_3.symm ?_ (hla := hla.goto (by decide) (by simp))
  simp only [Phase] at hph ⊢
  exact hph

/-- `cbz w2, cs` (position 4 → 10 holding, → 6 `Fresh`). -/
theorem wp_cbz (hcl : cl' → cl) (hW : World P g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st) (hL : LockWritesIn P r c.mem)
    (hp : AtPos t.st 4) (hph : Phase P tid cl 4 (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec) t.views r)
    (hla : LkMem P 4 (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec) t.views c.mem)
    (hex : isa.exec t.st = some tree) :
    tree.EraseWPR A tid iv rF (fun _ => True) c t (WpPostR (Inv P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  have hx3 := hF.x3_at hp (by decide)
  rw [exec_cbz t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ hv => ?_
  rw [← Phase.congr_views hv] at hph
  have hF' := hF.goto (m := t.st.st.1) (pc := if BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec = 0#32 then
    (layout swpWorker).addrOf 10 else (layout swpWorker).addrOf 5) rfl rfl rfl
  by_cases hz : BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec = 0#32
  · refine inv_withThread (i := 10) hW ht hst hF' hL (by simp [AtPos, hz]) ?_
    simp only [Phase] at hph ⊢
    split at hph
    case isFalse h => exact absurd hz h
    obtain ⟨S, k, hh, hm⟩ := hph
    exact ⟨S, k, hh, fun h => hm (hcl h)⟩
  · rw [← LkMem.congr_views hv] at hla
    refine inv_withThread (i := 6) hW ht hst hF' hL (by simp [AtPos, hz, addr_6]) ?_
      (hla := hla.goto (by decide) (by simp))
    simp only [Phase] at hph ⊢
    split at hph
    case isTrue h => exact absurd h hz
    exact hph

/-- `cbnz w2, spin` (position 7 → 8 or 6, `Fresh`). -/
theorem wp_cbnz (hW : World P g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st) (hL : LockWritesIn P r c.mem)
    (hp : AtPos t.st 7) (hph : Phase P tid cl 7 (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec) t.views r)
    (hla : LkMem P 7 (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec) t.views c.mem)
    (hex : isa.exec t.st = some tree) :
    tree.EraseWPR A tid iv rF (fun _ => True) c t (WpPostR (Inv P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  have hx3 := hF.x3_at hp (by decide)
  rw [exec_cbnz t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ hv => ?_
  rw [← Phase.congr_views hv] at hph
  have hF' := hF.goto (m := t.st.st.1) (pc := if BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec = 0#32 then
    (layout swpWorker).addrOf 8 else (layout swpWorker).addrOf 6) rfl rfl rfl
  by_cases hz : BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec = 0#32
  · rw [← LkMem.congr_views hv] at hla
    refine inv_withThread (i := 8) hW ht hst hF' hL (by simp [AtPos, hz]) ?_
      (hla := hla.goto (by decide) fun _ => .inr (.inr (.inr ⟨rfl, hz⟩)))
    simp only [Phase] at hph ⊢
    exact hph
  · rw [← LkMem.congr_views hv] at hla
    refine inv_withThread (i := 6) hW ht hst hF' hL (by simp [AtPos, hz]) ?_
      (hla := hla.goto (by decide) (by simp))
    simp only [Phase] at hph ⊢
    exact hph

/-- `b try` (position 8 → 3, `Fresh`). -/
theorem wp_b_try (hW : World P g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st) (hL : LockWritesIn P r c.mem)
    (hp : AtPos t.st 8) (hph : Phase P tid cl 8 (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec) t.views r)
    (hla : LkMem P 8 (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec) t.views c.mem)
    (hex : isa.exec t.st = some tree) :
    tree.EraseWPR A tid iv rF (fun _ => True) c t (WpPostR (Inv P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  have hx3 := hF.x3_at hp (by decide)
  rw [exec_b_try t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ hv => ?_
  rw [← Phase.congr_views hv] at hph
  rw [← LkMem.congr_views hv] at hla
  refine inv_withThread (i := 3) hW ht hst (hF.goto rfl rfl rfl) hL rfl ?_ (hla := hla.goto (by decide) (by simp))
  simp only [Phase] at hph ⊢
  exact hph

/-- `add w5, w5, #1` (position 11 → 12): `X5`'s low word becomes `k + 1`. -/
theorem wp_add (hcl : cl' → cl) (hW : World P g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st) (hL : LockWritesIn P r c.mem)
    (hp : AtPos t.st 11) (hph : Phase P tid cl 11 (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec) t.views r)
    (hex : isa.exec t.st = some tree) :
    tree.EraseWPR A tid iv rF (fun _ => True) c t (WpPostR (Inv P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  have hx3 := hF.x3_at hp (by decide)
  rw [exec_add t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ hv => ?_
  rw [← Phase.congr_views hv] at hph
  refine inv_withThread (i := 12) hW ht hst (hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl) hL
    rfl ?_
  simp only [Phase] at hph ⊢
  obtain ⟨S, k, hh, hm⟩ := hph
  refine ⟨S, k, hh, fun h => ?_⟩
  obtain ⟨hq, hm⟩ := hm (hcl h)
  refine ⟨hq, hm.imp (fun ⟨ts, hg, hc, hx⟩ => ⟨ts, hg, hc, ?_⟩) id⟩
  have h1 : t.st.st.1.regs.X5.toBitVec.take 32 = BitVec.ofNat 32 k := by rw [← hx]; rfl
  simp only [Reg64s.setXReg]
  rw [h1]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.add_mod]

/-- `b done` (position 14 → 16). -/
theorem wp_b_done (hcl : cl' → cl) (hW : World P g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st) (hL : LockWritesIn P r c.mem)
    (hp : AtPos t.st 14) (hph : Phase P tid cl 14 (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec) t.views r)
    (hex : isa.exec t.st = some tree) :
    tree.EraseWPR A tid iv rF (fun _ => True) c t (WpPostR (Inv P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  have hx3 := hF.x3_at hp (by decide)
  rw [exec_b_done t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ _ => ?_
  refine inv_withThread (i := 16) hW ht hst (hF.goto rfl rfl rfl) hL rfl ?_
  simp only [Phase] at hph ⊢
  exact ⟨hph.1, fun h => hph.2 (hcl h)⟩

/-- `ldr w2, [x0]` (position 6 → 7, `Fresh`): a load, nothing changes but
`X2` and the views. -/
theorem wp_ldr_spin (hW : World P g) (ht : c.threads[tid]? = some t) (hF : Frame P t.st) (hL : LockWritesIn P r c.mem)
    (hp : AtPos t.st 6) (hph : Phase P tid cl 6 (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec) t.views r)
    (hla : LkMem P 6 (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec) t.views c.mem)
    (hex : isa.exec t.st = some tree) :
    tree.EraseWPR A tid iv rF (fun _ => True) c t (WpPostR (Inv P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem) := by
  have hx3 := hF.x3_at hp (by decide)
  rw [exec_ldr_spin t.st (hF.at hp (by decide)) hF.x0 hF.dl] at hex
  cases hex
  refine EvTree.eraseWPR_load fun x hx => ?_
  obtain ⟨hm, hpr⟩ := readSuccs_memProm A iv hx
  refine WpPostR.noWrite hm hpr fun t' hst _ hv => ?_
  have h5 : t'.views.fwdb = x.2.2.views.fwdb := by simpa using congrArg Views.fwdb hv
  have hfw : ∀ f, t'.views.getFwd P.Lk = some f → t.views.getFwd P.Lk = some f := fun f hf => by
    simpa only [Views.getFwd, h5, SpinCommon.readSuccs_fwdb A iv hx] using hf
  have hcoh : t'.views.getCoh P.Lk = x.2.2.views.getCoh P.Lk := by
    simp only [Views.getCoh]; rw [show t'.views.coh = x.2.2.views.coh by simpa using congrArg Views.coh hv]
  simp only [Phase] at hph
  refine inv_withThread (i := 7) hW ht hst (hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl) hL
    rfl ?_ (hla := fun f hf => ?_)
  · simp only [Phase]
    refine ⟨hph.1, fun f hf => Nat.le_trans (hph.2 f (hfw f hf)) ?_⟩
    rw [hcoh]; exact SpinCommon.readSuccs_getCoh_le A iv hx
  obtain ⟨w, hw, hwl, hwv⟩ := (hla f (hfw f hf)).1 (by decide)
  refine ⟨fun _ => ⟨w, hw, hwl, hwv⟩, fun h => ?_⟩
  have hz : BitVec.setWidth 32 x.2.1 = 0 := by
    have h' := h.resolve_left (by decide) |>.resolve_left (by decide) |>.resolve_left (by decide) |>.2
    simpa [Reg64s.setXReg] using h'
  rw [hcoh]
  refine SpinCommon.readSuccs_writeIn_of_ne hx (hph.2 f (hfw f hf)) hw hwl (fun he => ?_)
    fun f' hf' => by rw [hfw f hf] at hf'; cases hf'; rfl
  rw [he, hwv] at hz; exact absurd hz (by decide)

end Silent

end Kraken.Promising.SLR.SwpInv
