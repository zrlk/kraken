/-
**Liveness of `treiber_pp.kl` for AArch64 on the
semantic machine** (`TraceSem` under `Arch.armv8`, promises included), under
weak fairness and memory fairness.

`treiber_pp_live_sem`: on every semantic trace from the whole-image start
configuration of `treiber_pp_envG_whole` (any layout, any fuel), weakly fair
(`WeakFairSem`) and memory fair (`MemFair`), the pusher and the popper both
reach their end addresses (`Done`). It instantiates the staged-freezing
skeleton `TreiberPp.skeleton` (`LiveTreiberPpSkel.lean`); its interface
fields are proved here from the thread steps and invariant of
`LiveTreiberPpA64Inv.lean`:

- a thread taking infinitely many instruction steps never has a successful
  `CASAL` (`noS1`: it would walk to its end, where it has no step) and loads
  `top` infinitely often (`walk1`, `reads_inf`);
- the writes to `top` are at most `2 * (1 + fuel)` (`cnt_bound`), so `top`'s
  last write is eventually constant (`TreiberPp.top_const`); a thread that
  loads `top` infinitely often then catches up with it (`MemFair`) and its
  next `CASAL` succeeds (`catchup`), unless (popper) `top` is `0` (`spin0`,
  `spin1`);
- a popper promise to `top` would persist and stay above the popper's
  coherence view, against memory fairness (`pop_noApp`); with a popper that
  never changes memory, every write to `top` is the pusher's node
  (`topVals`), so a finished pusher left `top = n ≠ 0` (`pushed`).

The fault-freedom side (`OkStepsPF`, an outcome for every running thread) is
a hypothesis of the generic `treiber_pp_live_gen`; `treiber_pp_live_sem`
discharges it with no declarations (every tree of the image is fault-free),
the runner forms (`LiveTreiberPpA64Runner.lean`) by
`treiber_pp_envG_runner_faultFree_sem`.
-/
import Kraken.Promising.LiveTreiberPpA64Inv
import Kraken.Promising.LiveRank
import Kraken.Promising.LiveOkStepsA64
import Kraken.Promising.SLR.EnvG.A64NoFault
import Kraken.Promising.SLR.EnvG.A64Live
import Kraken.Promising.SLR.EnvG.A64WholeTreiberRunner

namespace Kraken.Promising.Live.TreiberPpA64

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Term Kraken.Promising.Live.NoStuck
open Kraken.Promising.SLR.EnvG.Treiber (treiberImageA treiberImageA_noFault StartPushW StartPopW StartPushWD
  StartPopWD)

/-- **Thread `k` has finished**: it is at its end address. -/
def Done (k : Nat) (c : Config isa) : Prop := ∃ th, c.threads[k]? = some th ∧ th.st.st.2 = th.st.endPc

/-- The walk measure towards the next load of `top`. -/
def mu (p : Nat) : Nat :=
  match p with
  | 1 => 7 | 4 => 6 | 5 => 5 | 6 => 4 | 7 => 3 | 8 => 2 | 9 => 1
  | 14 => 10 | 15 => 9 | 16 => 8 | 17 => 7 | 18 => 6 | 19 => 5 | 20 => 3 | 21 => 2 | 22 => 1
  | _ => 0

theorem mu_next {p : Nat} (md : MachineData) (hp : p ∈ tPcs) (h3 : ¬ (p = 3 ∨ p = 13)) (he : p ≠ 11)
    (he' : p ≠ 24) : mu (nextP p md) < mu p := by
  simp only [tPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> first | (simp_all [nextP, mu]; done) | (simp only [nextP]; split <;> simp [mu])

theorem sOf_le (p : Nat) (s : MachineData) : sOf p s ≤ 1 := by
  unfold sOf; repeat (first | split | omega)

theorem fwd {p : Nat} {md : MachineData} (h : sOf p md = 1) (hp : p ∈ tPcs) (he : p ≠ 11) (he' : p ≠ 24) :
    p < nextP p md ∧ nextP p md ≤ 24 := by
  simp only [tPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> simp_all [sOf, nextP]

theorem end_ne {r i : Nat} (hi : i ∈ pcsR r) (he : i ≠ endP r) : i ≠ 11 ∧ i ≠ 24 := by
  by_cases h0 : r = 0 <;> simp only [pcsR, endP, h0, ↓reduceIte, List.mem_cons, List.not_mem_nil,
    or_false] at hi he ⊢ <;> omega

theorem sz64 (n : BitVec 64) : BitVec.setWidth 64 (BitVec.setWidth 128 n) = n :=
  BitVec.setWidth_setWidth_of_le _ (by decide)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout treiberImageA)]

set_option hygiene false in
local notation "pcT" => (layout treiberImageA).addrOf

/-- Off its end a thread is at a cell of the image. -/
theorem codeAt_of {ds : Decls} {t n : BitVec 64} {r : Nat} {s : isa.State} (hS : Static ds t n r s)
    (hP : PcOK r s) (hne : s.st.2 ≠ s.endPc) : ∃ d z rest, (layout treiberImageA).codeAt s.st.2 = (d, z) :: rest := by
  obtain ⟨i, hi, hpc, -⟩ := hP
  have he : i ≠ endP r := fun e => hne (by rw [hpc, hS.endPc, e])
  obtain ⟨e11, e24⟩ := end_ne hi he
  have hi' := mem_tPcs hi
  simp only [tPcs, List.mem_cons, List.not_mem_nil, or_false] at hi'
  have hl : i < treiberImageA.length := by simp only [treiberImageA, List.length_cons, List.length_nil]; omega
  have hc := Kraken.Executable.codeAt_addrOf (d := treiberImageA[i]) (by
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> first | omega | simp [treiberImageA, Directive.isLabel])
    (List.getElem?_eq_getElem hl)
  rw [hpc]; exact ⟨_, _, _, hc⟩

/-- Off its end a thread is running. -/
theorem halted_false {ds : Decls} {t n : BitVec 64} {r : Nat} {u : Thread isa} (hS : Static ds t n r u.st)
    (hP : PcOK r u.st) (hne : u.st.st.2 ≠ u.st.endPc) : u.halted = false := by
  obtain ⟨d, z, rest, hc⟩ := codeAt_of hS hP hne
  simp [Thread.halted, exec_eq_of_codeAtD hS.exe (by simpa using hne) hc]

/-- With no declarations, off its end a thread's tree is fault-free. -/
theorem noFault_at {t n : BitVec 64} {r : Nat} {s : isa.State} (hS : Static {} t n r s) (hP : PcOK r s)
    (hne : s.st.2 ≠ s.endPc) : ∀ tree, isa.exec s = some tree → tree.NoFault := by
  obtain ⟨d, z, rest, hc⟩ := codeAt_of hS hP hne
  exact AArch64.EnvG.noFault_of_codeAt hS.exe hS.decls hc (treiberImageA_noFault d z (AArch64.EnvG.mem_of_codeAt hc))

/-- The start states. -/
theorem start0 {ds : Decls} {t n : BitVec 64} {s : isa.State} (h : StartPushWD ds t n s) :
    Static ds t n 0 s ∧ s.st.2 = pcT 1 :=
  ⟨⟨h.exe, h.decls, h.endPc.trans label_pdone, h.x0, h.dt, fun _ => h.x1, fun _ => h.dd, fun _ => h.dn,
    fun h => absurd rfl h⟩, h.pc.trans label_pusher⟩

theorem start1 {ds : Decls} {t n : BitVec 64} {s : isa.State} (h : StartPopWD ds t s) :
    Static ds t n 1 s ∧ s.st.2 = pcT 13 :=
  ⟨⟨h.exe, h.decls, h.endPc.trans label_qdone, h.x0, h.dt, fun e => absurd e (by decide), fun e => absurd e (by decide),
    fun e => absurd e (by decide), fun _ => h.d4⟩, h.pc.trans label_popper⟩

/-- **`OkStepsPF` with no declarations**, under the invariant. -/
theorem okSteps_empty {t n : BitVec 64} {fuel : Nat} {c : Config isa} (h : Inv {} t n fuel c) :
    OkStepsPF Arch.armv8 c := by
  intro tid u hu hh hp
  have hTI := h.thr tid u hu
  have hne : u.st.st.2 ≠ u.st.endPc := fun e => by
    rw [Thread.halted, exec_end hTI.st (e.trans hTI.st.endPc)] at hh; cases hh
  cases hs : stepOne Arch.armv8 u tid c.mem with
  | none => rw [halted_of_stepOne_none hs] at hh; cases hh
  | some outs =>
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil outs (stepOne_ne_nil _ (h.bnd tid u hu) hp hs)
    cases r with
    | error m =>
      exact absurd ⟨outs, by show (c.threads[tid]?.bind fun t => stepOne Arch.armv8 t tid c.mem) = some outs; rw [hu]; exact hs,
        hr⟩ (Config.not_faultStep_of_noFaultRun _ hu (fun tree hex =>
          (noFault_at hTI.st hTI.pc hne tree hex).run _ _ _ _) m)
    | ok o => exact ⟨outs, o, rfl, hr⟩

/-- `top`'s final value: its initial value (no write) or a message's. -/
theorem fv_msg {m : Memory} {l : Loc} {P : Val → Prop} (h0 : m.lastWrite l = 0 → P (m.initVal l))
    (h : ∀ ts w, m.get? ts = some w → w.loc = l → P w.val) : P (m.finalVal l) := by
  rcases m.read?_eq_some (m.read?_lastWrite l) with ⟨e, hv⟩ | ⟨w, hw, hl, hv⟩
  · rw [hv]; exact h0 e
  · rw [hv]; exact h _ w hw hl

theorem final_false {c : Config isa} {k : Nat} {u : Thread isa} (hu : c.threads[k]? = some u)
    (hh : u.halted = false) : c.final = false := by
  rw [Bool.eq_false_iff]; intro hf
  obtain ⟨hk, rfl⟩ := Array.getElem?_eq_some_iff.mp hu
  have := Array.all_eq_true.mp hf k hk
  simp [hh] at this

theorem reach {fuel : Nat} (tr : TraceSem Arch.armv8 fuel isa) (j : Nat) :
    Live.Bridge.ReachableSem Arch.armv8 fuel (tr.cfg 0) (tr.cfg j) := by
  induction j with
  | zero => exact .refl _
  | succ j ih =>
    rcases tr.step j with ⟨k, hk⟩ | ⟨-, he⟩
    · exact reachableSem_snoc ih hk
    · rw [he]; exact ih

/-! ## Along a trace -/

section Trace

variable {ds : Decls} {t n : BitVec 64} (hT : ds.AgreesAt t 8) (hD : ds.AgreesAt n 4)
  (hN : ds.AgreesAt (n + 8#64) 8) (htn : t ≠ n + 8#64) {fuel : Nat} (tr : TraceSem Arch.armv8 fuel isa)
  (hI0 : Inv ds t n fuel (tr.cfg 0))

include hT hD hN htn hI0

theorem inv_at (j : Nat) : Inv ds t n fuel (tr.cfg j) := by
  induction j with
  | zero => exact hI0
  | succ j ih =>
    rcases tr.step j with ⟨k, hk⟩ | ⟨-, he⟩
    · obtain ⟨u, hu⟩ := TreiberPp.stepSem_get hk
      exact ih.step hT hD hN htn hu hk
    · rw [he]; exact ih

theorem get_thr (j : Nat) {k : Nat} (hk : k < 2) : ∃ u, (tr.cfg j).threads[k]? = some u := by
  have : k < (tr.cfg j).threads.size := by rw [(inv_at hT hD hN htn tr hI0 j).size]; exact hk
  exact ⟨_, Array.getElem?_eq_getElem this⟩

theorem lt2 {j k : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[k]? = some u) : k < 2 := by
  have := lt_size_of_get? hu; rwa [(inv_at hT hD hN htn tr hI0 j).size] at this

/-- The step lemma at a trace index. -/
theorem stepAt {j k : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[k]? = some u) {outs} {o : Outcome isa}
    (hs : stepOne Arch.armv8 u k (tr.cfg j).mem = some outs) (ho : .ok o ∈ outs) :
    StepOK ds t n k u (tr.cfg j).mem o :=
  have h := (inv_at hT hD hN htn tr hI0 j).thr k u hu
  thread_step hT hD hN htn h.st hs ho h.pc

/-- At its end a thread has no step. -/
theorem end_none {j k : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[k]? = some u) (he : pos u = endP k)
    (A : Arch) (mem : Memory) : stepOne A u k mem = none := by
  have h := (inv_at hT hD hN htn tr hI0 j).thr k u hu
  obtain ⟨i, hi, hpc, -⟩ := h.pc
  refine stepOne_end' h.st ?_ A k mem
  rw [hpc, ← he, pos, hpc, posOf_pcT (mem_tPcs hi)]

/-- **A thread taking infinitely many instruction steps never succeeds**: it
would walk to its end, where it has no step. -/
theorem noS1 {T : Nat} (hinf : InfOften fun k => InstrSem Arch.armv8 fuel T (tr.cfg k) (tr.cfg (k + 1)))
    {j : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[T]? = some u) : S u = 0 := by
  have hT2 := lt2 hT hD hN htn tr hI0 hu
  apply Classical.byContradiction
  intro h1
  have h1 : S u = 1 := by have := sOf_le (pos u) u.st.st.1; unfold S at h1 ⊢; omega
  obtain ⟨k, -, hk⟩ := TreiberPp.walk tr hinf (m := 0) (fun v => S v = 1) (fun s => 25 - posOf s.st.2)
    (fun _ => False) (fun v v' h e _ => by unfold S pos at h ⊢; rw [e]; exact h)
    (fun k v outs oc _ hv hP hs ho he => by
      have q := stepAt hT hD hN htn tr hI0 hv hs ho
      have hne : pos v ≠ endP T := fun e => by rw [end_none hT hD hN htn tr hI0 hv e] at hs; cases hs
      obtain ⟨i, hi, hpc, -⟩ := q.pc
      obtain ⟨i', hi', hpc', -⟩ := ((inv_at hT hD hN htn tr hI0 k).thr T v hv).pc
      have hp : pos v = i' := by rw [pos, hpc', posOf_pcT (mem_tPcs hi')]
      have hpv : pos v ∈ tPcs := hp ▸ mem_tPcs hi'
      obtain ⟨e11, e24⟩ := end_ne (hp ▸ hi') hne
      obtain ⟨hlt, hle⟩ := fwd hP hpv e11 e24
      have hS' : S oc.thread = 1 := by
        have : S oc.thread ≤ 1 := sOf_le _ _
        rcases q.eff with ⟨-, -, e⟩ | ⟨w, -, e, -⟩
        · omega
        · split at e <;> omega
      refine .inr ⟨hS', ?_⟩
      show 25 - pos oc.thread < 25 - pos v
      rw [q.nx]; omega) j u (Nat.zero_le _) hu h1
  exact hk

/-- **A thread taking infinitely many instruction steps loads `top`
infinitely often**, each time from position `3` or `13`. -/
theorem walk1 {T : Nat} (hinf : InfOften fun k => InstrSem Arch.armv8 fuel T (tr.cfg k) (tr.cfg (k + 1)))
    (hT2 : T < 2) (j : Nat) :
    ∃ k, j ≤ k ∧ ∃ u outs oc, (tr.cfg k).threads[T]? = some u ∧ (pos u = 3 ∨ pos u = 13) ∧
      stepOne Arch.armv8 u T (tr.cfg k).mem = some outs ∧ .ok oc ∈ outs ∧
      tr.cfg (k + 1) = (tr.cfg k).withThread T oc.thread oc.mem := by
  obtain ⟨u, hu⟩ := get_thr hT hD hN htn tr hI0 j hT2
  refine TreiberPp.walk tr hinf (m := 0) (fun _ => True) (fun s => mu (posOf s.st.2)) _ (fun _ _ _ _ _ => trivial)
    (fun k v outs oc _ hv _ hs ho he => ?_) j u (Nat.zero_le _) hu trivial
  by_cases h3 : pos v = 3 ∨ pos v = 13
  · exact .inl ⟨v, outs, oc, hv, h3, hs, ho, he⟩
  have q := stepAt hT hD hN htn tr hI0 hv hs ho
  obtain ⟨i', hi', hpc', -⟩ := ((inv_at hT hD hN htn tr hI0 k).thr T v hv).pc
  have hp : pos v = i' := by rw [pos, hpc', posOf_pcT (mem_tPcs hi')]
  have hne : i' ≠ endP T := fun e => by rw [end_none hT hD hN htn tr hI0 hv (hp.trans e)] at hs; cases hs
  refine .inr ⟨trivial, ?_⟩
  show mu (pos oc.thread) < mu (pos v)
  rw [q.nx, hp]; rw [hp] at h3
  refine mu_next _ (mem_tPcs hi') h3 (fun e => hne ?_) (fun e => hne ?_) <;> subst e
  · rw [role0 hi' (by decide)]; rfl
  · simp [endP, role1 hi' (by decide)]

theorem reads_inf {T : Nat} (hinf : InfOften fun k => InstrSem Arch.armv8 fuel T (tr.cfg k) (tr.cfg (k + 1)))
    (hT2 : T < 2) : InfOften (fun i => ∃ ts, ReadsAt Arch.armv8 tr.cfg T (topL t) ts i) := fun j => by
  obtain ⟨k, hk, u, outs, oc, hu, h3, hs, ho, he⟩ := walk1 hT hD hN htn tr hI0 hinf hT2 j
  have hTI := (inv_at hT hD hN htn tr hI0 k).thr T u hu
  obtain ⟨ts, v, ν, hl⟩ := step_reads hT hTI.st hs ho hTI.pc h3
  exact ⟨k, hk, ts, u, outs, oc, hu, hs, ho, he, v, ν, hl⟩

/-- **The writes to `top` are bounded.** -/
theorem cnt_bound (j : Nat) : (tr.cfg j).mem.cntBelow (topL t) (tr.cfg j).mem.last ≤ 2 * (1 + fuel) := by
  have h := inv_at hT hD hN htn tr hI0 j
  have := tsum_le (c := tr.cfg j) (F := fun _ u => S u + (tr.cfg j).mem.promAt (topL t) u.prom) (M := 1 + fuel)
    fun i v hv => by
      have := sOf_le (pos v) v.st.st.1
      have := promAt_le_length (m := (tr.cfg j).mem) (l := topL t) (p := v.prom)
      have := (h.thr i v hv).plen
      simp only [S]; omega
  rw [h.size] at this
  have := h.cnt
  omega

/-- **Catching up**: once `top`'s last write `L` and final value `F` are
constant from `m` on, a thread taking infinitely many instruction steps
whose coherence view reaches `L` would succeed (the popper only if `F`'s low
word is not `0`). -/
theorem catchup {T : Nat} (hinf : InfOften fun k => InstrSem Arch.armv8 fuel T (tr.cfg k) (tr.cfg (k + 1)))
    (hT2 : T < 2) {m : Nat} {L : Time} {F : Val}
    (hc : ∀ j, m ≤ j → (tr.cfg j).mem.lastWrite (topL t) = L ∧ (tr.cfg j).mem.finalVal (topL t) = F)
    (hF : T ≠ 0 → BitVec.setWidth 64 F ≠ 0) {j : Nat} (hj : m ≤ j) {u : Thread isa}
    (hu : (tr.cfg j).threads[T]? = some u) (hL : L ≤ u.views.getCoh (topL t)) : False := by
  obtain ⟨k, hk, u', outs, oc, hu', h3, hs, ho, he⟩ := walk1 hT hD hN htn tr hI0 hinf hT2 j
  have hL' : L ≤ u'.views.getCoh (topL t) := Nat.le_trans hL (TreiberPp.coh_mono tr hk hu hu' _)
  have q := stepAt hT hD hN htn tr hI0 hu' hs ho
  have hx2 := q.ld h3 (by rw [(hc k (by omega)).1]; exact hL')
  rw [(hc k (by omega)).2] at hx2
  -- the walk from the load to the `CASAL`
  let ps := if T = 0 then [4, 5, 6] else [14, 15, 16, 17]
  have hst : pos oc.thread ∈ ps := by
    obtain ⟨i', hi', hpc', -⟩ := ((inv_at hT hD hN htn tr hI0 k).thr T u' hu').pc
    have hp : pos u' = i' := by rw [pos, hpc', posOf_pcT (mem_tPcs hi')]
    rw [q.nx]
    unfold ps
    rcases h3 with e | e <;> rw [e] <;> rw [e] at hp <;> subst hp
    · rw [ite_eq_left (role0 hi' (by decide))]; simp [nextP]
    · rw [ite_eq_right (role1 hi' (by decide))]; simp [nextP]
  obtain ⟨_, -, hf⟩ := TreiberPp.walk tr hinf (m := m)
    (fun v => pos v ∈ ps ∧ v.st.st.1.regs.X2.toBitVec = BitVec.setWidth 64 F ∧ L ≤ v.views.getCoh (topL t))
    (fun s => 20 - posOf s.st.2) (fun _ => False)
    (fun v v' h e1 e2 => by unfold pos at h ⊢; rw [e1, e2]; exact h)
    (fun k' v outs' oc' hk' hv hP hs' ho' he' => by
      have q' := stepAt hT hD hN htn tr hI0 hv hs' ho'
      obtain ⟨hp, hx, hl⟩ := hP
      have hl' : L ≤ oc'.thread.views.getCoh (topL t) := Nat.le_trans hl ((stepOne_dord _ hs' ho').2.1 _)
      by_cases h6 : pos v = 6 ∨ pos v = 17
      · -- the `CASAL` succeeds
        have hx3 := q'.cas h6 (by rw [(hc k' hk').1]; exact hl)
        rw [(hc k' hk').2] at hx3
        have hx2' := q'.x2 (by omega) (by omega)
        have hS1 : S oc'.thread = 1 := by
          unfold S; rw [q'.nx]
          rcases h6 with h6 | h6 <;> simp [h6, nextP, sOf, hx3, hx2', hx]
        have := noS1 hT hD hN htn tr hI0 hinf (tr.wt_self hv he')
        omega
      · have hx2' := q'.x2 (by unfold ps at hp; split at hp <;> simp at hp <;> omega)
          (by unfold ps at hp; split at hp <;> simp at hp <;> omega)
        have hn' : pos oc'.thread = pos v + 1 ∧ pos v + 1 ∈ ps := by
          rw [q'.nx]
          unfold ps at hp ⊢
          split at hp
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with e | e | e <;> rw [e] at h6 ⊢ <;> simp_all [nextP]
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with e | e | e | e <;> rw [e] at h6 ⊢ <;> simp_all [nextP]
        refine .inr ⟨⟨hn'.1 ▸ hn'.2, by rw [hx2']; exact hx, hl'⟩, ?_⟩
        show 20 - pos oc'.thread < 20 - pos v
        have : pos v < 20 := by unfold ps at hp; split at hp <;> simp at hp <;> omega
        omega)
    (k + 1) oc.thread (by omega) (tr.wt_self hu' he) ⟨hst, hx2, Nat.le_trans hL' ((stepOne_dord _ hs ho).2.1 _)⟩
  exact hf

/-- A finished thread is at its end position. -/
theorem pos_end {j k : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[k]? = some u)
    (hd : u.st.st.2 = u.st.endPc) : pos u = endP k := by
  rw [pos, hd, ((inv_at hT hD hN htn tr hI0 j).thr k u hu).st.endPc]
  exact posOf_pcT (by unfold endP; split <;> decide)

theorem nostep {k j : Nat} (hd : Done k (tr.cfg j)) : ¬ StepSem Arch.armv8 fuel k (tr.cfg j) (tr.cfg (j + 1)) := by
  obtain ⟨u, hu, hpc⟩ := hd
  have hn := end_none hT hD hN htn tr hI0 hu (pos_end hT hD hN htn tr hI0 hu hpc)
  rintro (⟨u', outs, o, hu', hs, -⟩ | ⟨u', w, hu', -, hc, -⟩) <;> rw [hu] at hu' <;> cases hu'
  · rw [hn] at hs; cases hs
  · have hh : u.halted = true := halted_of_stepOne_none (hn Arch.armv8 (tr.cfg j).mem)
    exact not_certOkN_of_halted (t := promThread u (tr.cfg j).mem w) hh
      (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)) hc

theorem done_mono {k j j' : Nat} (hjj : j ≤ j') (hd : Done k (tr.cfg j)) : Done k (tr.cfg j') := by
  induction hjj with
  | refl => exact hd
  | step _ ih =>
    rcases tr.step _ with ⟨k', hk⟩ | ⟨-, he⟩
    · by_cases e : k = k'
      · subst e; exact absurd hk (nostep hT hD hN htn tr hI0 ih)
      · obtain ⟨u, hu, hpc⟩ := ih
        exact ⟨u, by rw [TreiberPp.get_of_stepSem_ne hk e]; exact hu, hpc⟩
    · rw [he]; exact ih

theorem running {j k : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[k]? = some u) (hd : ¬ Done k (tr.cfg j)) :
    u.halted = false :=
  have h := (inv_at hT hD hN htn tr hI0 j).thr k u hu
  halted_false h.st h.pc fun e => hd ⟨u, hu, e⟩

/-- **Spin(pusher)**: a pusher taking infinitely many instruction steps
catches up with `top` and succeeds. -/
theorem spin0 (hmf : MemFair Arch.armv8 tr.cfg)
    (hinf : InfOften fun k => InstrSem Arch.armv8 fuel 0 (tr.cfg k) (tr.cfg (k + 1))) : False := by
  obtain ⟨m, -, hc⟩ := TreiberPp.top_const tr (topL t) (i := 0) fun j _ => cnt_bound hT hD hN htn tr hI0 j
  obtain ⟨u0, hu0⟩ := get_thr hT hD hN htn tr hI0 m (by decide : 0 < 2)
  exact memFair_lastWrite_false hmf (reads_inf hT hD hN htn tr hI0 hinf (by decide)) hu0 fun j hj u hu hL =>
    catchup hT hD hN htn tr hI0 hinf (by decide) hc (fun h => absurd rfl h) hj hu hL

/-- A popper instruction step does not change memory or its promises. -/
theorem pop_instr (hinf : InfOften fun k => InstrSem Arch.armv8 fuel 1 (tr.cfg k) (tr.cfg (k + 1))) {j : Nat}
    {u : Thread isa} {outs} {o : Outcome isa} (hu : (tr.cfg j).threads[1]? = some u)
    (hs : stepOne Arch.armv8 u 1 (tr.cfg j).mem = some outs) (ho : .ok o ∈ outs)
    (he : tr.cfg (j + 1) = (tr.cfg j).withThread 1 o.thread o.mem) :
    o.mem = (tr.cfg j).mem ∧ o.thread.prom = u.prom := by
  rcases (stepAt hT hD hN htn tr hI0 hu hs ho).eff with ⟨hm, hp, -⟩ | ⟨w, -, hS, hq⟩
  · exact ⟨hm, hp⟩
  · have h0 := noS1 hT hD hN htn tr hI0 hinf (tr.wt_self hu he)
    simp only [Q, Nat.one_ne_zero, ↓reduceIte] at hq
    simp only [hq, ↓reduceIte] at hS; omega

/-- **A popper taking infinitely many instruction steps never changes
memory**: an instruction write would be a successful `CASAL`, and a promise
(to `top`) would stay outstanding, above the popper's view of `top`, against
memory fairness. -/
theorem pop_noApp (h0 : ∀ (k : Nat) (u : Thread isa), (tr.cfg 0).threads[k]? = some u → u.prom = [])
    (hmf : MemFair Arch.armv8 tr.cfg)
    (hinf : InfOften fun k => InstrSem Arch.armv8 fuel 1 (tr.cfg k) (tr.cfg (k + 1))) :
    ∀ k, StepSem Arch.armv8 fuel 1 (tr.cfg k) (tr.cfg (k + 1)) → (tr.cfg (k + 1)).mem = (tr.cfg k).mem := by
  intro k hk
  rcases hk with ⟨u, outs, o, hu, hs, ho, -, he⟩ | ⟨u, w, hu, -, -, he⟩
  · rw [he]; exact (pop_instr hT hD hN htn tr hI0 hinf hu hs ho he).1
  exfalso
  have hpl : ∀ (j k : Nat) (u : Thread isa), (tr.cfg j).threads[k]? = some u → ∀ ts ∈ u.prom,
      ts ≤ (tr.cfg j).mem.last := fun j k u hu => ((inv_at hT hD hN htn tr hI0 j).thr k u hu).promLe
  have hu1 : (tr.cfg (k + 1)).threads[1]? = some (promThread u (tr.cfg k).mem w) := by
    rw [he]; exact withThread_get_self hu
  have hts : (tr.cfg k).mem.last + 1 ∈ (promThread u (tr.cfg k).mem w).prom := by
    simp [Memory.append, Memory.last]
  have hw : (tr.cfg (k + 1)).mem.get? ((tr.cfg k).mem.last + 1) = some w := by
    rw [he]; exact Memory.get?_append_last _ _
  have hl : w.loc = topL t := by
    have := ((inv_at hT hD hN htn tr hI0 (k + 1)).thr 1 _ hu1).good _ hts w hw
    simpa [Q] using this
  have persist : ∀ j, k + 1 ≤ j → ∃ v, (tr.cfg j).threads[1]? = some v ∧ (tr.cfg k).mem.last + 1 ∈ v.prom := by
    intro j hj
    induction hj with
    | refl => exact ⟨_, hu1, hts⟩
    | step _ ih =>
      obtain ⟨v, hv, hm⟩ := ih
      rcases tr.step _ with ⟨k', hk'⟩ | ⟨-, he'⟩
      · by_cases e : 1 = k'
        · subst e
          rcases hk' with ⟨v', outs, o, hv', hs, ho, -, he'⟩ | ⟨v', w', hv', -, -, he'⟩ <;> rw [hv] at hv' <;>
            cases hv'
          · exact ⟨_, tr.wt_self hv he', by rw [(pop_instr hT hD hN htn tr hI0 hinf hv hs ho he').2]; exact hm⟩
          · exact ⟨_, by rw [he']; exact withThread_get_self hv, List.mem_append_left _ hm⟩
        · exact ⟨v, by rw [TreiberPp.get_of_stepSem_ne hk' e]; exact hv, hm⟩
      · exact ⟨v, by rw [he']; exact hv, hm⟩
  obtain ⟨j, hj, v, hv, hle⟩ := memFair_catchup hmf (reads_inf hT hD hN htn tr hI0 hinf (by decide)) hw hl
  obtain ⟨v', hv', hm⟩ := persist j hj
  rw [hv] at hv'; cases hv'
  have hw' : (tr.cfg j).mem.get? ((tr.cfg k).mem.last + 1) = some w := by
    rw [(tr.prefix_le hj).get? ((tr.cfg (k + 1)).mem.last_le_of_get?_eq_some hw)]; exact hw
  have := TreiberPp.coh_lt_of_prom tr h0 hpl hv hm hw'
  rw [hl] at this; exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le this hle)

/-- **With a popper that never changes memory, every write to `top` is the
pusher's node.** -/
theorem topVals (hm0 : ∀ ts, (tr.cfg 0).mem.get? ts = none)
    (hna : ∀ k, StepSem Arch.armv8 fuel 1 (tr.cfg k) (tr.cfg (k + 1)) → (tr.cfg (k + 1)).mem = (tr.cfg k).mem) :
    ∀ j ts w, (tr.cfg j).mem.get? ts = some w → w.loc = topL t → w.val = BitVec.setWidth 128 n := by
  intro j
  induction j with
  | zero => intro ts w hw; rw [hm0] at hw; cases hw
  | succ j ih =>
    intro ts w hw hl
    rcases tr.step j with ⟨k, hk⟩ | ⟨-, he⟩
    · obtain ⟨u, hu⟩ := TreiberPp.stepSem_get hk
      have hk2 := lt2 hT hD hN htn tr hI0 hu
      by_cases e : k = 1
      · subst e; rw [hna j hk] at hw; exact ih ts w hw hl
      obtain rfl : k = 0 := by omega
      rcases hk with ⟨u', outs, o, hu', hs, ho, -, he⟩ | ⟨u', w', hu', -, -, he⟩ <;> rw [hu] at hu' <;> cases hu'
      · have hw : o.mem.get? ts = some w := by rw [he] at hw; exact hw
        rcases (stepAt hT hD hN htn tr hI0 hu hs ho).eff with ⟨hm, -, -⟩ | ⟨w', hw', -, hq⟩
        · exact ih ts w (hm ▸ hw) hl
        · rcases hw' with ⟨hm, -⟩ | ⟨-, -, -, hm, -⟩
          · rw [hm] at hw
            rcases Memory.get?_append_eq_some _ _ hw with ⟨-, hw⟩ | ⟨-, rfl⟩
            · exact ih ts w hw hl
            · simp only [Q, ↓reduceIte] at hq; exact hq hl
          · exact ih ts w (hm ▸ hw) hl
      · have hm : (tr.cfg (j + 1)).mem = ((tr.cfg j).mem.append w').1 := by rw [he]; rfl
        rw [hm] at hw
        rcases Memory.get?_append_eq_some _ _ hw with ⟨-, hw⟩ | ⟨rfl, rfl⟩
        · exact ih ts w hw hl
        · have hu1 : (tr.cfg (j + 1)).threads[0]? = some (promThread u (tr.cfg j).mem w) := by
            rw [he]; exact withThread_get_self hu
          have := ((inv_at hT hD hN htn tr hI0 (j + 1)).thr 0 _ hu1).good ((tr.cfg j).mem.last + 1)
            (by simp [Memory.append, Memory.last]) w (by rw [hm]; exact Memory.get?_append_last _ _)
          simp only [Q, ↓reduceIte] at this; exact this hl
    · rw [he] at hw; exact ih ts w hw hl

/-- **Spin(popper)**, value part: `top` is eventually `0`, else the popper
would catch up with it and succeed. -/
theorem spin1b (hm0 : ∀ ts, (tr.cfg 0).mem.get? ts = none) (hz : (tr.cfg 0).mem.initVal (topL t) = 0)
    (hn : n ≠ 0) (hmf : MemFair Arch.armv8 tr.cfg)
    (hna : ∀ k, StepSem Arch.armv8 fuel 1 (tr.cfg k) (tr.cfg (k + 1)) → (tr.cfg (k + 1)).mem = (tr.cfg k).mem)
    (hinf : InfOften fun k => InstrSem Arch.armv8 fuel 1 (tr.cfg k) (tr.cfg (k + 1))) :
    ∃ m, ∀ j, m ≤ j → (tr.cfg j).mem.finalVal (topL t) = 0 := by
  obtain ⟨m, -, hc⟩ := TreiberPp.top_const tr (topL t) (i := 0) fun j _ => cnt_bound hT hD hN htn tr hI0 j
  refine ⟨m, fun j hj => ?_⟩
  rw [(hc j hj).2]
  apply Classical.byContradiction; intro hF
  have hF' : BitVec.setWidth 64 ((tr.cfg m).mem.finalVal (topL t)) ≠ 0 := by
    revert hF
    refine fv_msg (P := fun v => ¬ v = 0 → BitVec.setWidth 64 v ≠ 0) (fun _ h => ?_) fun ts w hw hl _ => ?_
    · rw [(tr.prefix_le (Nat.zero_le m)).initVal, hz] at h; exact absurd rfl h
    · rw [topVals hT hD hN htn tr hI0 hm0 hna m ts w hw hl, sz64]; exact hn
  obtain ⟨u1, hu1⟩ := get_thr hT hD hN htn tr hI0 m (by decide : 1 < 2)
  exact memFair_lastWrite_false hmf (reads_inf hT hD hN htn tr hI0 hinf (by decide)) hu1 fun j hj u hu hL =>
    catchup hT hD hN htn tr hI0 hinf (by decide) hc (fun _ => hF') hj hu hL

/-- **A finished pusher left `top = n ≠ 0`**, if the popper never changed
memory. -/
theorem pushed (hm0 : ∀ ts, (tr.cfg 0).mem.get? ts = none) (hn : n ≠ 0) {j : Nat} (hd : Done 0 (tr.cfg j))
    (hna : ∀ k, StepSem Arch.armv8 fuel 1 (tr.cfg k) (tr.cfg (k + 1)) → (tr.cfg (k + 1)).mem = (tr.cfg k).mem) :
    (tr.cfg j).mem.finalVal (topL t) ≠ 0 := by
  obtain ⟨u, hu, hpc⟩ := hd
  have hp := pos_end hT hD hN htn tr hI0 hu hpc
  have hS1 : 1 ≤ S u := by show 1 ≤ sOf (pos u) u.st.st.1; rw [hp]; simp [endP, sOf]
  obtain ⟨ts, w, hw, hl, -⟩ := (inv_at hT hD hN htn tr hI0 j).topN u hu hS1
  have hne : BitVec.setWidth 128 n ≠ 0 := fun e => hn (by rw [← sz64 n, e]; rfl)
  refine fv_msg (P := (· ≠ 0)) (fun e => ?_) fun ts' w' hw' hl' => by
    rw [topVals hT hD hN htn tr hI0 hm0 hna j ts' w' hw' hl']; exact hne
  have : ts ≤ (tr.cfg j).mem.lastWrite w.loc :=
    Nat.le_of_not_lt fun h => (tr.cfg j).mem.not_write_of_lastWrite_lt w.loc h hw rfl
  rw [hl, e] at this
  obtain rfl : ts = 0 := Nat.le_zero.mp this
  rw [Memory.get?_zero] at hw; cases hw

/-- **The skeleton's interface** for a trace from the start states. -/
theorem iface (h0 : ∀ (k : Nat) (u : Thread isa), (tr.cfg 0).threads[k]? = some u → u.prom = [])
    (hm0 : ∀ ts, (tr.cfg 0).mem.get? ts = none) (hz : (tr.cfg 0).mem.initVal (topL t) = 0) (hn : n ≠ 0)
    (hmf : MemFair Arch.armv8 tr.cfg) (hok : ∀ j, OkStepsPF Arch.armv8 (tr.cfg j)) :
    TreiberPp.Iface tr Done (topL t) where
  size j := (inv_at hT hD hN htn tr hI0 j).size
  done_mono _ _ _ h hd := done_mono hT hD hN htn tr hI0 h hd
  done_nostep _ _ hd := nostep hT hD hN htn tr hI0 hd
  notdone_nonfinal _ j hk hd :=
    let ⟨_, hu⟩ := get_thr hT hD hN htn tr hI0 j hk
    final_false hu (running hT hD hN htn tr hI0 hu hd)
  notdone_running _ _ hu hd := running hT hD hN htn tr hI0 hu hd
  drop := ⟨1, fun i tid u hu =>
    have h := (inv_at hT hD hN htn tr hI0 i).thr tid u hu
    dropBounded hT hD hN htn h.st h.pc⟩
  ok := hok
  init0 u hu := h0 0 u hu
  spin0 _ _ hinf := spin0 hT hD hN htn tr hI0 hmf hinf
  spin1 _ _ hinf := have hna := pop_noApp hT hD hN htn tr hI0 h0 hmf hinf
    ⟨hna, spin1b hT hD hN htn tr hI0 hm0 hz hn hmf hna hinf⟩
  pushed _ hd hna := pushed hT hD hN htn tr hI0 hm0 hn hd hna

end Trace

/-- **Liveness from the start states, given `OkStepsPF` on the reachable
configurations** (any declarations agreeing on `top`, the node's data and
`next` words). -/
theorem treiber_pp_live_gen {ds : Decls} {t n : BitVec 64} (hT : ds.AgreesAt t 8) (hD : ds.AgreesAt n 4)
    (hN : ds.AgreesAt (n + 8#64) 8) (htn : t ≠ n + 8#64) (hn : n ≠ 0) {fuel : Nat} {sP sQ : isa.State}
    {initMem : List (Loc × Val)} (hP : StartPushWD ds t n sP) (hQ : StartPopWD ds t sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal (topL t) = 0)
    (hok : ∀ c, Live.Bridge.ReachableSem Arch.armv8 fuel (Config.init [sP, sQ] initMem) c → OkStepsPF Arch.armv8 c) :
    LiveFromSem Arch.armv8 fuel (Config.init [sP, sQ] initMem)
      (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg) (fun tid _ => tid < 2) Done := by
  intro tr h0 ⟨hwf, hmf⟩ tid i htid
  have hI0 : Inv ds t n fuel (tr.cfg 0) := h0 ▸ Inv.init (start0 hP).1 (start0 hP).2 (start1 (n := n) hQ).1 (start1 (n := n) hQ).2
  refine TreiberPp.skeleton tr Done (topL t) (iface hT hD hN htn tr hI0 (fun k u hu => Config.init_prom (h0 ▸ hu))
    (fun ts => by rw [h0]; simp [Config.init, Memory.get?]) (h0 ▸ hT0) hn hmf
    fun j => hok _ (h0 ▸ reach tr j)) hwf tid htid i

/-- **Liveness of `treiber_pp.kl` for AArch64 on the semantic machine**:
from the start configuration of `treiber_pp_envG_whole` (any layout, any
fuel, a node `n ≠ 0`), on every weakly fair and memory fair semantic trace
(promises included), the pusher and the popper both reach their end
addresses. -/
theorem treiber_pp_live_sem {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l treiberImageA)]
    (t n : BitVec 64) (htn : t ≠ n + 8) (hn : n ≠ 0) {sP sQ : isa.State} {initMem : List (Loc × Val)}
    (hP : StartPushW (layout := l) t n sP) (hQ : StartPopW (layout := l) t sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    LiveFromSem Arch.armv8 fuel (Config.init [sP, sQ] initMem)
      (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg) (fun tid _ => tid < 2) Done := by
  have hP' : StartPushWD (layout := l) {} t n sP := ⟨hP.exe, hP.decls, hP.pc, hP.endPc, hP.x0, hP.x1, hP.x9, hP.dt,
    hP.dd, hP.dn⟩
  have hQ' : StartPopWD (layout := l) {} t sQ := ⟨hQ.exe, hQ.decls, hQ.pc, hQ.endPc, hQ.x0, hQ.dt, hQ.d4⟩
  have hE := fun a k => Decls.agreesAt_empty a k
  refine treiber_pp_live_gen (layout := l) (hE _ _) (hE _ _) (hE _ _) htn hn hP' hQ' hT0 fun c hr => ?_
  refine okSteps_empty (layout := l) (Live.NoStuck.reachableSem_inv (Inv {} t n fuel) (fun _ c _ h hs => ?_) hr
    (Inv.init (start0 hP').1 (start0 hP').2 (start1 (n := n) hQ').1 (start1 (n := n) hQ').2))
  obtain ⟨u, hu⟩ := TreiberPp.stepSem_get hs
  exact h.step (hE _ _) (hE _ _) (hE _ _) htn hu hs

section
open Kraken.Promising.SLR.EnvG.Treiber Kraken.Promising.SLR.EnvG.ConcreteTreiber

/-- **`treiber_pp.kl` is live on the runner's configuration**:
`treiber_pp_live_sem` at `[pusherW0, popperW1]`, `wLayoutT`, `treiberInitMem`. -/
theorem treiber_pp_live_sem_concrete (fuel : Nat) :
    LiveFromSem Arch.armv8 fuel (Config.init [pusherW0, popperW1] treiberInitMem)
      (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg) (fun tid _ => tid < 2) Done :=
  treiber_pp_live_sem wLayoutT topAddr n1Addr (by decide) (by decide) pusherW0_start popperW1_start
    (by simp only [Config.init]; decide)

end

end Kraken.Promising.Live.TreiberPpA64

#print axioms Kraken.Promising.Live.TreiberPpA64.treiber_pp_live_sem
#print axioms Kraken.Promising.Live.TreiberPpA64.treiber_pp_live_sem_concrete
