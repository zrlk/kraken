/-
**The worker's steps that keep memory and promises** (data in `Spike/Lib/WakeW1.lean`, `Spike/Lib/WakeW1Compat.lean`).

- `Parts`: `Post` unpacked at a ghost record `w`, with the protocol's `oc`;
  `post_parts`: `Post` gives it.
- `Parts.src_prom`: a source promise of the worker is the flag's message
  `kc` of the protocol; `Parts.past_noProm`: past its store the source
  worker has no promise.
- `localStep_pre`, `localRun_pass`: a local run of the source worker stays
  before its store point (or does not move).
- `Parts.certified_set`: the source worker, after a local run, is
  certified (no promise, or its promise `kc` fulfilled by its store,
  `certified_pre`).
- `post_keep`: a worker step replacing thread 1 by a thread with the same
  promises, memory and kernel state kept, matched by a local run of the
  source worker into `Wi`, keeps `Post` (a silent row, a choice, a runtime
  load, a fence, a system call's return).
-/
import Spike.Lib.WakeW1Frame
import Spike.Lib.WakeW1Src
import Spike.Lib.WakeW1Core
import Spike.Lib.Inv2CohL

namespace Spike.Lib.WakeW1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc Spike.Lib.WorkerSrcStep
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt

/-! ## `Post`, unpacked -/

/-- **`Post` unpacked** at the ghost record `w`: the two threads on each
side, the core, main's `PreC` and `PT0`, the worker's `PT1`, the protocol
`CProt` at `oc`, the kernel relation. -/
structure Parts (Q : WakeRel) (D : WSide Q.ι) (Λ : Scc.Sem.Layout) (w : Q.ι) (t : Cfg) (s : TermRun.Cfg)
    (t0 t1 : Thread isaLSE2) (s0 s1 : TermRun.TTh) (ts : Nat → Option Nat) (tp sp : List Nat)
    (oc : Option (Nat × Nat)) : Prop where
  th : t.1.threads = #[t0, t1]
  ths : s.ths = #[s0, s1]
  core : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
    (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1.st s1.stack) t.1.mem t0 t1 s.mem s0 s1 ts
    tp sp
  preC : PreC (Q.SR w) (Q.C w).cT t.1.mem t0.views
  pt0 : Q.PT0 w t.1.mem s.mem t0 s0
  pt1 : PT1 D w t.1.mem s.mem t1 s1
  prot : CProt (Q.SR w) (Q.C w) oc t.1.mem t1 s.mem s1 ts tp sp
  kr : Q.KR w t s

variable {Q : WakeRel} {D : WSide Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}

/-- **`Post` unpacks.** -/
theorem post_parts (hC : WCompat Q D μ Λ arch) {t : Cfg} {s : TermRun.Cfg} (h : Q.Post Λ t s) :
    ∃ w t0 t1 s0 s1 ts tp sp oc, Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc := by
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hth, hs, hcore, hp0, hp1, oc, hprot⟩, hkr⟩ := h
  simp only [WakeRel.PTw, ite_true] at hp0
  simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, hC.pt1] at hp1
  exact ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, hth, hs, hcore, hp0.1, hp0.2, hp1, hprot, hkr⟩

namespace Parts

variable {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

theorem s1_get (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) : s.ths[1]? = some s1 := by
  rw [h.ths]; rfl

theorem t1_get (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) : t.1.threads[1]? = some t1 := by
  rw [h.th]; rfl

/-- The worker's control invariant at its source thread. -/
theorem wCtl (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) : WCtl (D.cw w) (Ctl.of s1) :=
  ⟨rfl, h.pt1.2.2.2.1, h.pt1.2.2.2.2.1, h.pt1.2.2.2.2.2.1⟩

/-- **A source promise of the worker is the protocol's `kc`**, a message
to `cS`. -/
theorem src_prom (hC : WCompat Q D μ Λ arch) (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) {k : Nat}
    (hk : k ∈ s1.promises) : ∃ Tc, oc = some (Tc, k) := by
  obtain ⟨hS, m, hm, hl⟩ := h.pt1.2.2.2.2.2.2.2.1 k hk
  rw [hC.cwv w] at hl
  injection hl with hl1
  rw [hC.S w] at hS
  exact h.prot.smsg k m hm hS (by first | exact hl1 | exact hl1.symm)

/-- `helloC`'s store point is `WPass`. -/
theorem passS_iff (hC : WCompat Q D μ Λ arch) (th : TermRun.TTh) : (Q.C w).passS th ↔ WPass th := by
  rw [hC.C w]; rfl

/-- **Past its store the source worker has no promise**: its promise would
be `kc`, mirrored (`prom_corr`), but past the store `Tc` is not mirrored. -/
theorem past_noProm (hC : WCompat Q D μ Λ arch) (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hpast : s1.term = wkUnpark ∨ s1.term = .ret .unit) : s1.promises = [] := by
  cases hp : s1.promises with
  | nil => rfl
  | cons k ks =>
    have hk : k ∈ s1.promises := by rw [hp]; exact List.mem_cons_self
    obtain ⟨Tc, rfl⟩ := h.src_prom hC hk
    have hpS : (Q.C w).passS s1 := (passS_iff (w := w) hC s1).mpr ⟨h.pt1.2.1, hpast⟩
    obtain ⟨Tc', kc', hoc, hn⟩ := h.prot.pass_done (h.prot.pass_iff.mpr hpS)
    simp only [Option.some.injEq, Prod.mk.injEq] at hoc
    obtain ⟨rfl, rfl⟩ := hoc
    obtain ⟨hT, -, hts, -, -⟩ := h.prot.some_msg Tc k rfl
    have := (h.core.mem.prom_corr k Tc hts (by omega)).mp ((h.core.sp_prom k).mpr (.inr hk))
    exact absurd this hn

end Parts

/-! ## Local runs of the source worker -/

/-- **A local step of the source worker is before its store point**, from
and to. -/
theorem localStep_pre {cw : TermRun.Word} {cS : WeakMem.Address} (hcw : cw.val = .loc cS 0) {c c' : Ctl}
    (h : LocalStep wakeSrc c c') (hc : WCtl cw c) :
    (c.term ≠ wkUnpark ∧ c.term ≠ .ret .unit) ∧ (c'.term ≠ wkUnpark ∧ c'.term ≠ .ret .unit) := by
  rcases hc.term with ht | ht | ht | ht | ht
  · obtain ⟨-, -, e1, -⟩ := localStep_wkTail h ht (hc.body (.inl ht))
    rw [ht, e1]; simp [wkTail, wkBody, wkUnpark]
  · obtain ⟨e1, -⟩ := localStep_wkBody h ht (hc.body (.inr ht))
    rw [ht, e1]; simp [wkBody, wkStore, wkUnpark]
  · have hn : ¬ PreSplit c.term := by
      rw [ht]; rintro (hp | hp) <;> simp [wkStore, wkTail, wkBody] at hp
    exact (localStep_wkStore_false h ht (hc.cj hn) hcw).elim
  · exact (localStep_wkUnpark_false h ht).elim
  · exact (localStep_not_ret h .unit ht).elim

/-- **A local run of the source worker keeps its side of the store point.** -/
theorem localRun_pass {cw : TermRun.Word} {cS : WeakMem.Address} (hcw : cw.val = .loc cS 0) {c c' : Ctl}
    (h : LocalRun wakeSrc c c') (hc : WCtl cw c) :
    (c'.term = wkUnpark ∨ c'.term = .ret .unit) ↔ (c.term = wkUnpark ∨ c.term = .ret .unit) := by
  induction h with
  | refl => exact Iff.rfl
  | @step c₀ c₁ c₂ hs hr ih =>
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := localStep_pre hcw hs hc
    rw [ih (localStep_wCtl hcw hs hc)]
    exact ⟨fun h => h.elim (absurd · h3) (absurd · h4), fun h => h.elim (absurd · h1) (absurd · h2)⟩

namespace Parts

variable {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **The source worker after a local run is certified**: with no promise
trivially; with its promise `kc` (before its store point, `past_noProm`),
by its run to the store and the fulfilment (`certified_pre`; G1–G3 from
`CProtS`, `fulfil_ok`). -/
theorem certified_set (hC : WCompat Q D μ Λ arch) (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) {c' : Ctl}
    (hr : LocalRun wakeSrc (Ctl.of s1) c') :
    TermRun.Certified wakeSrc Promises.Knobs.all arch
      { s with ths := s.ths.set! 1 { s1 with term := c'.term, env := c'.env } } 1 := by
  have hi := h.s1_get
  have hcw := hC.cwv w
  have hctl' := localRun_wCtl hcw hr h.wCtl
  let s1' : TermRun.TTh := { s1 with term := c'.term, env := c'.env }
  have hi' : ({ s with ths := s.ths.set! 1 s1' } : TermRun.Cfg).ths[1]? = some s1' := getElem?_set!_self hi s1'
  obtain hp | ⟨k, ks, hp⟩ : s1.promises = [] ∨ ∃ k ks, s1.promises = k :: ks := by
    cases s1.promises <;> simp
  · exact certified_nil hi' (by simp [s1', hp])
  · have hk : k ∈ s1.promises := by rw [hp]; exact List.mem_cons_self
    have hks : ks = [] := by
      have := h.pt1.2.2.2.2.2.2.1; rw [hp] at this; simpa using this
    subst hks
    obtain ⟨Tc, rfl⟩ := h.src_prom hC hk
    have hnp : ¬ (s1.term = wkUnpark ∨ s1.term = .ret .unit) := fun hpast => by
      rw [h.past_noProm hC hpast] at hp; cases hp
    have hnpS : ¬ (Q.C w).passS s1 := fun hps => hnp ((passS_iff (w := w) hC s1).mp hps).2
    have hS := ((cProt_iff _ _ _).mp h.prot).2.1
    obtain ⟨-, m, hm, hml, hmv⟩ := hS.some_msg Tc k rfl
    obtain ⟨hmv', hob⟩ := fulfil_ok hS hnpS ((h.core.sp_prom k).mpr (.inr hk)) hm
    rw [hC.C w] at hmv' hob
    have hpre : c'.term ≠ wkUnpark ∧ c'.term ≠ .ret .unit := by
      have := (not_congr (localRun_pass hcw hr h.wCtl)).mpr hnp
      exact ⟨fun e => this (.inl e), fun e => this (.inr e)⟩
    have hm' : ({ s with ths := s.ths.set! 1 s1' } : TermRun.Cfg).mem[k]? = some ⟨(Q.C w).cS, .num 1, m.view⟩ := by
      show s.mem[k]? = _
      rw [hm, ← hml, ← hmv]
    have hc'eq : Ctl.of s1' = c' := by
      obtain ⟨tm, en, hd⟩ := c'
      have : hd = none := hctl'.hold
      subst this; rfl
    exact certified_pre (k := Promises.Knobs.all) hi' (by rw [hc'eq]; exact hctl') hpre h.pt1.2.1 h.pt1.2.2.1 hcw
      (by simp [s1', hp]) hm' hmv' hob

end Parts

/-! ## Steps keeping memory and promises -/

/-- **A worker step keeping memory, promises and the kernel state, matched
by a local run of the source worker, keeps `Post`**: thread 1 replaced by
`t1'` (same promises, its bound, cover, owned words and no-promise fact at
the memory), the source worker after a local run from its control to `c'`
with `Wi w t1'.st c'`. -/
theorem post_keep (hC : WCompat Q D μ Λ arch) {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2}
    {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hex : SrcSem.mainExit s = [])
    {t1' : Thread isaLSE2} {c' : Ctl} (hp : t1'.prom = t1.prom) (hb : t1'.Bnd t.1.mem.last)
    (hcov : CohCoversL t1'.views t1'.prom t.1.mem ((Q.P w).cov 1))
    (hown : ExtRows.OwnOk (Q.own w 1 t1'.st []) t.1.mem t1'.prom)
    (hnp : (Q.P w).noProm t1'.st → t1'.prom = [])
    (hr : LocalRun wakeSrc (Ctl.of s1) c') (hwi : D.Wi w t1'.st c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 t1' t.1.mem, t.2) s' := by
  have hi := h.s1_get
  have hcw := hC.cwv w
  have hctl' := localRun_wCtl hcw hr h.wCtl
  let s1' : TermRun.TTh := { s1 with term := c'.term, env := c'.env }
  have hc'eq : Ctl.of s1' = c' := by
    obtain ⟨tm, en, hd⟩ := c'
    have : hd = none := hctl'.hold
    subst this; rfl
  have hrun : (wakeS arch).Run s [] { s with ths := s.ths.set! 1 s1' } :=
    localRunS_run_source_i (P := srcPo 2 arch wakeSrc) rfl (by decide) hr.toS hi rfl rfl h.pt1.2.2.1 hex
      (h.certified_set hC hr)
  have hs' : ({ s with ths := s.ths.set! 1 s1' } : TermRun.Cfg).ths = #[s0, s1'] := by
    show s.ths.set! 1 s1' = _
    rw [h.ths]; rfl
  have hpass := localRun_pass hcw hr h.wCtl
  have hpT : ∀ (st : isaLSE2.State) (c : Ctl), D.Wi w st c →
      ((Q.C w).passT st ↔ (c.term = wkUnpark ∨ c.term = .ret .unit)) := hC.pass w
  have hpT' : (Q.C w).passT t1'.st ↔ (Q.C w).passT t1.st := by
    rw [hpT _ _ hwi, hpT _ _ h.pt1.1, hpass]
  refine ⟨_, hrun, post_frame (ts' := ts) (tp' := tp) (sp' := sp) hC h.th h.ths hs' h.preC h.pt0 h.kr h.core.T_le ⟨.inl rfl, .inl rfl⟩ ?_ ?_ ?_ rfl⟩
  · refine core1_same h.core (by simp) hp rfl hb hcov h.core.scov1 ?_ ?_ ?_ hnp
    · simp only [Nat.one_ne_zero, ite_false]
      rw [show s1'.stack = [] from h.pt1.2.1]; exact hown
    · intro L v v' h0 h1
      simp only [ite_true] at h0
      simp only [Nat.one_ne_zero, ite_false] at h1
      rw [show s1'.stack = [] from h.pt1.2.1] at h1
      exact hC.ownDisj w _ _ _ L v v' h0 h1
    · intro L v h1
      simp only [Nat.one_ne_zero, ite_false] at h1
      rw [show s1'.stack = [] from h.pt1.2.1] at h1
      exact hC.ownCov w _ L v h1
  · refine ⟨hc'eq ▸ hwi, h.pt1.2.1, h.pt1.2.2.1, hctl'.term, hctl'.body, hctl'.cj, h.pt1.2.2.2.2.2.2.1,
      h.pt1.2.2.2.2.2.2.2.1, hp ▸ h.pt1.2.2.2.2.2.2.2.2⟩
  · obtain ⟨hT, hS, hl⟩ := (cProt_iff _ _ _).mp h.prot
    refine ⟨oc, (cProt_iff _ _ _).mpr ⟨⟨hT.tmsg, hT.some_msg, fun Tc kc hoc htp => hp ▸ hT.prom_worker Tc kc hoc htp,
      fun hq => hT.pass_done (hpT'.mp hq), fun hq => hT.pass_prom (fun h' => hq (hpT'.mpr h'))⟩,
      cProtS_vs hS (by rw [hC.C w]; exact ⟨rfl, rfl⟩) rfl ?_, ?_⟩⟩
    · intro hn h'
      exact hn ((Parts.passS_iff hC s1').mpr ⟨h.pt1.2.1, hpass.mpr ((Parts.passS_iff hC s1).mp h').2⟩)
    · rw [Parts.passS_iff hC s1', hpT _ _ hwi]
      exact ⟨fun h' => ⟨h.pt1.2.1, h'⟩, fun h' => h'.2⟩

/-- info: 'Spike.Lib.WakeW1.post_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_keep

end Spike.Lib.WakeW1
