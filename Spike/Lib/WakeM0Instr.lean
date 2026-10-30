/-
**main's instruction steps that keep memory and promises** (`post_step0`). The thread-0 counterpart of
`Spike/Lib/WakeW1Instr.lean`.

- `stepOne_getCoh_mono`: one instruction raises no coherence view
  (ISA-generic; every rule's views are a `setCoh` of the old or keep its
  coherence), so main's `PreC` is kept (`PreC.mono`).
- `post_instrKeep0`: an instruction step of main keeping memory and
  promises, its new state with a local run of main's source in `Mi`, keeps
  `Post` (`post_keep0`; the bound and cover by the step lemmas, `PreC` by
  `stepOne_getCoh_mono`, no promise at a no-promise state by certification,
  `WCompat0.noProm0`).
- `post_silent0`, `post_choice0`, `post_fnc0`, `post_rtLoad0`: main's rows
  that keep memory and promises.
-/
import Spike.Lib.WakeM0Keep
import Spike.Lib.WakeW1Instr

namespace Spike.Lib.WakeM0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt Spike.Lib.WakeW1

/-! ## Coherence views only grow -/

section Mono

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **A run of an instruction's event tree raises no coherence view.** -/
theorem runTree_getCoh_mono {σ : Type} (tree : EvTree σ) :
    ∀ (c : Kraken.Promising.Ctx) (s : σ) (c' : Kraken.Promising.Ctx), .ok (s, c') ∈ runTree A tid iv c tree →
      ∀ l, c.views.getCoh l ≤ c'.views.getCoh l :=
  runTree_preserves A tid iv (fun c c' => ∀ l, c.views.getCoh l ≤ c'.views.getCoh l)
    (fun _ _ => Nat.le_refl _)
    (fun _ _ _ h₁ h₂ l => Nat.le_trans (h₁ l) (h₂ l))
    (fun c _ _ _ _ x hx l => by
      obtain ⟨v, -, -, h⟩ := readSuccs_shape A iv hx
      rw [h]; exact getCoh_le_setCoh _ _ _ _)
    (fun c iv' _ _ _ _ _ _ _ c' h l => by
      rcases (Lower.mem_writeSuccs_iff A tid iv').mp h with ⟨t, -, -, -, rfl⟩ | ⟨-, rfl⟩
      · exact getCoh_le_setCoh _ _ _ _
      · exact getCoh_le_setCoh _ _ _ _)
    (fun c k l => by cases k <;> exact Nat.le_refl _)
    (fun _ _ _ => Nat.le_refl _)
    (fun c k noRet l' l => by unfold rmwPost; split <;> exact Nat.le_refl _)
    tree

/-- **One instruction raises no coherence view.** -/
theorem stepOne_getCoh_mono {I : ISA} {t : Thread I} {mem : Memory}
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) : ∀ l, t.views.getCoh l ≤ o.thread.views.getCoh l := by
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, c'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have hc' := runTree_getCoh_mono A tid _ tree _ st c' hr
      obtain ⟨-, e2⟩ := finishInstr_relKey hth
      have e3 : th.views.coh = c'.views.coh := by have := congrArg Views.coh e2; exact this
      intro l
      have := hc' l
      unfold Views.getCoh at this ⊢
      rw [e3]; exact this

/-- A load keeps memory and promises (`WakeW1.stepOne_load_keep` at any
thread). -/
theorem stepOne_load_keep' {t : Thread isaLSE2} {mem : Memory} {kl : Kraken.LoadKind} {xcl : Bool} {L : Loc}
    {g : Val → isaLSE2.State} (hex : isaLSE2.exec t.st = some (.load kl xcl L fun v => .done (g v)))
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
    (hso : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok o ∈ outs) :
    o.mem = mem ∧ o.thread.prom = t.prom := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff Arch.armv8 tid hex).mp ⟨outs, o, hso, ho, rfl, rfl⟩
  rw [Lower.run_load_iff] at hr
  obtain ⟨ts1, v, hx, rfl⟩ := hr
  have hmem : c'.mem = mem := by
    obtain ⟨-, -, -, he⟩ := readSuccs_shape Arch.armv8 _ hx
    exact congrArg Ctx.mem he
  exact ⟨hm.trans hmem, (finishInstr_relKey hth).1.trans (readSuccs_prom Arch.armv8 _ hx)⟩

end Mono

/-! ## Steps keeping memory and promises -/

variable {Q : WakeRel} {D : WSide Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **An instruction step of main keeping memory and promises keeps
`Post`**, its new state with main's source's local run in `Mi`. -/
theorem post_instrKeep0 (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = WakeKR.KR r0 r1) (hown : Q.own = WakeOwn.wakeOwn)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
    (hso : stepOne Arch.armv8 t0 0 t.1.mem = some outs) (ho : .ok o ∈ outs)
    (hco : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 0) 0 o.thread o.mem)
    (hm : o.mem = t.1.mem) (hp : o.thread.prom = t0.prom) {c' : Ctl}
    (hr : LocalRun wakeSrc (Ctl.of s0) c') (hmi : M.Mi w o.thread.st c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  have hb := (stepOne_bnd _ hso ho h.core.bnd0).1
  have hcov := stepOne_cohL _ hso ho h.core.cov0
  have hpre := h.preC.mono (stepOne_getCoh_mono _ _ hso ho _)
  rw [hm] at hb hcov ⊢
  exact post_keep0 hC hC0 hPT0 hKR hown h hp hb hcov (fun hn => hC0.noProm0 w _ _ _ hn hco) hpre hr hmi

section Rows

variable (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
  (hKR : Q.KR = WakeKR.KR r0 r1) (hown : Q.own = WakeOwn.wakeOwn)
  (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
  {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
  (hso : stepOne Arch.armv8 t0 0 t.1.mem = some outs) (ho : .ok o ∈ outs)
  (hco : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 0) 0 o.thread o.mem)
include hC hC0 hPT0 hKR hown h hso ho hco

/-- **main's silent row keeps `Post`.** -/
theorem post_silent0 {s' : isaLSE2.State} {c' : Ctl} (he : isaLSE2.exec t0.st = some (.done s'))
    (hr : LocalRun wakeSrc (Ctl.of s0) c') (hX : M.Mi w s' c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  obtain ⟨st, hP, hth, hm⟩ := Lower.stepOne_silent_ok Arch.armv8 0 he (Lower.silentTree_done s')
    ⟨outs, o, hso, ho, rfl, rfl⟩
  exact post_instrKeep0 hC hC0 hPT0 hKR hown h hso ho hco hm (finishInstr_relKey hth).1 hr
    ((finishInstr_st hth) ▸ hP ▸ hX)

/-- **main's choice row keeps `Post`.** -/
theorem post_choice0 {P : isaLSE2.State → Prop} {tree : EvTree isaLSE2.State}
    (he : isaLSE2.exec t0.st = some tree) (hs : Lower.SilentTree P tree)
    (hX : ∀ s', P s' → ∃ c', LocalRun wakeSrc (Ctl.of s0) c' ∧ M.Mi w s' c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  obtain ⟨st, hP, hth, hm⟩ := Lower.stepOne_silent_ok Arch.armv8 0 he hs ⟨outs, o, hso, ho, rfl, rfl⟩
  obtain ⟨c', hr, hX'⟩ := hX _ ((finishInstr_st hth) ▸ hP)
  exact post_instrKeep0 hC hC0 hPT0 hKR hown h hso ho hco hm (finishInstr_relKey hth).1 hr hX'

/-- **main's fence row keeps `Post`.** -/
theorem post_fnc0 {k : Kraken.FenceKind} {s' : isaLSE2.State} {c' : Ctl}
    (he : isaLSE2.exec t0.st = some (.fence k fun _ => .done s'))
    (hr : LocalRun wakeSrc (Ctl.of s0) c') (hX : M.Mi w s' c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  obtain ⟨hst, hm, hp⟩ := stepOne_fence_eq Arch.armv8 he hso ho
  exact post_instrKeep0 hC hC0 hPT0 hKR hown h hso ho hco hm hp hr (hst ▸ hX)

/-- **main's runtime-load row keeps `Post`**: the value read is a `G` value
(the memory's invariant); main owns no word (`WCompat0.own0`). -/
theorem post_rtLoad0 {kl : Kraken.LoadKind} {L : Loc} {g : Val → isaLSE2.State} {c' : Ctl}
    (he : isaLSE2.exec t0.st = some (.load kl false L fun v => .done (g v)))
    (hr : LocalRun wakeSrc (Ctl.of s0) c')
    (hX : ∀ v, (M.ms w).G L v → (∀ u, (L, u) ∈ (M.ms w).own t0.st → v = u) → M.Mi w (g v) c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  obtain ⟨hm, hp⟩ := stepOne_load_keep' 0 he hso ho
  rw [hC0.G0 w] at hX
  simp only [hC0.own0 w, List.not_mem_nil, false_implies, implies_true, true_implies] at hX
  obtain ⟨v, hst, hG⟩ := stepOne_load_msgsExcept he hso ho (Scc.Sem.MemInv.msgsExcept h.core.memInv _)
    h.core.memInv.1
  exact post_instrKeep0 hC hC0 hPT0 hKR hown h hso ho hco hm hp hr (hst ▸ hX v hG)

end Rows

/-- info: 'Spike.Lib.WakeM0.post_rtLoad0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_rtLoad0

end Spike.Lib.WakeM0
