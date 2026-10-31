/-
**main's instruction steps that keep memory and promises** (hello plan
1.6, `post_step0`). The thread-0 counterpart of
`Spike/Lib/X64WakeW1Instr.lean`.

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

x86-64 twin of `Spike/Lib/WakeM0Instr.lean` (same names, namespaces with the
`X64` prefix).
-/
import Spike.Lib.X64WakeM0Keep
import Spike.Lib.X64WakeW1Instr

namespace Spike.Lib.X64WakeM0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt Spike.Lib.X64WakeW1

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

/-- A load keeps memory and promises (`X64WakeW1.stepOne_load_keep` at any
thread). -/
theorem stepOne_load_keep' {t : Thread isa} {mem : Memory} {kl : Kraken.LoadKind} {xcl : Bool} {L : Loc}
    {g : Val → isa.State} (hex : isa.exec t.st = some (.load kl xcl L fun v => .done (g v)))
    {outs : List (Except String (Outcome isa))} {o : Outcome isa}
    (hso : stepOne Arch.tso t tid mem = some outs) (ho : .ok o ∈ outs) :
    o.mem = mem ∧ o.thread.prom = t.prom := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff Arch.tso tid hex).mp ⟨outs, o, hso, ho, rfl, rfl⟩
  rw [Lower.run_load_iff] at hr
  obtain ⟨ts1, v, hx, rfl⟩ := hr
  have hmem : c'.mem = mem := by
    obtain ⟨-, -, -, he⟩ := readSuccs_shape Arch.tso _ hx
    exact congrArg Ctx.mem he
  exact ⟨hm.trans hmem, (finishInstr_relKey hth).1.trans (readSuccs_prom Arch.tso _ hx)⟩

end Mono

/-! ## Steps keeping memory and promises -/

variable {Q : WakeRel} {D : WSide Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isa} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **An instruction step of main keeping memory and promises keeps
`Post`**, its new state with main's source's local run in `Mi`. -/
theorem post_instrKeep0 (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = X64WakeKR.KR r0 r1)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    {outs : List (Except String (Outcome isa))} {o : Outcome isa}
    (hso : stepOne Arch.tso t0 0 t.1.mem = some outs) (ho : .ok o ∈ outs)
    (hco : CertOkC Arch.tso (certSem abi Arch.tso μ t.2 0) 0 o.thread o.mem)
    (hm : o.mem = t.1.mem) (hp : o.thread.prom = t0.prom) {c' : Ctl}
    (hr : LocalRun wakeSrc (Ctl.of s0) c') (hmi : M.Mi w o.thread.st c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  have hb := (stepOne_bnd _ hso ho h.core.bnd0).1
  have hcov := stepOne_cohL _ hso ho h.core.cov0
  have hpre := h.preC.mono (stepOne_getCoh_mono _ _ hso ho _)
  rw [hm] at hb hcov ⊢
  exact post_keep0 hC hC0 hPT0 hKR h hp hb hcov (fun hn => hC0.noProm0 w _ _ _ hn hco) hpre hr hmi

section Rows

variable (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
  (hKR : Q.KR = X64WakeKR.KR r0 r1)
  (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
  {outs : List (Except String (Outcome isa))} {o : Outcome isa}
  (hso : stepOne Arch.tso t0 0 t.1.mem = some outs) (ho : .ok o ∈ outs)
  (hco : CertOkC Arch.tso (certSem abi Arch.tso μ t.2 0) 0 o.thread o.mem)
include hC hC0 hPT0 hKR h hso ho hco

/-- **main's silent row keeps `Post`.** -/
theorem post_silent0 {s' : isa.State} {c' : Ctl} (he : isa.exec t0.st = some (.done s'))
    (hr : LocalRun wakeSrc (Ctl.of s0) c') (hX : M.Mi w s' c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  obtain ⟨st, hP, hth, hm⟩ := Lower.stepOne_silent_ok Arch.tso 0 he (Lower.silentTree_done s')
    ⟨outs, o, hso, ho, rfl, rfl⟩
  exact post_instrKeep0 hC hC0 hPT0 hKR h hso ho hco hm (finishInstr_relKey hth).1 hr
    ((finishInstr_st hth) ▸ hP ▸ hX)

/-- **main's choice row keeps `Post`.** -/
theorem post_choice0 {P : isa.State → Prop} {tree : EvTree isa.State}
    (he : isa.exec t0.st = some tree) (hs : Lower.SilentTree P tree)
    (hX : ∀ s', P s' → ∃ c', LocalRun wakeSrc (Ctl.of s0) c' ∧ M.Mi w s' c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  obtain ⟨st, hP, hth, hm⟩ := Lower.stepOne_silent_ok Arch.tso 0 he hs ⟨outs, o, hso, ho, rfl, rfl⟩
  obtain ⟨c', hr, hX'⟩ := hX _ ((finishInstr_st hth) ▸ hP)
  exact post_instrKeep0 hC hC0 hPT0 hKR h hso ho hco hm (finishInstr_relKey hth).1 hr hX'

/-- **main's fence row keeps `Post`.** -/
theorem post_fnc0 {k : Kraken.FenceKind} {s' : isa.State} {c' : Ctl}
    (he : isa.exec t0.st = some (.fence k fun _ => .done s'))
    (hr : LocalRun wakeSrc (Ctl.of s0) c') (hX : M.Mi w s' c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  obtain ⟨hst, hm, hp⟩ := stepOne_fence_eq Arch.tso he hso ho
  exact post_instrKeep0 hC hC0 hPT0 hKR h hso ho hco hm hp hr (hst ▸ hX)

/-- **main's runtime-load row keeps `Post`**: the value read is a `G` value
(the memory's invariant), the owned value if main owns the word
(`WCompat0.own0`; its latest write not promised, under its cover,
`WCompat0.ownCov0`). -/
theorem post_rtLoad0 {kl : Kraken.LoadKind} {L : Loc} {g : Val → isa.State} {c' : Ctl}
    (he : isa.exec t0.st = some (.load kl false L fun v => .done (g v)))
    (hr : LocalRun wakeSrc (Ctl.of s0) c')
    (hX : ∀ v, (M.ms w).G L v → (∀ u, (L, u) ∈ (M.ms w).own t0.st → v = u) → M.Mi w (g v) c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  obtain ⟨hm, hp⟩ := stepOne_load_keep' 0 he hso ho
  rw [hC0.G0 w] at hX
  simp only [hC0.own0 w] at hX
  have hmi : M.Mi w o.thread.st c' := by
    by_cases hL : ∃ v0, (L, v0) ∈ Q.own w 0 t0.st []
    · obtain ⟨v0, hv0⟩ := hL
      have hown := h.own0 hPT0
      have hL8 := (hown L v0 hv0).1
      have hcL := hC0.ownCov0 w _ L v0 hv0
      obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
      obtain ⟨-, ts1, v, hst, hl, hrd⟩ := stepOne_load_tlatestL Arch.tso he hso ho h.core.cov0 hcL
      rw [hst]
      exact hX v (h.core.memInv.read? hrd) fun u hu => hown.read hl hrd u hu
    · obtain ⟨v, hst, hG⟩ := stepOne_load_msgsExcept he hso ho (Scc.Sem.MemInv.msgsExcept h.core.memInv _)
        h.core.memInv.1
      rw [hst]
      exact hX v hG fun u hu => absurd ⟨u, hu⟩ hL
  exact post_instrKeep0 hC hC0 hPT0 hKR h hso ho hco hm hp hr hmi

end Rows

/-- info: 'Spike.Lib.X64WakeM0.post_rtLoad0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_rtLoad0

end Spike.Lib.X64WakeM0
