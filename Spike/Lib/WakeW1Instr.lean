/-
**The worker's instruction steps that keep memory and promises** (hello
plan 1.6; data in `Spike/Lib/WakeW1.lean`,
`Spike/Lib/WakeW1Compat.lean`).

- `post_instrKeep`: an instruction step of the worker keeping memory and
  promises, its new state with a local run of the source worker in `Wi`,
  keeps `Post` (`post_keep`; the bound, cover and owned words by the step
  lemmas, no promise at a no-promise state by certification).
- `post_silent`, `post_choice`, `post_fnc`, `post_rtLoad`: the rows that
  keep memory and promises.
-/
import Spike.Lib.WakeW1Keep

namespace Spike.Lib.WakeW1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt

variable {Q : WakeRel} {D : WSide Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

namespace Parts

/-- The worker's promises are at most the memory's last timestamp. -/
theorem prom_le (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) : ∀ p ∈ t1.prom, p ≤ t.1.mem.last := by
  intro p hp
  obtain ⟨-, m, hg, -⟩ := h.core.prom1 p hp
  exact Scc.Sem.Memory.le_last_of_get? hg

/-- The worker's owned words read as their values. -/
theorem own1 (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) :
    ExtRows.OwnOk (Q.own w 1 t1.st []) t.1.mem t1.prom := by
  have := h.core.own1
  simp only [Nat.one_ne_zero, ite_false] at this
  rw [h.pt1.2.1] at this
  exact this

/-- The worker's promises are distinct. -/
theorem nodup (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) : t1.prom.Nodup :=
  h.pt1.2.2.2.2.2.2.2.2

end Parts

/-- A successful instruction step has a tree. -/
theorem exec_of_stepOne {t1 : Thread isaLSE2} {mem : Memory} {outs : List (Except String (Outcome isaLSE2))}
    (hso : stepOne Arch.armv8 t1 1 mem = some outs) : ∃ tree, isaLSE2.exec t1.st = some tree := by
  cases hex : isaLSE2.exec t1.st with
  | none => simp [stepOne, hex] at hso
  | some tree => exact ⟨tree, rfl⟩

/-- **An instruction step of the worker keeps its owned words** (`ownOk_stepL`
on its cover set, the owned words' tree by `WCompat.ownInstr`). -/
theorem Parts.own_step (hC : WCompat Q D μ Λ arch) (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hns : abi.atSys t1.st = false) {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
    (hso : stepOne Arch.armv8 t1 1 t.1.mem = some outs) (ho : .ok o ∈ outs) :
    ExtRows.OwnOk (Q.own w 1 o.thread.st []) o.mem o.thread.prom := by
  obtain ⟨tree, hex⟩ := exec_of_stepOne hso
  exact ownOk_stepL hex (hC.ownInstr w _ _ tree h.pt1.1 hns hex) h.core.cov1 h.nodup h.prom_le hso ho
    (fun l v hm => hC.ownCov w _ l v hm) (fun l v hm => hC.ownCov w _ l v hm) h.own1

/-- **An instruction step of the worker keeping memory and promises keeps
`Post`**, its new state with the source worker's local run in `Wi`. -/
theorem post_instrKeep (hC : WCompat Q D μ Λ arch) (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hex : SrcSem.mainExit s = []) (hns : abi.atSys t1.st = false)
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
    (hso : stepOne Arch.armv8 t1 1 t.1.mem = some outs) (ho : .ok o ∈ outs)
    (hco : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 o.thread o.mem)
    (hm : o.mem = t.1.mem) (hp : o.thread.prom = t1.prom) {c' : Ctl}
    (hr : LocalRun wakeSrc (Ctl.of s1) c') (hwi : D.Wi w o.thread.st c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  have hb := (stepOne_bnd _ hso ho h.core.bnd1).1
  have hcov := stepOne_cohL _ hso ho h.core.cov1
  have hown := h.own_step hC hns hso ho
  rw [hm] at hb hcov hown ⊢
  exact post_keep hC h hex hp hb hcov hown (fun hn => hC.noProm w _ _ _ hn hco) hr hwi

/-! ## The rows keeping memory and promises -/

/-- A load keeps memory and promises and lands at one of its values. -/
theorem stepOne_load_keep {t1 : Thread isaLSE2} {mem : Memory} {kl : Kraken.LoadKind} {xcl : Bool} {L : Loc}
    {g : Val → isaLSE2.State} (hex : isaLSE2.exec t1.st = some (.load kl xcl L fun v => .done (g v)))
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
    (hso : stepOne Arch.armv8 t1 1 mem = some outs) (ho : .ok o ∈ outs) :
    o.mem = mem ∧ o.thread.prom = t1.prom := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff Arch.armv8 1 hex).mp ⟨outs, o, hso, ho, rfl, rfl⟩
  rw [Lower.run_load_iff] at hr
  obtain ⟨ts1, v, hx, rfl⟩ := hr
  have hmem : c'.mem = mem := by
    obtain ⟨-, -, -, he⟩ := readSuccs_shape Arch.armv8 _ hx
    exact congrArg Ctx.mem he
  exact ⟨hm.trans hmem, (finishInstr_relKey hth).1.trans (readSuccs_prom Arch.armv8 _ hx)⟩

/-- **A silent row** (`Out.silent`, `Out.choice`): memory and promises kept,
the state a leaf. -/
theorem stepOne_silent_keep {t1 : Thread isaLSE2} {mem : Memory} {tree : EvTree isaLSE2.State}
    {P : isaLSE2.State → Prop} (hex : isaLSE2.exec t1.st = some tree) (hs : Lower.SilentTree P tree)
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
    (hso : stepOne Arch.armv8 t1 1 mem = some outs) (ho : .ok o ∈ outs) :
    o.mem = mem ∧ o.thread.prom = t1.prom ∧ P o.thread.st := by
  obtain ⟨st, hP, hth, hm⟩ := Lower.stepOne_silent_ok Arch.armv8 1 hex hs ⟨outs, o, hso, ho, rfl, rfl⟩
  exact ⟨hm, (finishInstr_relKey hth).1, (finishInstr_st hth) ▸ hP⟩

section Rows

variable (hC : WCompat Q D μ Λ arch) (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
  (hex : SrcSem.mainExit s = []) (hns : abi.atSys t1.st = false)
  {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
  (hso : stepOne Arch.armv8 t1 1 t.1.mem = some outs) (ho : .ok o ∈ outs)
  (hco : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 o.thread o.mem)
include hC h hex hns hso ho hco

/-- **The silent row keeps `Post`.** -/
theorem post_silent {s' : isaLSE2.State} {c' : Ctl} (he : isaLSE2.exec t1.st = some (.done s'))
    (hr : LocalRun wakeSrc (Ctl.of s1) c') (hX : D.Wi w s' c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  obtain ⟨hm, hp, hst⟩ := stepOne_silent_keep he (Lower.silentTree_done s') hso ho
  exact post_instrKeep hC h hex hns hso ho hco hm hp hr (hst ▸ hX)

/-- **The choice row keeps `Post`.** -/
theorem post_choice {P : isaLSE2.State → Prop} {tree : EvTree isaLSE2.State}
    (he : isaLSE2.exec t1.st = some tree) (hs : Lower.SilentTree P tree)
    (hX : ∀ s', P s' → ∃ c', LocalRun wakeSrc (Ctl.of s1) c' ∧ D.Wi w s' c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  obtain ⟨hm, hp, hP⟩ := stepOne_silent_keep he hs hso ho
  obtain ⟨c', hr, hX'⟩ := hX _ hP
  exact post_instrKeep hC h hex hns hso ho hco hm hp hr hX'

/-- **The fence row keeps `Post`.** -/
theorem post_fnc {k : Kraken.FenceKind} {s' : isaLSE2.State} {c' : Ctl}
    (he : isaLSE2.exec t1.st = some (.fence k fun _ => .done s'))
    (hr : LocalRun wakeSrc (Ctl.of s1) c') (hX : D.Wi w s' c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  obtain ⟨hst, hm, hp⟩ := stepOne_fence_eq Arch.armv8 he hso ho
  exact post_instrKeep hC h hex hns hso ho hco hm hp hr (hst ▸ hX)

/-- **The runtime-load row keeps `Post`**: the value read is a `G` value
(the memory's invariant), the owned value if the worker owns the word (its
latest write not promised, under its cover). -/
theorem post_rtLoad {kl : Kraken.LoadKind} {L : Loc} {g : Val → isaLSE2.State} {c' : Ctl}
    (he : isaLSE2.exec t1.st = some (.load kl false L fun v => .done (g v)))
    (hr : LocalRun wakeSrc (Ctl.of s1) c')
    (hX : ∀ v, (D.ms w).G L v → (∀ u, (L, u) ∈ (D.ms w).own t1.st → v = u) → D.Wi w (g v) c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  obtain ⟨hm, hp⟩ := stepOne_load_keep he hso ho
  rw [hC.G w] at hX
  simp only [hC.own w] at hX
  have hwi : D.Wi w o.thread.st c' := by
    by_cases hL : ∃ v0, (L, v0) ∈ Q.own w 1 t1.st []
    · obtain ⟨v0, hv0⟩ := hL
      have hL8 := (h.own1 L v0 hv0).1
      have hcL := hC.ownCov w _ L v0 hv0
      obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
      obtain ⟨-, ts1, v, hst, hl, hrd⟩ := stepOne_load_tlatestL Arch.armv8 he hso ho h.core.cov1 hcL
      rw [hst]
      exact hX v (h.core.memInv.read? hrd) fun u hu => h.own1.read hl hrd u hu
    · obtain ⟨v, hst, hG⟩ := stepOne_load_msgsExcept he hso ho (Scc.Sem.MemInv.msgsExcept h.core.memInv _) h.core.memInv.1
      rw [hst]
      exact hX v hG fun u hu => absurd ⟨u, hu⟩ hL
  exact post_instrKeep hC h hex hns hso ho hco hm hp hr hwi

end Rows

end Spike.Lib.WakeW1
