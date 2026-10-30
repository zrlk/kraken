/-
**wake.w after the spawn has progress** (`WakeObligations.post_progress`, AArch64): the skeleton, with
the three facts `Post` does not carry as named hypotheses.

- `out_progressG`, `out_no_errorG`, `out_execG`: `ExtRows.out_progress`,
  `out_no_error`, `out_exec` for an arbitrary memory side `ms` (the
  ExtRows lemmas are stated at `MemSide.ofLabels`; the proofs only case on
  the row); `outL_*`, `outT_*`: the same for the load-or-stutter row
  (`OutL.ldSt`, a load), the unpark (`OutT.unpk`, an RMW) and the fence
  (`OutT.fnc`, `fence_ok`).
- `TOk`, `progress_of`: **progress of the two-slot machine from per-thread
  facts**: a process that has not exited, a thread `0` that runs, and for
  every thread that runs: an instruction (`halted` false), at no transfer
  site, certified when it has promises, with no error outcome and no
  unmapped access off a system call, and a step with no promise off a
  system call (when it has none), and a supported call at one
  (no `write`, no `clone`, an `exit_group` off every abort site).
- `post_progress_of`: `post_progress` from `Post`, the compatibility facts
  (`WCompat`, `WCompat0`), `hoffM` (main off every abort site) and
  the named hypotheses:
  * `hca : CertAll μ t`: a running thread with promises is certified
    (`CertReplay.CertOkCNA`, hence `CertOkC`, under `certSem` at the current
    kernel state), the simulation's certification invariant.
  * `hmapped`: no instruction of a running thread touches an unmapped
    location (planned: `RunInv` with `WakeStack.mapped_held`).
  * `hhalt`: a thread at a system call has an instruction (the `svc`
    cell).
  `InLayout` is `Inv2Core.memIn` (`Consumer1.inLayout_of_memIn`).
-/
import Spike.Lib.WakeM0Sys
import Spike.Lib.WakeKR

namespace Spike.Lib.WakeProgress

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.Lower Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.ExtThread Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WakeW1 Spike.Lib.Inv2Core
open Kraken.Promising.Live.TicketStep (ctx0)

/-! ## The rows' outcomes, for any memory side -/

section Rows

variable {I : ISA} (A : Arch) {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
  {X : Frag I} {c : Ctl}

/-- **A thread with no promise at a fence has an outcome** with no promise. -/
theorem fence_ok {t : Thread I} {tid : Nat} {mem : Memory} (hp : t.prom = []) {k : Kraken.FenceKind}
    {s : I.State} (hex : I.exec t.st = some (.fence k fun _ => .done s)) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] := by
  obtain ⟨th, hth⟩ := Spike.Bridge.finishInstr_nonempty t (I.deps t.st) (instrViews t (I.deps t.st)) s
    (fenceStep (ctx0 tid t mem) k)
  obtain ⟨outs, o, hs, ho, rfl, -⟩ := (stepOne_ok_iff A tid hex).mpr ⟨s, _, (run_fence_iff A tid _).mpr ⟨rfl, rfl⟩, hth, rfl⟩
  exact ⟨outs, o, hs, ho, (finishInstr_relKey hth).1.trans ((fenceStep_fields _ k).2.2.2.2.1.trans hp)⟩

/-- **A fence has no error outcome.** -/
theorem fence_no_error {t : Thread I} {tid : Nat} {mem : Memory} {k : Kraken.FenceKind} {s : I.State}
    (hex : I.exec t.st = some (.fence k fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hs : stepOne A t tid mem = some outs) (m : String) :
    (.error m : Except String (Kraken.Promising.Outcome I)) ∉ outs :=
  Spike.Bridge.stepOne_no_error A hex (fun x hx => by
    simp only [runTree, List.mem_singleton] at hx; exact ⟨_, hx⟩) hs m

/-- **An `Out` row off a system call has an outcome** for a thread with no
promise and its values at most `|M|` (`ExtRows.out_progress`, any `ms`). -/
theorem out_progressG {K : Kernel.Abi I} {t : Thread I} {tid : Nat} {mem : Memory}
    (hp : t.prom = []) (hb : t.Bnd mem.last) (hK : ms.K = some K) (hns : K.atSys t.st = false)
    (hout : Out p lbl ms X t.st c) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] := by
  have hsil : ∀ {P : I.State → Prop} {tree : EvTree I.State}, I.exec t.st = some tree → SilentTree P tree →
      ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] := by
    intro P tree he hs
    obtain ⟨s, -, hall⟩ := stepOne_silent_exists A tid (mem := mem) he hs
    obtain ⟨th, hth⟩ := Spike.Bridge.finishInstr_nonempty t (I.deps t.st) (instrViews t (I.deps t.st)) s
      (ctx0 tid t mem)
    obtain ⟨outs, o, hs, ho, rfl, -⟩ := hall th hth
    exact ⟨outs, o, hs, ho, (finishInstr_relKey hth).1.trans hp⟩
  cases hout with
  | silent s' c' he => exact hsil he (silentTree_done s')
  | choice P tree he hs => exact hsil he hs
  | load kl A' g x a e ty w he => exact ExtRows.load_ok hp he
  | store kr A' V s' x a b e ty tb w wb he => exact ExtRows.store_ok hp hb he
  | rtStore kr L V s' c' he => exact ExtRows.store_ok hp hb he
  | rtLoad kl L g c' he => exact ExtRows.load_ok hp he
  | rtRmw k L op g c' he => exact RtRmw.rmw_ok A hp hb he
  | sys K' _ hK' hs => rw [hK] at hK'; cases hK'; rw [hns] at hs; cases hs
  | emit K' _ _ _ _ hK' hae => rw [hK] at hK'; cases hK'; rw [hns] at hae; cases hae
  | holdLoad kl A' g x sa u v e he => exact ExtRows.load_ok hp he
  | xchgStore kr A' V s' x sa u v e tv wv wold he => exact ExtRows.store_ok hp hb he
  | ctrRmw k op g x τ e n he => exact RtRmw.rmw_ok A hp hb he
  | alloc s' A' x a τ e ta ws k _ _ _ he => exact hsil he (silentTree_done s')
  | newStore kr A' V s' x a t e w wold old _ he => exact ExtRows.store_ok hp hb he
  | fence k s' c' he =>
    obtain ⟨outs, o, hs, ho, hpo⟩ := FenceStep.stepOne_fence_progress A tid (mem := mem) he
    exact ⟨outs, o, hs, ho, hpo.trans hp⟩

/-- **An `Out` row off a system call has no error outcome** (any `ms`). -/
theorem out_no_errorG {K : Kernel.Abi I} {t : Thread I} {tid : Nat} {mem : Memory}
    (hK : ms.K = some K) (hns : K.atSys t.st = false) (hout : Out p lbl ms X t.st c)
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hs : stepOne A t tid mem = some outs) (m : String) :
    (.error m : Except String (Kraken.Promising.Outcome I)) ∉ outs := by
  cases hout with
  | silent s' c' he => exact stepOne_silent_no_error A tid he (silentTree_done s') hs m
  | choice P tree he hsl => exact stepOne_silent_no_error A tid he hsl hs m
  | load kl A' g x a e ty w he =>
    exact Spike.Bridge.stepOne_no_error A he (Spike.Bridge.runTree_load_ok A _ _ _ _ _ _) hs m
  | store kr A' V s' x a b e ty tb w wb he =>
    exact Spike.Bridge.stepOne_no_error A he (Spike.Bridge.runTree_store_ok A _ _ _ _ _ _ _) hs m
  | rtStore kr L V s' c' he =>
    exact Spike.Bridge.stepOne_no_error A he (Spike.Bridge.runTree_store_ok A _ _ _ _ _ _ _) hs m
  | rtLoad kl L g c' he =>
    exact Spike.Bridge.stepOne_no_error A he (Spike.Bridge.runTree_load_ok A _ _ _ _ _ _) hs m
  | rtRmw k L op g c' he =>
    exact Spike.Bridge.stepOne_no_error A he (RtRmw.runTree_rmw_ok A _ _ _ _ _ _ _) hs m
  | sys K' _ hK' hsy => rw [hK] at hK'; cases hK'; rw [hns] at hsy; cases hsy
  | emit K' _ _ _ _ hK' hae => rw [hK] at hK'; cases hK'; rw [hns] at hae; cases hae
  | holdLoad kl A' g x sa u v e he =>
    exact Spike.Bridge.stepOne_no_error A he (Spike.Bridge.runTree_load_ok A _ _ _ _ _ _) hs m
  | xchgStore kr A' V s' x sa u v e tv wv wold he =>
    exact Spike.Bridge.stepOne_no_error A he (Spike.Bridge.runTree_store_ok A _ _ _ _ _ _ _) hs m
  | ctrRmw k op g x τ e n he =>
    exact Spike.Bridge.stepOne_no_error A he (RtRmw.runTree_rmw_ok A _ _ _ _ _ _ _) hs m
  | alloc s' A' x a τ e ta ws k _ _ _ he => exact stepOne_silent_no_error A tid he (silentTree_done s') hs m
  | newStore kr A' V s' x a t e w wold old _ he =>
    exact Spike.Bridge.stepOne_no_error A he (Spike.Bridge.runTree_store_ok A _ _ _ _ _ _ _) hs m
  | fence k s' c' he => exact FenceStep.stepOne_fence_no_error A tid he hs m

/-- **An `Out` row off a system call has an instruction** (any `ms`). -/
theorem out_execG {K : Kernel.Abi I} {s : I.State} (hK : ms.K = some K) (hns : K.atSys s = false)
    (h : Out p lbl ms X s c) : (I.exec s).isSome := by
  cases h with
  | sys K' _ hK' hs => rw [hK] at hK'; cases hK'; rw [hns] at hs; cases hs
  | emit K' _ _ _ _ hK' hae => rw [hK] at hK'; cases hK'; rw [hns] at hae; cases hae
  | silent _ _ he | choice _ _ he _ | load _ _ _ _ _ _ _ _ he | store _ _ _ _ _ _ _ _ _ _ _ _ he
  | rtStore _ _ _ _ _ he | rtLoad _ _ _ _ he | rtRmw _ _ _ _ _ he | holdLoad _ _ _ _ _ _ _ _ he
  | xchgStore _ _ _ _ _ _ _ _ _ _ _ _ he | ctrRmw _ _ _ _ _ _ _ he | alloc _ _ _ _ _ _ _ _ _ _ _ _ he
  | fence _ _ _ he | newStore _ _ _ _ _ _ _ _ _ _ _ _ he =>
    rw [he]; rfl

/-- The off-system-call facts of a row: an instruction, an outcome with no
promise (for a thread with none), no error outcome. -/
def RowOK (A : Arch) (t : Thread I) (tid : Nat) (mem : Memory) : Prop :=
  (I.exec t.st).isSome ∧
    (t.prom = [] → ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = []) ∧
    ∀ outs, stepOne A t tid mem = some outs → ∀ m, (.error m : Except String (Kraken.Promising.Outcome I)) ∉ outs

/-- **An `OutL` row off a system call is `RowOK`.** -/
theorem outL_ok {K : Kernel.Abi I} {t : Thread I} {tid : Nat} {mem : Memory} (hb : t.Bnd mem.last)
    (hK : ms.K = some K) (hns : K.atSys t.st = false) (h : OutL p lbl ms X t.st c) : RowOK A t tid mem := by
  cases h with
  | out r =>
    exact ⟨out_execG hK hns r, fun hp => out_progressG A hp hb hK hns r,
      fun _ hs m => out_no_errorG A hK hns r hs m⟩
  | ldSt kl A' g x a e ty w V he =>
    exact ⟨by rw [he]; rfl, fun hp => ExtRows.load_ok hp he,
      fun _ hs m => Spike.Bridge.stepOne_no_error A he (Spike.Bridge.runTree_load_ok A _ _ _ _ _ _) hs m⟩

/-- **An `OutT` row off a system call is `RowOK`.** -/
theorem outT_ok {K : Kernel.Abi I} {t : Thread I} {tid : Nat} {mem : Memory} (hb : t.Bnd mem.last)
    (hK : ms.K = some K) (hns : K.atSys t.st = false) (h : OutT p lbl ms X t.st c) : RowOK A t tid mem := by
  cases h with
  | outL r => exact outL_ok A hb hK hns r
  | unpk k A' B op g x a e ty jw he =>
    exact ⟨by rw [he]; rfl, fun hp => RtRmw.rmw_ok A hp hb he,
      fun _ hs m => Spike.Bridge.stepOne_no_error A he (RtRmw.runTree_rmw_ok A _ _ _ _ _ _ _) hs m⟩
  | texit K' a hK' hat => rw [hK] at hK'; cases hK'; rw [hns] at hat; cases hat
  | fnc k s' c' he =>
    exact ⟨by rw [he]; rfl, fun hp => fence_ok A hp he, fun _ hs m => fence_no_error A he hs m⟩

end Rows

/-! ## Progress of the two-slot machine from per-thread facts -/

/-- **The supported calls of a progress argument**: no `write`, no `clone`,
an `exit_group` off every abort site. -/
def CallOK (μ : Marks) (s : isaLSE2.State) (call : Call) : Prop :=
  (∀ fd buf n, call ≠ .write fd buf n) ∧ (∀ st tl, call ≠ .clone st tl) ∧
    ∀ v, call = .exitGroup v → ∀ k a, μ.abortAt k = some a → pcOf s ≠ a

/-- **The facts about a running thread `th` (slot `tid`) progress needs**:
an instruction, at no transfer site, certified when it has promises; off a
system call `RowOK` and no unmapped access; at one a supported call. -/
structure TOk (μ : Marks) (t : Cfg) (tid : Nat) (th : Thread isaLSE2) : Prop where
  exec : (isaLSE2.exec th.st).isSome
  site : siteAt abi μ th.st = none
  cert : th.prom ≠ [] → CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 tid) tid th t.1.mem
  row : abi.atSys th.st = false → RowOK Arch.armv8 th tid t.1.mem
  mapped : abi.atSys th.st = false → ∀ e, isaLSE2.exec th.st = some e →
    ¬ Touches (fun l w => Kernel.mapped t.2 w l = false) e
  sys : abi.atSys th.st = true → ∃ call, callOf abi th = some call ∧ CallOK μ th.st call

theorem runs_true {x : KState} {tid : Nat} (h : ¬ x.runs tid = false) : x.runs tid = true := by
  cases hr : x.runs tid
  · exact absurd hr h
  · rfl

/-- **The step of a running thread** from its `TOk` facts: off a system
call its row's outcome with no promise left or the first step of its
certification; at one the kernel's return (`Kernel.sys_progress` with
promises), `exit` or `exit_group` (none with promises,
`Kernel.prom_nil_of_exit`). -/
theorem tOk_step {μ : Marks} {t : Cfg} {tid : Nat} {th : Thread isaLSE2}
    (ht : t.1.threads[tid]? = some th) (hrk : t.2.runs tid = true) (hxk : t.2.exited = none)
    (h : TOk μ t tid th) : ∃ es c', (machine (kernel 2)).Step μ tid t es c' := by
  have hruns : (machine (kernel 2)).runs t tid :=
    ⟨⟨th, ht⟩, hxk, by show ¬ (t.2.runs tid = false); rw [hrk]; simp⟩
  have hsn := h.site
  have hsite : ∀ k, ¬ (machine (kernel 2)).AtSite μ k t tid := by
    rintro k ⟨a, ha, t2, ht2, hpc⟩
    cases (show some t2 = some th from ht2.symm.trans ht)
    have hn := siteAt_eq_none_iff.mp hsn
    cases k
    · subst hpc; exact hn.1 ha
    · subst hpc; exact hn.2 ha
  cases hs : abi.atSys th.st
  · have hnsys : ¬ (machine (kernel 2)).atSys t tid := fun ⟨t2, ht2, h2⟩ => by
      cases (show some t2 = some th from ht2.symm.trans ht)
      have h3 : abi.atSys th.st = true := h2
      rw [hs] at h3; cases h3
    by_cases hpn : th.prom = []
    · obtain ⟨outs, o, hso, ho, hpo⟩ := (h.row hs).2.1 hpn
      exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, certOkC_of_prom_nil hpo, rfl⟩)⟩
    · obtain ⟨t', mem', hr, hp'⟩ := h.cert hpn
      cases hr with
      | refl => exact absurd hp' hpn
      | step hs1 hrest =>
        obtain ⟨outs, o, hso, ho, rfl⟩ := hs1
        replace hso : stepOne Arch.armv8 th tid t.1.mem = some outs :=
          (Kernel.certSem_step_of_not_site (x := t.2) hsn hs).symm.trans hso
        exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, ⟨t', mem', hrest, hp'⟩, rfl⟩)⟩
  · have hr := Kernel.ready_of abi (t := th) (c := t) hs hrk hxk
    obtain ⟨call, hc, hnw, hcl, hab⟩ := h.sys hs
    have hsys : ∀ c', (kernel 2).sys μ tid t [] c' → ∃ es c', (machine (kernel 2)).Step μ tid t es c' :=
      fun c' h => ⟨[], c', .sys hruns h (by simp) (by simp) (by simp)⟩
    by_cases hpn : th.prom = []
    rotate_left
    · cases call with
      | write fd buf n => exact absurd rfl (hnw fd buf n)
      | exitGroup v => exact absurd (Kernel.prom_nil_of_exit hsn hs hc (.inr ⟨v, rfl⟩) (h.cert hpn)) hpn
      | exit => exact absurd (Kernel.prom_nil_of_exit hsn hs hc (.inl rfl) (h.cert hpn)) hpn
      | clone st tl => exact absurd rfl (hcl st tl)
      | _ =>
        obtain ⟨r, es, c', h', hca⟩ := Kernel.sys_progress ht hr hsn hc (fun _ _ _ h => by cases h)
          (fun _ _ h => by cases h) hpn (h.cert hpn)
        obtain rfl := Kernel.sysStep_ret_nil ht hc (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
          (fun h => by cases h) (fun _ h => by cases h) h'
        exact hsys c' ⟨.ret r, h', hca⟩
    cases call with
    | write fd buf n => exact absurd rfl (hnw fd buf n)
    | futexWait => exact hsys _ (Kernel.sys_futexWait (K := abi) Arch.armv8 2 ht hr hpn hc)
    | futexWake k => exact hsys _ (Kernel.sys_futexWake (K := abi) Arch.armv8 2 ht hr hpn hc)
    | rtSigaction => exact hsys _ (Kernel.sys_rtSigaction (K := abi) Arch.armv8 2 ht hr hpn hc)
    | archSetFs a => exact hsys _ (Kernel.sys_archSetFs (K := abi) Arch.armv8 2 ht hr hpn hc)
    | exitGroup v =>
      have hnoab : ∀ k a, μ.abortAt k = some a → ¬ (machine (kernel 2)).AtAddr a t tid :=
        fun k a ha ⟨t2, ht2, hpc⟩ => by
          cases (show some t2 = some th from ht2.symm.trans ht); exact hab v rfl k a ha hpc
      exact ⟨_, _, .sys hruns (Kernel.sys_exitGroup (K := abi) Arch.armv8 2 ht hr hpn hc) (by simp)
        (fun k hk => by simp at hk) (fun _ _ => hnoab)⟩
    | exit =>
      refine hsys _ ⟨.ret 0, by simp [sysStep, ht, hr, hc] <;> rfl, certAfter_of_prom abi fun t' h' => ?_⟩
      cases (show some th = some t' from ht.symm.trans h')
      exact hpn
    | clone st tl => exact absurd rfl (hcl st tl)

/-- **Progress of the two-slot machine from per-thread facts**: a process
that has not exited, thread `0` running, and `TOk` for every running
thread. -/
theorem progress_of {μ : Marks} {t : Cfg} (hx : t.2.exited = none)
    (h0 : ∃ th, t.1.threads[0]? = some th ∧ t.2.runs 0 = true)
    (hok : ∀ tid th, t.1.threads[tid]? = some th → t.2.runs tid = true → TOk μ t tid th) :
    (machine (kernel 2)).Progress μ t := by
  have nh : ∀ tid th, t.1.threads[tid]? = some th → t.2.runs tid = true → th.halted = false := by
    intro tid th ht hr
    have he := (hok tid th ht hr).exec
    simp only [Thread.halted]
    cases hh : isaLSE2.exec th.st
    · rw [hh] at he; cases he
    · rfl
  refine ⟨?_, .inr ⟨?_, fun tid hl => ?_⟩⟩
  · rintro (⟨tid, m, ⟨⟨t1, ht1⟩, -, hd⟩, hns, outs, hs, hm⟩ | (⟨tid, hf⟩ | ⟨tid, t1, e, ht1, hr, -, hns, hex, htouch⟩))
    · have hr := runs_true hd
      have hsy : abi.atSys t1.st = false := by
        cases h : abi.atSys t1.st
        · rfl
        · exact absurd ⟨t1, ht1, h⟩ hns
      have hs' : stepOne Arch.armv8 t1 tid t.1.mem = some outs := by simp only [stepThread, ht1] at hs; exact hs
      exact ((hok tid t1 ht1 hr).row hsy).2.2 outs hs' m hm
    · unfold Kernel.faultAt at hf
      split at hf
      · rename_i t1 ht1
        have hr : t.2.runs tid = true := by
          cases h : t.2.runs tid
          · simp [h] at hf
          · rfl
        have hT := hok tid t1 ht1 hr
        rw [nh tid t1 ht1 hr, Bool.or_false] at hf
        cases hsy : abi.atSys t1.st
        · simp [hsy] at hf
        · obtain ⟨call, hd, -, hcl, -⟩ := hT.sys hsy
          rw [hd] at hf
          cases call with
          | clone st tl => exact hcl st tl rfl
          | _ => simp at hf
      · cases hf
    · exact (hok tid t1 ht1 hr).mapped hns e hex htouch
  · obtain ⟨th, ht, hr⟩ := h0
    exact ⟨0, hx, by show ¬ (t.2.runs 0 = false); rw [hr]; simp, th, ht,
      fun h => by rw [nh 0 th ht hr] at h; cases h.1⟩
  · obtain ⟨hx', hd, th, ht, -⟩ := hl
    have hr := runs_true hd
    exact tOk_step ht hr hx (hok tid th ht hr)

/-! ## wake.w after the spawn -/

variable {Q : WakeRel} {D : WSide Q.ι} {M : WakeM0.MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}

/-- **main's call at a system call** is supported (`CallOK`): its row is
`Out.sys` (`WakeM0.sys_rows0`: not `exit` or `clone`), not a `write`
(`WCompat0.noWrite0`), and main is off every abort site (`hoffM`). -/
theorem main_call (hC0 : WakeM0.WCompat0 Q M μ Λ)
    (hoffM : ∀ w s c, M.Mi w s c → ∀ k a, μ.abortAt k = some a → pcOf s ≠ a)
    {w : Q.ι} {st : isaLSE2.State} {c : Ctl} (hmi : M.Mi w st c) (hat : abi.atSys st = true) :
    ∃ call, decode abi.nrs (abi.nr st) (abi.arg st) = some call ∧ CallOK μ st call := by
  have hd : ∃ call, decode abi.nrs (abi.nr st) (abi.arg st) = some call := by
    cases M.closed w _ _ hmi with
    | out r =>
      cases r with
      | sys K call hK ha hd => rw [hC0.K0 w] at hK; cases hK; exact ⟨call, hd⟩
      | emit K buf n Pw Qw hK ha hd => rw [hC0.K0 w] at hK; cases hK; exact ⟨_, hd⟩
      | choice P tree he hsil hX =>
        obtain ⟨m, rfl⟩ := hC0.sysExec0 w _ _ _ hmi hat he
        cases hsil
      | _ =>
        obtain ⟨m, hm⟩ := hC0.sysExec0 w _ _ _ hmi hat ‹isaLSE2.exec st = some _›
        cases hm
    | ldSt _ _ _ _ _ _ _ _ _ he =>
      obtain ⟨m, hm⟩ := hC0.sysExec0 w _ _ _ hmi hat he
      cases hm
  obtain ⟨call, hd⟩ := hd
  obtain ⟨hok, -⟩ := WakeM0.sys_rows0 hC0 hmi hat hd
  exact ⟨call, hd, fun fd buf n e => hC0.noWrite0 w _ _ fd buf n hmi hat (e ▸ hd), hok.2.1,
    fun _ _ k a ha => hoffM w _ _ hmi k a ha⟩

/-- **The worker's call at a system call** is supported (`CallOK`): its
row is `Out.sys` (`SysOk`: not `exit` or `clone`; `WCompat.sysOk`: then
neither `write` nor `exit_group`) or `OutT.texit` (`exit`); the `emit` row is
a `write`, which `WCompat.sysOk` excludes. -/
theorem worker_call (hC : WCompat Q D μ Λ arch) {w : Q.ι} {st : isaLSE2.State} {c : Ctl} (hwi : D.Wi w st c)
    (hat : abi.atSys st = true) :
    ∃ call, decode abi.nrs (abi.nr st) (abi.arg st) = some call ∧ CallOK μ st call := by
  have hx : CallOK μ st .exit := ⟨fun _ _ _ => nofun, fun _ _ => nofun, fun _ h => nomatch h⟩
  cases D.closed w _ _ hwi with
  | outL hl =>
    cases hl with
    | out r =>
      cases r with
      | sys K call hK ha hd hok =>
        rw [hC.K w] at hK; cases hK
        rcases hC.sysOk w _ _ call hwi hat hd with rfl | ⟨hnw, hng⟩
        · exact absurd rfl hok.1
        · exact ⟨call, hd, hnw, hok.2.1, fun v e => absurd e (hng v)⟩
      | emit K buf n Pw Qw hK ha hd =>
        rw [hC.K w] at hK; cases hK
        rcases hC.sysOk w _ _ _ hwi hat hd with h | ⟨hnw, -⟩
        · cases h
        · exact absurd rfl (hnw 1 buf n)
      | choice P tree he hsil hX =>
        obtain ⟨m, rfl⟩ := hC.sysExec w _ _ _ hwi hat he
        cases hsil
      | _ =>
        obtain ⟨m, hm⟩ := hC.sysExec w _ _ _ hwi hat ‹isaLSE2.exec st = some _›
        cases hm
    | ldSt _ _ _ _ _ _ _ _ _ he =>
      obtain ⟨m, hm⟩ := hC.sysExec w _ _ _ hwi hat he
      cases hm
  | texit K a hK ha hd => rw [hC.K w] at hK; cases hK; exact ⟨_, hd, hx⟩
  | unpk _ _ _ _ _ _ _ _ _ _ he =>
    obtain ⟨m, hm⟩ := hC.sysExec w _ _ _ hwi hat he
    cases hm
  | fnc _ _ _ he =>
    obtain ⟨m, hm⟩ := hC.sysExec w _ _ _ hwi hat he
    cases hm

/-- **`post_progress`** (skeleton): after the spawn the
two-slot machine has progress and its memory is in the layout. An exited
process has progress (`Kernel.exited_progress`); otherwise `progress_of`,
thread 0 running by `KR`, main's `TOk` from its rows (`WakeM0.MSide.closed`,
`WCompat0`; `KR`'s `MainLive` puts it in `Mi`, not at `wlRet`), the
worker's from its rows (`WSide.closed`, `WCompat`). `InLayout` is
`Inv2Core.memIn`. The named hypotheses (owners):
- `hca` (`CertAll`, the simulation's certification invariant, kept by
  `WakeObligations.cert_step`): a running thread with promises is certified
  at the current kernel state;
- `hmapped` (`RunInv` and `WakeStack.mapped_held`, the per-row
  accesses): no running thread's instruction touches an unmapped location;
- `hhalt0`, `hhalt1`: at a system call the state has an
  instruction (the `svc` cell, `Lower.A64.exec_svc`). -/
theorem post_progress_of (hC : WCompat Q D μ Λ arch) (hC0 : WakeM0.WCompat0 Q M μ Λ)
    (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = WakeKR.KR r0 r1)
    (hoffM : ∀ w s c, M.Mi w s c → ∀ k a, μ.abortAt k = some a → pcOf s ≠ a)
    (hhalt0 : ∀ w s c, M.Mi w s c → abi.atSys s = true → (isaLSE2.exec s).isSome)
    (hhalt1 : ∀ w s c, D.Wi w s c → abi.atSys s = true → (isaLSE2.exec s).isSome)
    {t : Cfg} {s : TermRun.Cfg} (hP : Q.Post Λ t s)
    (hca : CertAll μ t)
    (hmapped : t.2.exited = none → ∀ tid th e, t.1.threads[tid]? = some th → t.2.runs tid = true →
      abi.atSys th.st = false →
      isaLSE2.exec th.st = some e → ¬ Touches (fun l w => Kernel.mapped t.2 w l = false) e) :
    (machine (kernel 2)).Progress μ t ∧ InLayout (M := machine (kernel 2)) Λ t := by
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hT, hS, core, h0, h1, -⟩, hK⟩ := hP
  refine ⟨?_, Consumer1.inLayout_of_memIn core.memIn⟩
  rw [hKR] at hK
  obtain ⟨-, ⟨j, hsl0⟩, -, -, hm, -⟩ := hK
  cases hx : t.2.exited with
  | some o => exact Kernel.exited_progress abi (o := o) hx
  | none =>
  simp only [WakeRel.PTw] at h0 h1
  rw [hPT0] at h0
  rw [hC.pt1] at h1
  have ht0 : t.1.threads[0]? = some t0 := by rw [hT]; rfl
  have ht1 : t.1.threads[1]? = some t1 := by rw [hT]; rfl
  have hr0 : t.2.runs 0 = true := by simp [KState.runs, hsl0]
  have hmi : M.Mi w t0.st (Ctl.of s0) :=
    h0.2.1.resolve_right (hm hx s0 (by rw [hS]; rfl))
  have hwi : D.Wi w t1.st (Ctl.of s1) := h1.1
  refine progress_of hx ⟨t0, ht0, hr0⟩ fun tid th ht hr => ?_
  rcases tid with _ | _ | n
  · cases (show some t0 = some th from ht0.symm.trans ht)
    have hrow : abi.atSys t0.st = false → RowOK Arch.armv8 t0 0 t.1.mem :=
      fun hs => outL_ok Arch.armv8 core.bnd0 (hC0.K0 w) hs (M.closed w _ _ hmi)
    refine ⟨?_, hC0.noSite0 w _ _ hmi, fun hp => (hca hx 0 t0 ht0 hr hp).certOkC, hrow, fun hs e hex => hmapped hx 0 t0 e ht0 hr hs hex, fun hs => ?_⟩
    · cases hs : abi.atSys t0.st
      · exact (hrow hs).1
      · exact hhalt0 w _ _ hmi hs
    · exact main_call hC0 hoffM hmi hs
  · cases (show some t1 = some th from ht1.symm.trans ht)
    have hrow : abi.atSys t1.st = false → RowOK Arch.armv8 t1 1 t.1.mem :=
      fun hs => outT_ok Arch.armv8 core.bnd1 (hC.K w) hs (D.closed w _ _ hwi)
    refine ⟨?_, hC.noSite w _ _ hwi, fun hp => (hca hx 1 t1 ht1 hr hp).certOkC, hrow, fun hs e hex => hmapped hx 1 t1 e ht1 hr hs hex, fun hs => ?_⟩
    · cases hs : abi.atSys t1.st
      · exact (hrow hs).1
      · exact hhalt1 w _ _ hwi hs
    · exact worker_call hC hwi hs
  · rw [hT] at ht; simp at ht

/-- info: 'Spike.Lib.WakeProgress.post_progress_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_progress_of

end Spike.Lib.WakeProgress
