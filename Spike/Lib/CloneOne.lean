/-
**A `clone` with no dormant slot, and with one** (the
pre-spawn half), for any ISA and `Kernel.Abi` on the canonical machine.

- `clone_step_nodormant`: a step of a thread at a `clone` call in a
  configuration with no dormant slot (the one-slot configuration before the
  spawn) is the kernel's refusal: the event `cloneErr`, the thread returned
  `-EAGAIN` or `-ENOMEM` (`retThread`), the kernel state and memory
  unchanged. A successful `clone` (`spawnStep`) needs a dormant slot.
- `nodormant_one`: one running slot leaves none dormant.
- `obs_cloneErr`: the refusal is unobservable (the source stutters).
- `clone_progress_up`: the lifted configuration `up d u` of a one-thread
  `d` (any `u`) whose thread is at a `clone` with no promise has progress (the extra
  dormant slot: no fault, `dormants_up`; the refusal steps, `sys_cloneErr`).
-/
import Spike.Lib.TwoSlot

namespace Spike.Lib.CloneOne

open Kraken.Promising Scc.Sem Scc.Sem.Kernel Spike.Lib.TwoSlot

variable {I : ISA} {K : Abi I} {A : Arch} {n : Nat} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)} {pcf : I.State → Nat}

local notation "M" => ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf

/-- **The refusal is unobservable.** -/
theorem obs_cloneErr : obs [Ev.cloneErr] = [] := rfl

/-- **One running slot leaves none dormant.** -/
theorem nodormant_one {x : KState} (h1 : x.slots.size = 1) (hr : x.runs 0 = true) :
    ∀ j : Nat, x.slots[j]? ≠ some Slot.dormant := by
  intro j hj
  have hlt : j < x.slots.size := (Array.getElem?_eq_some_iff.mp hj).1
  rw [h1] at hlt
  obtain rfl : j = 0 := Nat.lt_one_iff.mp hlt
  simp [KState.runs, hj] at hr

/-- **With no dormant slot, a step at a `clone` is its refusal**: thread
`tid` (in state `t`, at a `clone` call, at no transfer site) steps only by
the kernel's `-EAGAIN`/`-ENOMEM` return, with the event `cloneErr`. -/
theorem clone_step_nodormant {μ : Marks} {tid : Nat} {d d' : (M).Cfg} {t : Thread I}
    {stack tls : Nat} {es : List Ev} (hdor : ∀ j : Nat, d.2.slots[j]? ≠ some Slot.dormant)
    (ht : d.1.threads[tid]? = some t) (ha : K.atSys t.st = true)
    (hcall : callOf K t = some (.clone stack tls)) (hns : ∀ k, ¬ (M).AtSite μ k d tid)
    (h : (M).Step μ tid d es d') :
    es = [.cloneErr] ∧ ∃ r, (r = neg eagain ∨ r = neg enomem) ∧
      d' = (d.1.withThread tid (retThread K t r) d.1.mem, d.2) := by
  cases h with
  | instr _ hna _ _ => exact absurd ⟨t, ht, ha⟩ hna
  | xfer k _ hs _ => exact absurd hs (hns k)
  | spawn _ hy =>
    obtain ⟨j, r, h1, -⟩ := hy
    have h1 : spawnStep K tid d j r = some d' := h1
    unfold spawnStep at h1
    erw [ht] at h1
    simp only [hcall] at h1
    split at h1
    · cases h1
    · split at h1
      · rename_i hc; exact absurd hc.1 (hdor j)
      · cases h1
  | sys _ hy _ _ _ =>
    obtain ⟨p, h1, -⟩ := hy
    have h1 : sysStep K A tid d p = some (es, d') := h1
    unfold sysStep at h1
    erw [ht] at h1
    simp only [hcall] at h1
    split at h1
    · cases h1
    · cases p with
      | byte rd => cases h1
      | abort k => cases h1
      | ret r =>
        simp only at h1
        split at h1
        · rename_i hr
          simp only [back] at h1
          obtain ⟨rfl, rfl⟩ := h1
          exact ⟨rfl, r, hr, rfl⟩
        · cases h1

/-- **The lifted configuration at a `clone` has progress** (whatever the
extra thread `u`: its slot is dormant): `d`'s one thread `t` runs, is at a `clone` call, is not halted and has no promise; the
extra slot is dormant, so the `clone` does not fault (`dormants_up`), and
the kernel's refusal (`sys_cloneErr`) is a step. -/
theorem clone_progress_up {μ : Marks} {d : Config I × KState} {u : Thread I} {t : Thread I}
    {stack tls : Nat} (hn : d.1.threads.size = d.2.slots.size)
    (hth : d.1.threads = #[t]) (hr : d.2.runs 0 = true) (hx : d.2.exited = none)
    (ha : K.atSys t.st = true) (hcall : callOf K t = some (.clone stack tls)) (hnh : t.halted = false)
    (hp : t.prom = []) :
    (M).Progress μ (up d u) := by
  have ht : d.1.threads[0]? = some t := by rw [hth]; rfl
  have h1 : d.1.threads.size = 1 := by rw [hth]; rfl
  have hs1 : d.2.slots.size = 1 := hn ▸ h1
  have ht0 : 0 < d.1.threads.size := by rw [h1]; exact Nat.zero_lt_one
  have hs0 : 0 < d.2.slots.size := by rw [hs1]; exact Nat.zero_lt_one
  have htu : (up d u).1.threads[0]? = some t := by
    show (upC d.1 u).threads[0]? = some t
    rw [upC_get ht0]; exact ht
  have hru : (up d u).2.runs 0 = true := by
    show (upX d.2).runs 0 = true
    rw [upX_runs hs0]; exact hr
  have hxu : (up d u).2.exited = none := by show (upX d.2).exited = none; rw [upX_exited]; exact hx
  have hruns : (M).runs (up d u) 0 :=
    ⟨⟨t, htu⟩, hxu, by show ¬ ((up d u).2.runs 0 = false); rw [hru]; simp⟩
  have hready : ready K 0 (up d u) t = true := ready_of K ha hru hxu
  have hstep : ∃ es c', (M).Step μ 0 (up d u) es c' :=
    ⟨_, _, .sys hruns (sys_cloneErr (K := K) (μ := μ) A n htu hready hp hcall) (by simp)
      (fun k hk => by simp at hk) (fun e he => by simp at he)⟩
  have hsys : (M).atSys (up d u) 0 := ⟨t, htu, ha⟩
  refine ⟨?_, .inr ⟨⟨0, hxu, hruns.2.2, t, htu, fun h => by rw [hnh] at h; cases h.1⟩, fun tid hl => ?_⟩⟩
  · rintro (⟨tid, m, ⟨⟨t1, ht1⟩, -, hd⟩, hns, -⟩ | ⟨tid, hf⟩ | ⟨tid, t1, e, ht1, hr1, -, hns, -⟩)
    · -- an instruction fault needs a thread off a system call: only thread 0 runs
      have hr1 : (upX d.2).runs tid = true := by
        simpa [Kernel.hooks, up] using hd
      have hlt := lt_of_runs_up hr1
      rw [hs1] at hlt
      obtain rfl : tid = 0 := Nat.lt_one_iff.mp hlt
      exact hns hsys
    · unfold faultAt at hf
      split at hf
      · rename_i t1 ht1
        simp only [Bool.and_eq_true, Bool.or_eq_true] at hf
        have hr1 := hf.1.1
        have hlt := lt_of_runs_up hr1
        rw [hs1] at hlt
        obtain rfl : tid = 0 := Nat.lt_one_iff.mp hlt
        obtain rfl : t = t1 := Option.some.inj (htu.symm.trans ht1)
        rcases hf.2 with ⟨-, h3⟩ | h3
        · rw [hcall] at h3
          have hd := dormants_up d.2
          simp only [up] at h3
          rw [hd] at h3; cases h3
        · rw [hnh] at h3; cases h3
      · cases hf
    · have hlt := lt_of_runs_up hr1
      rw [hs1] at hlt
      obtain rfl : tid = 0 := Nat.lt_one_iff.mp hlt
      obtain rfl : t = t1 := Option.some.inj (htu.symm.trans ht1)
      rw [ha] at hns; cases hns
  · obtain ⟨-, hd, -⟩ := hl
    have hr1 : (upX d.2).runs tid = true := by
      simpa [Kernel.hooks, up] using hd
    have hlt := lt_of_runs_up hr1
    rw [hs1] at hlt
    obtain rfl : tid = 0 := Nat.lt_one_iff.mp hlt
    exact hstep

end Spike.Lib.CloneOne
