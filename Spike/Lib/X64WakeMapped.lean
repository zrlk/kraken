/-
**wake.w on x86-64: no unmapped access after the spawn**
(`WakeAssembly.wake_obligations`' `hmapped`, for `post_progress`): while the
process runs, no instruction a running thread of a `Post` configuration
executes off a system call touches a location the kernel state leaves
unmapped.

The per-state fact is hello1's (`X64Consumer.SFacts.mapped`): the
instruction touches only locations mapped in the loaded kernel state without
the entry stack (`X64Consumer.K0`: the layout's data, heap, stack pool and
pinned region read-write, its code and `.rodata` read-only). Private memory
(the stacks) is not an event, so it is not touched. Under the run invariant
(`X64WakeRunInv.RunInv`) the kernel state maps every region `K0` maps
(`mapped_of_K0`), so the fact carries over.

- `mapped_of_K0`: a location mapped in `K0` is mapped under `RunInv`.
- `noTouch_of_K0`: no unmapped touch, from `K0` to `RunInv`.
- `hmapped_of`: `hmapped` from main's invariant (`hM`, main's side)
  and the worker's (`hW`, the worker's side) touching only what `K0`
  maps; main's source after its return (`wlRet`) is excluded while the
  process runs (`KR`'s `MainLive`).

x86-64 twin of `Spike/Lib/WakeMapped.lean` (same names, namespaces with the
`X64` prefix).
-/
import Spike.Lib.X64WakeRunInv
import Spike.Lib.X64Consumer
import Spike.Lib.X64WakeKR
import Spike.Lib.X64WakeM0
import Spike.Lib.X64WakeW1

namespace Spike.Lib.X64WakeMapped

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.X64Consumer (K0)

/-- **A location mapped in `K0` is mapped under the run invariant**: the
kernel state maps the loaded regions (and the held ranges). -/
theorem mapped_of_K0 {Λ : Scc.Sem.Layout} {E : Entry} {t : Config isa × KState}
    (hr : X64WakeRunInv.RunInv Λ E t) {w : Bool} {l : Loc} (h : Kernel.mapped (K0 Λ) w l = true) :
    Kernel.mapped t.2 w l = true := by
  unfold Kernel.mapped at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro i hi
  obtain ⟨r, hr', hc⟩ := List.any_eq_true.mp (h i hi)
  refine List.any_eq_true.mpr ⟨r, ?_, hc⟩
  simp only [mappedRegions, K0, List.mem_append] at hr' ⊢
  rw [hr.2.1, hr.2.2]
  simp only [KState.init, List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
  cases w <;> simp_all
  · rcases hr' with (h | h | h | h) | h | h <;> simp [h]
  · rcases hr' with h | h | h | h <;> simp [h]

/-- **No unmapped touch carries over** from `K0` to a kernel state under
the run invariant. -/
theorem noTouch_of_K0 {Λ : Scc.Sem.Layout} {E : Entry} {t : Config isa × KState}
    (hr : X64WakeRunInv.RunInv Λ E t) {σ : Type} {e : EvTree σ}
    (h : ¬ Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e) :
    ¬ Touches (fun l w => Kernel.mapped t.2 w l = false) e := fun ht =>
  h (Consumer1.touches_mono (fun l w hf => by
    cases hk : Kernel.mapped (K0 Λ) w l
    · rfl
    · rw [mapped_of_K0 hr hk] at hf; cases hf) ht)

/-- **`hmapped`**: main's invariant (`hM`) and the worker's (`hW`) touch
only locations `K0` maps off a system call; at wake's per-thread relations
(`hPT0`, `hPT1`) and kernel relation (`hKR`), while the process runs. -/
theorem hmapped_of {Q : WakeRel} {M : X64WakeM0.MSide Q.ι} {D : X64WakeW1.WSide Q.ι} {r0 r1 : Q.ι → Range}
    (hPT0 : Q.PT0 = X64WakeM0.PT0 M) (hPT1 : Q.PT1 = X64WakeW1.PT1 D) (hKR : Q.KR = X64WakeKR.KR r0 r1)
    {Λ : Scc.Sem.Layout} {E : Entry}
    (hM : ∀ w s c, M.Mi w s c → abi.atSys s = false → ∀ e, isa.exec s = some e →
      ¬ Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e)
    (hW : ∀ w s c, D.Wi w s c → abi.atSys s = false → ∀ e, isa.exec s = some e →
      ¬ Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e) :
    ∀ t s, Q.Post Λ t s → X64WakeRunInv.RunInv Λ E t → t.2.exited = none →
      ∀ tid th e, t.1.threads[tid]? = some th → t.2.runs tid = true → abi.atSys th.st = false →
        isa.exec th.st = some e → ¬ Touches (fun l w => Kernel.mapped t.2 w l = false) e := by
  intro t s hP hr hx tid th e hth _ hs he
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hT, hS, -, h0, h1, -⟩, hK⟩ := hP
  rw [hKR] at hK
  have hm := X64WakeKR.kr_live hK
  simp only [WakeRel.PTw, ite_true, show (1 : Nat) ≠ 0 from by decide, ite_false] at h0 h1
  rw [hT] at hth
  rcases tid with _ | _ | tid
  · cases (show t0 = th by simpa using hth)
    rw [hPT0] at h0
    obtain ⟨hmi, -⟩ := h0.2
    have hl : s0.term ≠ WakeMLive.wlRet := hm hx s0 (by rw [hS]; rfl)
    have hmi' : M.Mi w th.st (Ctl.of s0) := by
      first
        | exact hmi.resolve_right hl
        | exact hmi
    exact noTouch_of_K0 hr (hM w _ _ hmi' hs e he)
  · cases (show t1 = th by simpa using hth)
    rw [hPT1] at h1
    exact noTouch_of_K0 hr (hW w _ _ h1.1 hs e he)
  · simp at hth

/-- info: 'Spike.Lib.X64WakeMapped.hmapped_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMapped.hmapped_of

end Spike.Lib.X64WakeMapped
