/-
**The thread that does not step keeps its append-free certification**
(`WakeAssembly`'s `henv`, AArch64; `henv_of`).

From `Post`, a step of thread `tid` (`Spike.Lib.WakeW1.step1_cases`) is an
instruction or a promise, which only append to memory and keep the kernel
state, or a system call, which keeps memory and changes only `tid`'s slot and
`exited`; a `clone` and a range transfer are impossible from `Post`
(`WakeCert.spawnStep_dormant` with `KR`, `WakeCert.no_site_of_post`). Thread
`i ≠ tid`'s `CertOkCNA` is carried across by `CertReplay.certOkCNA_memExt` (its
thread is bounded by the memory, `Inv2Core.bnd0`/`bnd1`) and
`CertReplay.certSem_kframe` (`CertReplay.sysStep_kframe`). Nothing about either
side's program is used beyond `Post`, so this serves main and the worker
alike.
-/
import Spike.Lib.WakeCert
import Spike.Lib.WakeW1Keep
import Spike.Lib.CertReplayExt
import Spike.Lib.CertReplayK

namespace Spike.Lib.WakeEnv

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeW1 Spike.Lib.WakeCert

variable {Q : WakeRel} {D : WSide Q.ι} {M : WakeM0.MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}

/-- **At `Post` every thread is bounded by the memory.** -/
theorem post_bnd (hC : WCompat Q D μ Λ arch) {t : Cfg} {s : TermRun.Cfg} (hP : Q.Post Λ t s) {i : Nat}
    {th : Thread isaLSE2} (ht : t.1.threads[i]? = some th) : th.Bnd t.1.mem.last := by
  obtain ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ := post_parts hC hP
  rw [h.th] at ht
  rcases i with _ | _ | n
  · cases (show some t0 = some th from ht)
    exact h.core.bnd0
  · cases (show some t1 = some th from ht)
    exact h.core.bnd1
  · simp at ht

/-- An instruction only appends to memory. -/
theorem stepOne_prefix {t : Thread isaLSE2} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Kraken.Promising.Outcome isaLSE2))} (hs : stepOne Arch.armv8 t tid mem = some outs)
    {o : Kraken.Promising.Outcome isaLSE2} (ho : .ok o ∈ outs) : mem.Prefix o.mem := by
  obtain ⟨hi, hm⟩ := stepOne_ext Arch.armv8 hs ho
  exact ⟨hi, by rw [hm]; exact List.prefix_append _ _⟩

/-- **`henv`**: from `Post`, a step of thread `tid` keeps the append-free
certification of every other thread whose state it keeps. -/
theorem henv_of (hC : WCompat Q D μ Λ arch) (hC0 : WakeM0.WCompat0 Q M μ Λ)
    (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = WakeKR.KR r0 r1) :
    ∀ tid t es t' s i th, Q.Post Λ t s → i ≠ tid → (machine (kernel 2)).Step μ tid t es t' →
      t.2.exited = none → t'.2.exited = none →
      t.1.threads[i]? = some th → t'.1.threads[i]? = some th → t.2.runs i = true → th.prom ≠ [] →
      CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t.2 i) i th t.1.mem →
      CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t'.2 i) i th t'.1.mem := by
  intro tid t es t' s i th hP _ hs hx _ ht _ _ _ hc
  have hb := post_bnd hC hP ht
  obtain ⟨⟨t1, h1⟩, -, -⟩ := hs.runs
  rcases step1_cases h1 hs with ⟨-, -, outs, o, hso, ho, rfl, -⟩ | ⟨-, w, -, rfl, -⟩ | ⟨p, hsy, -⟩ |
      ⟨-, j, r, hsp⟩ | ⟨-, k, hk, -⟩
  · exact CertReplay.certOkCNA_memExt hb (stepOne_prefix hso ho) hc
  · exact CertReplay.certOkCNA_memExt hb (Memory.Prefix.append _ _) hc
  · rw [CertReplay.certSem_kframe (CertReplay.sysStep_kframe hsy), (sysStep_frame hsy).1]
    exact hc
  · exfalso
    obtain ⟨hd, hj⟩ := spawnStep_dormant hsp
    obtain ⟨w, ⟨t0, t1, -, -, -, -, -, hT, -⟩, hK⟩ := hP
    rw [hKR] at hK
    obtain ⟨-, ⟨j0, h0⟩, h1, -⟩ := hK
    rw [hT] at hj
    rcases j with _ | _ | j
    · rw [h0] at hd; cases hd
    · exact h1 hd
    · simp at hj; omega
  · exfalso
    obtain ⟨a, ha, t2, ht2, hpc⟩ := hk
    cases (show some t2 = some t1 from ht2.symm.trans h1)
    have hn := siteAt_eq_none_iff.mp (no_site_of_post hC hC0 hPT0 hKR hP hx h1)
    subst hpc
    cases k
    · exact hn.1 ha
    · exact hn.2 ha

/-- info: 'Spike.Lib.WakeEnv.henv_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms henv_of

end Spike.Lib.WakeEnv
