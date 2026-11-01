/-
**hello.w on AArch64: a step from `Post` to `Post` keeps `CertAll`** (row
B8-genC; `HelloAssembly.HelloRowsW.cert_step`, the twins of
`WakeCert.no_site_of_post` / `certAll_step_of` and `WakeEnv.post_bnd` /
`henv_of` at hello's worker data `PT1h` and kernel relation `KRH`).

wake's proofs read the worker's data only for its states' being at no
transfer site (`WCompatH.noSite`) and the threads' bounds (the core), the
kernel relation only for its slot conjuncts (`KRH`'s are `KR`'s).

- `no_site_of_postH`, `certAll_step_ofH`, `post_bndH`, `henv_ofH`: as wake's
  (without the `H`).
- `cert_stepH`: `HelloRowsW.cert_step`'s statement, given `hconv` (row
  B8-genV, `HelloRowsW.hconv`).
-/
import Spike.Lib.WakeEnv
import Spike.Lib.HelloAssembly

namespace Spike.Lib.HelloCert

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeW1 Spike.Lib.WakeCert Spike.Lib.WakeEnv
open Spike.Lib.HelloW1 (WSideH PT1h PartsH post_partsH WCompatH)
open Spike.Lib.HelloKRE (KRHE)
open Spike.Lib.A64HelloWriteK (KRH)

variable {Q : WakeRel} {D : WSideH Q.ι} {M : WakeM0.MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch} {AbW : isaLSE2.State → Prop}


/-- **The step of a running thread from `Post` is neither a `clone` nor a
range transfer**, and the thread is in its side's invariant (at no
transfer site). -/
theorem no_site_of_postH (hC : WCompatH Q D μ Λ arch AbW) (hC0 : WakeM0.WCompat0 Q M μ Λ)
    (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = KRHE D r0 r1) {t : Cfg} {s : TermRun.Cfg}
    (hP : Q.Post Λ t s) (hx : t.2.exited = none) {tid : Nat} {th : Thread isaLSE2}
    (ht : t.1.threads[tid]? = some th) : siteAt abi μ th.st = none := by
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hT, hS, -, h0, h1, -⟩, hK⟩ := hP
  rw [hKR] at hK
  replace hK := hK.1
  simp only [WakeRel.PTw] at h0 h1
  rw [hPT0] at h0
  rw [hC.pt1] at h1
  rcases tid with _ | _ | n
  · have e : some t0 = some th := by rw [← ht, hT]; rfl
    cases e
    exact hC0.noSite0 w _ _ (h0.2.1.resolve_right (hK.2.2.2.2.1 hx s0 (by rw [hS]; rfl)))
  · have e : some t1 = some th := by rw [← ht, hT]; rfl
    cases e
    obtain ⟨_, _, hw⟩ := HelloEmitPh.PT1hE.wi h1
    exact hC.noSite w _ _ _ hw
  · rw [hT] at ht; simp at ht

/-- **`cert_step`**: a step from `Post` to `Post` keeps `CertAll`. The
stepping thread by the semantics (`CertOkC`), made append-free at the
post-state by `hconv`; the other by `henv` (transports of
`CertOkCNA`). -/
theorem certAll_step_ofH (hC : WCompatH Q D μ Λ arch AbW) (hC0 : WakeM0.WCompat0 Q M μ Λ)
    (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = KRHE D r0 r1)
    (henv : ∀ tid t es t' s i th, Q.Post Λ t s → i ≠ tid → (machine (kernel 2)).Step μ tid t es t' →
      t.2.exited = none → t'.2.exited = none →
      t.1.threads[i]? = some th → t'.1.threads[i]? = some th → t.2.runs i = true → th.prom ≠ [] →
      CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t.2 i) i th t.1.mem →
      CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t'.2 i) i th t'.1.mem)
    (hconv : ∀ t s, Q.Post Λ t s → CertConv μ t) :
    ∀ tid t es t' s s', Q.Post Λ t s → CertAll μ t → (machine (kernel 2)).Step μ tid t es t' →
      Q.Post Λ t' s' → CertAll μ t' := by
  intro tid t es t' s s' hP hca hs hP' hx'
  obtain ⟨⟨th, ht⟩, hx, -⟩ := hs.runs
  have hx : t.2.exited = none := hx
  have hlt : tid < t.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  -- the other thread: kept, transported by `henv`
  have hother : ∀ i th', i ≠ tid → t'.1.threads[i]? = t.1.threads[i]? →
      (t'.2.runs i = true → t.2.runs i = true) → t'.1.threads[i]? = some th' → t'.2.runs i = true →
      th'.prom ≠ [] → CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t'.2 i) i th' t'.1.mem := by
    intro i th' hne he hr ht' hr' hp
    have ht0 : t.1.threads[i]? = some th' := he ▸ ht'
    exact henv tid t es t' s i th' hP hne hs hx hx' ht0 ht' (hr hr') hp (hca hx i th' ht0 (hr hr') hp)
  rcases step1_cases ht hs with ⟨-, -, outs, o, -, -, rfl, hco⟩ | ⟨-, w, -, rfl, hco⟩ | ⟨p, hsy, hca'⟩ |
      ⟨-, j, r, hsp⟩ | ⟨-, k, hk, -⟩
  · intro i th' ht' hr' hp
    by_cases hi : i = tid
    · subst hi
      have e : (t.1.withThread i o.thread o.mem).threads[i]? = some o.thread := by
        rw [withThread_get, ite_eq_left ⟨rfl, hlt⟩]
      cases (show some o.thread = some th' from e.symm.trans ht')
      exact hconv _ _ hP' hx' _ _ ht' hr' hp hco
    · exact hother i th' hi (withThread_ne hi) id ht' hr' hp
  · intro i th' ht' hr' hp
    by_cases hi : i = tid
    · subst hi
      have e : (t.1.withThread i (Live.Sem.promThread th t.1.mem w) (t.1.mem.append w).1).threads[i]? =
          some (Live.Sem.promThread th t.1.mem w) := by
        rw [withThread_get, ite_eq_left ⟨rfl, hlt⟩]
      cases (show some (Live.Sem.promThread th t.1.mem w) = some th' from e.symm.trans ht')
      exact hconv _ _ hP' hx' _ _ ht' hr' hp hco
    · exact hother i th' hi (withThread_ne hi) id ht' hr' hp
  · obtain ⟨-, hth, hsl⟩ := sysStep_frame hsy
    intro i th' ht' hr' hp
    by_cases hi : i = tid
    · subst hi
      exact hconv _ _ hP' hx' _ th' ht' hr' hp (hca' th' ht')
    · refine hother i th' hi (hth i hi) (fun h => ?_) ht' hr' hp
      simp only [KState.runs] at h ⊢
      rw [← hsl i hi]
      exact h
  · exfalso
    obtain ⟨hd, hj⟩ := spawnStep_dormant hsp
    obtain ⟨w, ⟨t0, t1, -, -, -, -, -, hT, -⟩, hK⟩ := hP
    rw [hKR] at hK
    replace hK := hK.1
    obtain ⟨-, ⟨j0, h0⟩, h1, -⟩ := hK
    rw [hT] at hj
    rcases j with _ | _ | j
    · rw [h0] at hd; cases hd
    · exact h1 hd
    · simp at hj; omega
  · exfalso
    obtain ⟨a, ha, t2, ht2, hpc⟩ := hk
    cases (show some t2 = some th from ht2.symm.trans ht)
    have hn := siteAt_eq_none_iff.mp (no_site_of_postH hC hC0 hPT0 hKR hP hx ht)
    subst hpc
    cases k
    · exact hn.1 ha
    · exact hn.2 ha


/-- **At `Post` every thread is bounded by the memory.** -/
theorem post_bndH (hC : WCompatH Q D μ Λ arch AbW) {t : Cfg} {s : TermRun.Cfg} (hP : Q.Post Λ t s) {i : Nat}
    {th : Thread isaLSE2} (ht : t.1.threads[i]? = some th) : th.Bnd t.1.mem.last := by
  rcases HelloEmitPh.post_partsHE hC.pt1 hP with ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ |
    ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h, -⟩
  · rw [h.th] at ht
    rcases i with _ | _ | n
    · cases (show some t0 = some th from ht)
      exact h.core.bnd0
    · cases (show some t1 = some th from ht)
      exact h.core.bnd1
    · simp at ht
  · rw [h.th] at ht
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
theorem henv_ofH (hC : WCompatH Q D μ Λ arch AbW) (hC0 : WakeM0.WCompat0 Q M μ Λ)
    (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = KRHE D r0 r1) :
    ∀ tid t es t' s i th, Q.Post Λ t s → i ≠ tid → (machine (kernel 2)).Step μ tid t es t' →
      t.2.exited = none → t'.2.exited = none →
      t.1.threads[i]? = some th → t'.1.threads[i]? = some th → t.2.runs i = true → th.prom ≠ [] →
      CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t.2 i) i th t.1.mem →
      CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t'.2 i) i th t'.1.mem := by
  intro tid t es t' s i th hP _ hs hx _ ht _ _ _ hc
  have hb := post_bndH hC hP ht
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
    replace hK := hK.1
    obtain ⟨-, ⟨j0, h0⟩, h1, -⟩ := hK
    rw [hT] at hj
    rcases j with _ | _ | j
    · rw [h0] at hd; cases hd
    · exact h1 hd
    · simp at hj; omega
  · exfalso
    obtain ⟨a, ha, t2, ht2, hpc⟩ := hk
    cases (show some t2 = some t1 from ht2.symm.trans h1)
    have hn := siteAt_eq_none_iff.mp (no_site_of_postH hC hC0 hPT0 hKR hP hx h1)
    subst hpc
    cases k
    · exact hn.1 ha
    · exact hn.2 ha

/-- info: 'Spike.Lib.HelloCert.henv_ofH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms henv_ofH

/-! ## At `HelloCompat` -/

open Spike.Lib.HelloW1Store (NoWrite)
open Spike.Lib.HelloAssembly (HelloCompat)

/-- **`HelloRowsW.cert_step`** given `hconv`: `certAll_step_ofH` with
`henv_ofH`. -/
theorem cert_stepH {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0} {hem : NoWrite D}
    (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = KRHE D r0 r1) (hC : HelloCompat Q D M μ Λ arch AbW hcw hem)
    (hconv : ∀ t s, Q.Post Λ t s → CertConv μ t) :
    ∀ tid t es t' s s', Q.Post Λ t s → CertAll μ t → (machine (kernel 2)).Step μ tid t es t' →
      Q.Post Λ t' s' → CertAll μ t' :=
  certAll_step_ofH hC.1 hC.2.2.2 hPT0 hKR (henv_ofH hC.1 hC.2.2.2 hPT0 hKR) hconv

/-- info: 'Spike.Lib.HelloCert.cert_stepH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cert_stepH

end Spike.Lib.HelloCert
