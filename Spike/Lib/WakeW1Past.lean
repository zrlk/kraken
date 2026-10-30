/-
**Past its store the worker holds no promise inside a placed label**
(the caveat of the worker's certification
transport, `CertReplay`).

A target promise of the worker inside a placed label is mirrored (`prom_tp`)
and, since no target promise is unmirrored (`tq = []`), is the image of a
source message (`mem_onto`); by `prom_corr` that message is a source promise,
so main's (`WCompatX.sp0`: none) or the worker's; past its store point the
source worker has none (`Parts.past_noProm`).

- `Parts.past_noLabProm`: at the source store point (`wkUnpark` or done);
- `Parts.pastT_noLabProm`: at the target store point (`passT`, `WCompat.pass`);
- `Parts.pastT_noProm_cT`: in particular no promise to the flag word `cT`;
- `post_pastT_noProm_cT`: the same from `Post`.
-/
import Spike.Lib.WakeW1Rt

namespace Spike.Lib.WakeW1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt

variable {Q : WakeRel} {D : WSide Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}

namespace Parts

variable {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **Past its source store point the worker has no promise inside a placed
label.** -/
theorem past_noLabProm (hC : WCompat Q D μ Λ arch) (hx : WCompatX Q D)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hpast : s1.term = wkUnpark ∨ s1.term = .ret .unit)
    {k : Nat} (hk : k ∈ t1.prom) {m : Msg} (hm : t.1.mem.get? k = some m) :
    ¬ InLabel (Q.SR w).lbl (Q.SR w).lsize m.loc := by
  intro hin
  have htp : k ∈ tp := h.core.prom_tp k m (.inr hk) hm hin
  obtain ⟨kp, -, hts⟩ := (h.core.mem.mem_onto k m hm hin).resolve_right (by simp)
  have hsp : kp ∈ sp := (h.core.mem.prom_corr kp k hts (h.core.mem.tp_le k htp).1).mpr htp
  rcases (h.core.sp_prom kp).mp hsp with h0 | h1
  · rw [hx.sp0 w _ _ _ _ h.pt0] at h0; cases h0
  · rw [h.past_noProm hC hpast] at h1; cases h1

/-- **Past its target store point** (`passT`) **the worker has no promise
inside a placed label.** -/
theorem pastT_noLabProm (hC : WCompat Q D μ Λ arch) (hx : WCompatX Q D)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hpass : (Q.C w).passT t1.st)
    {k : Nat} (hk : k ∈ t1.prom) {m : Msg} (hm : t.1.mem.get? k = some m) :
    ¬ InLabel (Q.SR w).lbl (Q.SR w).lsize m.loc :=
  h.past_noLabProm hC hx ((hC.pass w t1.st (Ctl.of s1) h.pt1.1).mp hpass) hk hm

/-- **Past its target store point the worker has no promise to the flag
word `cT`.** -/
theorem pastT_noProm_cT (hC : WCompat Q D μ Λ arch) (hx : WCompatX Q D) (hwf : Λ.WF)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hpass : (Q.C w).passT t1.st)
    {k : Nat} (hk : k ∈ t1.prom) {m : Msg} (hm : t.1.mem.get? k = some m) : m.loc ≠ (Q.C w).cT := by
  intro hl
  obtain ⟨a, ha, hwa, ho⟩ := hC.cT w
  refine h.pastT_noLabProm hC hx hpass hk hm ?_
  rw [hl, ha]
  exact inLabel_wordLoc h.core.mem hwf hwa ho

end Parts

/-- **From `Post`: past its target store point the worker has no promise to
`cT`.** -/
theorem post_pastT_noProm_cT (hC : WCompat Q D μ Λ arch) (hx : WCompatX Q D) (hwf : Λ.WF)
    {t : Cfg} {s : TermRun.Cfg} (hP : Q.Post Λ t s) :
    ∃ w, ∀ t1, t.1.threads[1]? = some t1 → (Q.C w).passT t1.st →
      ∀ k ∈ t1.prom, ∀ m : Msg, t.1.mem.get? k = some m → m.loc ≠ (Q.C w).cT := by
  obtain ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ := post_parts hC hP
  refine ⟨w, fun t1' ht1 hpass k hk m hm => ?_⟩
  cases (show some t1 = some t1' from h.t1_get.symm.trans ht1)
  exact h.pastT_noProm_cT hC hx hwf hpass hk hm

/-- info: 'Spike.Lib.WakeW1.post_pastT_noProm_cT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_pastT_noProm_cT

end Spike.Lib.WakeW1
