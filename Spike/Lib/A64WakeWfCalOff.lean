/-
**wake.w's `wc_main` callees' written words off the arena** (AArch64): the
premises `hoffN`, `hoffP`, `hoffH` of `A64WakeWfCalW1`'s `reserveW_wf` /
`tcbWG_wf` at `Ly := RuntimeLayout.ofPlaceW hpw i` and wake's arena
`WakeOD.arW hpw i` (`Rt.arOf`: the heap's base, `allocCells` cells, the
counter at `scc_rt_heap_use`). Each word lies in `.data` or `pinned`, both
disjoint from the heap (A1), which holds the arena (A8's `heapSizeOk`), and
apart from the counter's word.

- `off_of`: a word in `.data` or `pinned`, not the counter's address, is off
  the arena and not its counter word.
- `hoffP_W`: `scc_rt_pinned_next` (a runtime word: `words_mapped`, A8's
  `ctrSep`).
- `hoffPin_W`, `hoffH_W`, `hoffT_W`: a word of `[pinA, pinA + 168)`, in
  `pinned` (`hpin2`), the counter in `.data` (`CtrZ`); the second TCB's
  header `pinA + 96` and its id word `t2 + 56 = pinA + 160`.
- `NtOff`, `ntOff_of_a13`, `hoffN_W`, `sepN_W`, `hmN_W`: `scc_rt_nthreads` is
  no runtime word of A8; A13's data part (`Spawn.A64.a13data`, decided at the
  concrete layout) places it (`NtOff`: a data symbol, `wordOk`, apart from
  the counter and the four counters); it is then off the arena, none of the
  counters and mapped.
-/
import Spike.Lib.WakeOD
import Spike.Lib.WakeTcbArea

namespace Spike.Lib.A64.WakePh.CalWf

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Scc.Cert.Rt.A64 (symLab rtA wordOk WordSep)
open Scc.Cert.PlaceOK (heapUseOf allocCells)

/-- **`scc_rt_nthreads` placed apart from the heap's counter**: a data
symbol of the link whose word passes `wordOk` (below `2 ^ 32`, aligned, clear
of the stack pool, its bytes in `.data` or `pinned`) and is apart from the
allocator's counter and the four counters of the runtime
(`Spawn.A64.a13data` at the one word). -/
def NtOff (Λ : Scc.Sem.Layout) (o : Scc.Cert.PlaceOK.A64.Out) : Bool :=
  (symLab Λ.code.lo o.prog (Scc.Sem.loadSyms Λ o.secs.rodata) "scc_rt_nthreads").isSome &&
    wordOk Λ (rtA Λ o.prog o.secs "scc_rt_nthreads") &&
    decide (WordSep (rtA Λ o.prog o.secs "scc_rt_nthreads") (BitVec.ofNat 64 (heapUseOf Λ))) &&
    ["scc_rt_pinned_next", "scc_rt_stack_lock", "scc_rt_stack_free_n", "scc_rt_stack_next"].all
      fun x => decide (WordSep (rtA Λ o.prog o.secs "scc_rt_nthreads") (rtA Λ o.prog o.secs x))

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

/-- **A word in `.data` or `pinned`, not at the counter, is off wake's
arena and not its counter word.** -/
theorem off_of {x : BitVec 64} (hx : (Ly).Λ.data.contains x.toNat ∨ (Ly).Λ.pinned.contains x.toNat)
    (hc : x ≠ BitVec.ofNat 64 (heapUseOf (Ly).Λ)) :
    ¬ ((WakeOD.arW hpw i).heap ≤ x.toNat ∧ x.toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨x, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc := by
  have hh : (WakeOD.arW hpw i).heap = (Ly).Λ.heap.lo := rfl
  have hn : (WakeOD.arW hpw i).cells = allocCells := rfl
  have hs : 16 * allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW (Spike.Lib.PlaceW.link i hpw)
  obtain ⟨-, -, -, hdh, -, -, -, -, hph, -⟩ := (Spike.Lib.PlaceW.wf_link_of_placeW i hpw).disjoint
  have hdh' : (Ly).Λ.data.Disjoint (Ly).Λ.heap := hdh
  have hph' : (Ly).Λ.heap.Disjoint (Ly).Λ.pinned := hph
  simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint] at hx hdh' hph'
  refine ⟨by rw [hh, hn]; omega, fun he => hc (congrArg Loc.addr he)⟩

/-- Two words apart are distinct. -/
theorem ne_of_sep {a b : BitVec 64} (h : WordSep a b) : a ≠ b := fun he => by
  unfold WordSep at h; rw [he] at h; omega

/-- **`tcbWG_wf`'s `hoffP`**: `scc_rt_pinned_next` is off wake's arena. -/
theorem hoffP_W :
    ¬ ((WakeOD.arW hpw i).heap ≤ (Ly).pnA.toNat ∧
        (Ly).pnA.toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨(Ly).pnA, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc :=
  off_of hpw i (by simpa using ((Ly).words_mapped _ (Ly).pn_mem).2.2 0 (by decide))
    (ne_of_sep (Scc.Cert.Rt.A64.ctrSep_of_rtWordsOk (Spike.Lib.PlaceW.rtWordsOk_link_of_placeW i hpw) _
      (Ly).pn_mem))

/-- **A word of `[pinA, pinA + 168)` is off wake's arena**, given `pinned`
holds it (`hpin2`) and the counter's zeroed item (`CtrZ`, the counter in
`.data`). -/
theorem hoffPin_W (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hcz : Spike.Lib.A64.Rt.CtrZ o) {c : Nat} (hc : c + 8 ≤ 168) :
    ¬ ((WakeOD.arW hpw i).heap ≤ ((Ly).pinA + BitVec.ofNat 64 c).toNat ∧
        ((Ly).pinA + BitVec.ofNat 64 c).toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨(Ly).pinA + BitVec.ofNat 64 c, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc := by
  have ht := Spike.Lib.WakeTcbArea.pin2_toNat hpw i (c := c) (by omega)
  have hp : (Ly).Λ.pinned.contains ((Ly).pinA + BitVec.ofNat 64 c).toNat :=
    Spike.Lib.WakeTcbArea.pin2_contains hpw i hpin2 (by omega) (by omega)
  have hd : (Ly).Λ.data.contains (heapUseOf (Ly).Λ) :=
    Spike.Lib.A64.Rt.ArenaW.ctr_data_of_placeW (Spike.Lib.PlaceW.link i hpw) hcz
  have hb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 :=
    Spike.Lib.A64.Rt.ArenaW.data_below_of_placeW (Spike.Lib.PlaceW.link i hpw)
  obtain ⟨-, -, -, -, -, -, -, hdp0, -, -⟩ := (Spike.Lib.PlaceW.wf_link_of_placeW i hpw).disjoint
  have hdp : (Ly).Λ.data.Disjoint (Ly).Λ.pinned := hdp0
  refine off_of hpw i (.inr hp) fun he => ?_
  have h2 := congrArg BitVec.toNat he
  simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint] at hp hd hdp hb
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h2
  omega

/-- **`tcbWG_wf`'s `hoffH`**: the second TCB's header `scc_rt_pinned + 96`
is off wake's arena (`hoffPin_W`). -/
theorem hoffH_W (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hcz : Spike.Lib.A64.Rt.CtrZ o) :
    ¬ ((WakeOD.arW hpw i).heap ≤ ((Ly).pinA + 96#64).toNat ∧
        ((Ly).pinA + 96#64).toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨(Ly).pinA + 96#64, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc :=
  hoffPin_W hpw i hpin2 hcz (c := 96) (by decide)

/-- **`WcGLy.offT`**: the second TCB's id word `t2 + 56 = scc_rt_pinned +
160` is off wake's arena (`hoffPin_W`). -/
theorem hoffT_W (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hcz : Spike.Lib.A64.Rt.CtrZ o) :
    ¬ ((WakeOD.arW hpw i).heap ≤ (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 104#64 + 56#64).toNat ∧
        (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 104#64 + 56#64).toNat <
          (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 104#64 + 56#64, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc := by
  have e : Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 104#64 + 56#64 = (Ly).pinA + BitVec.ofNat 64 160 := by
    rw [(Ly).lab_pin, BitVec.add_assoc]; rfl
  rw [e]
  exact hoffPin_W hpw i hpin2 hcz (by decide)

/-- **`NtOff` from A13's data part** at the layout `Ly.Λ` (`Λ0` with the
immediates, which `NtOff` does not read). -/
theorem ntOff_of_a13 (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) : NtOff Λ0 o = true := by
  change NtOff (Ly).Λ o = true
  simp only [Scc.Cert.Spawn.A64.a13data, Bool.and_eq_true, List.all_cons, List.all_eq_true,
    decide_eq_true_eq] at hA13
  obtain ⟨⟨⟨⟨⟨hs, hw, -⟩, ho, -⟩, hc, -⟩, -⟩, -⟩ := hA13
  simp only [NtOff, Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq]
  have m : ∀ x, x ∈ [rtA (Ly).Λ o.prog o.secs "scc_rt_pinned_next", rtA (Ly).Λ o.prog o.secs "scc_rt_stack_next",
      rtA (Ly).Λ o.prog o.secs "scc_rt_stack_lock", rtA (Ly).Λ o.prog o.secs "scc_rt_stack_free_n"] →
      WordSep (rtA (Ly).Λ o.prog o.secs "scc_rt_nthreads") x := fun x hx =>
    ho x <| by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [Scc.Cert.Rt.A64.rtWords, List.mem_append, List.mem_cons]
      rcases hx with h | h | h | h <;> simp [h]
  exact ⟨⟨⟨hs, hw⟩, hc⟩, m _ (by simp), m _ (by simp), m _ (by simp), m _ (by simp)⟩

/-- `NtOff` places `scc_rt_nthreads`: its label is its `rtA` address,
whose word passes `wordOk` and is apart from the counter. -/
theorem ntA_of (hnt : NtOff Λ0 o = true) :
    ntA (Ly).lab = rtA Λ0 o.prog o.secs "scc_rt_nthreads" ∧ wordOk Λ0 (rtA Λ0 o.prog o.secs "scc_rt_nthreads") ∧
      WordSep (rtA Λ0 o.prog o.secs "scc_rt_nthreads") (BitVec.ofNat 64 (heapUseOf Λ0)) ∧
      WordSep (ntA (Ly).lab) (Ly).pnA ∧ WordSep (ntA (Ly).lab) (Ly).lockA ∧
      WordSep (ntA (Ly).lab) (Ly).freeNA ∧ WordSep (ntA (Ly).lab) (Ly).nextA := by
  simp only [NtOff, Bool.and_eq_true, Option.isSome_iff_exists, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true] at hnt
  obtain ⟨⟨⟨⟨a, ha⟩, hw⟩, hs⟩, h1, h2, h3, h4⟩ := hnt
  have hl : (Ly).lab "scc_rt_nthreads" = Int64.ofNat a :=
    Scc.Cert.Rt.A64.label_threadAt_of_symLab (E := Scc.Sem.Entry.linux)
      (Scc.Cert.Link.A64.symsAround_of_loadOk (Spike.Lib.PlaceW.loadOk_link_of_placeW i hpw)) ha
  have he : ntA (Ly).lab = rtA Λ0 o.prog o.secs "scc_rt_nthreads" := by simp [ntA, hl, rtA, ha]
  rw [he]
  exact ⟨rfl, hw, hs, h1, h2, h3, h4⟩

/-- **`reserveW_wf`'s `hoffN`**: `scc_rt_nthreads` is off wake's arena,
given A13's data part. -/
theorem hoffN_W (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    ¬ ((WakeOD.arW hpw i).heap ≤ (ntA (Ly).lab).toNat ∧
        (ntA (Ly).lab).toNat < (WakeOD.arW hpw i).heap + 16 * (WakeOD.arW hpw i).cells) ∧
      (⟨ntA (Ly).lab, 8⟩ : Loc) ≠ (WakeOD.arW hpw i).ctrLoc := by
  obtain ⟨he, hw, hs, -⟩ := ntA_of hpw i (ntOff_of_a13 hpw i hA13)
  simp only [wordOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true] at hw
  have h0 := hw.2 0 (by decide)
  rw [Nat.add_zero] at h0
  rw [he]
  exact off_of hpw i h0 (ne_of_sep hs)

/-- **`WcGLy.sepN`**: `scc_rt_nthreads` is none of the four counters, given
`NtOff`. -/
theorem sepN_W (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    ntA (Ly).lab ≠ (Ly).pnA ∧ ntA (Ly).lab ≠ (Ly).lockA ∧ ntA (Ly).lab ≠ (Ly).freeNA ∧
      ntA (Ly).lab ≠ (Ly).nextA := by
  obtain ⟨-, -, -, h1, h2, h3, h4⟩ := ntA_of hpw i (ntOff_of_a13 hpw i hA13)
  exact ⟨ne_of_sep h1, ne_of_sep h2, ne_of_sep h3, ne_of_sep h4⟩

/-- **`reserveW_wf`'s `hmN`**: `scc_rt_nthreads` is mapped, given A13's data part. -/
theorem hmN_W (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) (w : Bool) :
    Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) w ⟨ntA (Ly).lab, 8⟩ = true := by
  obtain ⟨he, hw, -⟩ := ntA_of hpw i (ntOff_of_a13 hpw i hA13)
  simp only [wordOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true] at hw
  rw [he]
  exact Spike.Lib.A64Consumer.mapped_K0_of_mem fun j hj => hw.2 j hj

end Place

/-- info: 'Spike.Lib.A64.WakePh.CalWf.hoffP_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hoffP_W

/-- info: 'Spike.Lib.A64.WakePh.CalWf.hoffH_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hoffH_W

/-- info: 'Spike.Lib.A64.WakePh.CalWf.hoffT_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hoffT_W

/-- info: 'Spike.Lib.A64.WakePh.CalWf.sepN_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sepN_W

/-- info: 'Spike.Lib.A64.WakePh.CalWf.ntOff_of_a13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ntOff_of_a13

/-- info: 'Spike.Lib.A64.WakePh.CalWf.hoffN_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hoffN_W

/-- info: 'Spike.Lib.A64.WakePh.CalWf.hmN_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hmN_W

end Spike.Lib.A64.WakePh.CalWf
