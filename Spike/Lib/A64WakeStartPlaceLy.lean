/-
**The layout premises of `StartPlace.wake_start_wc_place` at wake's
placed output** (AArch64): at the runtime's layout
`Ly := RuntimeLayout.ofPlaceW hpw i` of an output with wake's placement
facts, the premises `hp`, `hlo`, `hro`, `hfree`, `hcT`, `hax` from
`PlaceW` and the root's instance facts that `WakeFinalCAW.wake_finalCA_genW`
already carries (the loader's parses `hpa`/`hwp`, `hlo`, `hstat`), at the
root's choices (`WakeOD.wakeD`: `L0 := L0T`, `ls0 := ls0T ls`; `WakeFinalCAW`:
`cT := WakeHG.cTW`). No pc literal: every address is a label's or a
region's.

- `hp_W`: `o.prog = wakeProg` from the two parses of the certificate.
- `hlo_W`: `(Ly).Λ.code.lo = lo` from the input layout's (`ofPlaceW` changes
  only the immediates).
- `hro`: `WakeOSide.hro_W` (A1).
- `hfree_W`: `RtFree Ly (L0T Ly.Λ) (ls0T ls)`: with no static label the start
  places only main's `ThreadId` box, which has no cells (`WakeLoadT.l0T_some`).
- `hcT_W`: the dummy flag word `cTW` (the heap's base) is not the first
  limit word `pinA + 16`, which A8 keeps off the heap (`rtOffOk`).
- `hax`: `ax := (Ly).lab siteL`, by `rfl`.
- `ntA_W`, `wsep_W`: `hs : WSep Ly (ntA Ly.lab)`: the counters and the first
  TCB's words by A8, the thread counter `scc_rt_nthreads` off them by A13's
  data part `a13data` (not in `PlaceW`; decided at the concrete layout).
- `hsub1_W`: the child's stack `r1W` in the stack pool (A8, A13's data part).
- `hctr2_of_data`: `hctr2` from the counters lying in `.data` and the second
  limit word `pinA + 112` in the pinned region (`hpin2`). `PlaceW` does not
  place the counters' symbols (their bytes are in `.data` or the pinned
  region, A8's `wordOk`), so either `hctr2` or `hctrD` is an instance fact of
  the concrete layout, decided there (at `Λe`: `.bss` words below
  `scc_rt_heap`).
- `hpin2_W`, `hpin2_outLit`: the pinned region reaches `pinA + 168`
  (`WakeOG.hGpl_gW`'s, `wake_finalCA_genW`'s `hpin2`) from A1's
  `regionsTied` (the region is the `.zero` after `scc_rt_pinned`), at wake's
  certificate for every layout (one `decide` on its `.zero`'s size).
-/
import Spike.Lib.A64WakeStartPlace
import Spike.Lib.WakeHG
import Spike.Lib.WakeLoadT
import Spike.Lib.WakeOSide

namespace Spike.Lib.A64.WakePh.StartPlaceLy

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (Arena FragS)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakeLoadT (L0T ls0T)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

omit hpw i in
/-- **`hp`**: the output's program is wake's, from the loader's two parses
of the certificate. -/
theorem hp_W {asm : String} (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog)
    (hwp : Scc.Sem.A64.textProgram asm = .ok wakeProg) : o.prog = wakeProg :=
  Except.ok.inj (hpa.symm.trans hwp)

/-- **`hlo`**: the code's base is the input layout's. -/
theorem hlo_W (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) : (Ly).Λ.code.lo = Spike.Lib.A64.WakePh.lo := hlo

/-- **`hfree`** at the start's labels: with no static label, the only
placed label is main's `ThreadId` box, of no cells, so it covers no
runtime word. -/
theorem hfree_W (hstat : Λ0.static = fun _ => none) (ls : Spike.Lib.A64Consumer.Lsize) :
    Spike.Lib.A64.Rt.RtFree (Ly) (L0T (Ly).Λ) (ls0T ls) := by
  rintro a - ⟨l, b, hl, hc⟩
  obtain ⟨rfl, rfl⟩ := Spike.Lib.WakeLoadT.l0T_some hstat hl
  simp [Scc.Sem.lrange, ls0T, Spike.Lib.A64ConsumerA.updN, Scc.Sem.Range.contains] at hc
  omega

/-- **`hcT`** at the root's dummy flag word: the heap's base is not the
first limit word, which A8 keeps clear of the heap (`rtOffOk`, field `2`). -/
theorem hcT_W : Spike.Lib.WakeHG.cTW hpw i ≠ ⟨(Ly).pinA + 16#64, 8⟩ := by
  intro he
  have hc := Scc.Cert.Rt.A64.clear_of_rtOffOk (PlaceW.rtOff_of_placeW (PlaceW.link i hpw)) (j := 2) (by decide)
  have hh := (PlaceW.wf_link_of_placeW i hpw).inSpace _
    (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.heap ∈ (Ly).Λ.regions)
  have hin := Spike.Lib.WakeHG.cTW_heap hpw i
  change Scc.Cert.Rt.A64.clearB (Ly).Λ.data ((Ly).pinA + 16#64) = true ∧
    Scc.Cert.Rt.A64.clearB (Ly).Λ.heap ((Ly).pinA + 16#64) = true at hc
  simp only [Scc.Cert.Rt.A64.clearB, Bool.or_eq_true, decide_eq_true_eq] at hc
  simp only [Scc.Sem.Range.InSpace, Scc.Sem.Range.contains] at hh hin
  have hb := congrArg (fun l : Loc => l.addr.toNat) he
  simp only [Spike.Lib.WakeHG.cTW, Scc.Sem.wordLoc, BitVec.toNat_ofNat] at hb
  have : (Ly).Λ.heap.lo % 2 ^ 64 = (Ly).Λ.heap.lo := Nat.mod_eq_of_lt (by omega)
  omega

/-- **`hctr2`** from the counters in `.data` and the second limit word in
the pinned region (`hpin2`): `.data` and the pinned region are disjoint
(`Layout.WF`), `pinA` the pinned region's base. -/
theorem hctr2_of_data (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hctrD : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], (Ly).Λ.data.contains a.toNat) :
    ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.WakeGOf2.lim2A (Ly) := by
  intro a ha he
  have hd : Λ0.data.contains a.toNat := hctrD a ha
  have hpz : (Ly).pinA.toNat + 168 ≤ Λ0.pinned.lo + Λ0.pinned.size := hpin2
  have hp0 : (Ly).pinA.toNat = Λ0.pinned.lo := PlaceW.pinA_toNat_ofPlaceW hpw i
  have hdp : Λ0.data.Disjoint Λ0.pinned := (PlaceW.wf_link_of_placeW i hpw).disjoint.2.2.2.2.2.2.2.1
  have hs := (Ly).words_small _ (Ly).pin_mem
  have hb : a.toNat = (Ly).pinA.toNat + 112 := by
    rw [he]
    show ((Ly).pinA + 112#64).toNat = _
    rw [BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint] at hd hdp
  omega

/-- **`hpin2`**: the pinned region, at `scc_rt_pinned` (`pinA`), is the
`.zero` after that symbol in `.bss`/`.data` (A1's `regionsTied`), so it
reaches `pinA + 168` once that `.zero` has 168 bytes. -/
theorem hpin2_W {n : Nat}
    (hz : Scc.Cert.PlaceOK.zeroAfter (o.secs.bss ++ o.secs.data) Scc.Cert.Link.pinnedSym = some n)
    (hn : 168 ≤ n) : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size := by
  have hreg := PlaceW.regionsTied_of_placeW hpw
  simp only [Scc.Cert.PlaceOK.regionsTied, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hreg
  have hsz : Λ0.pinned.size = n := Option.some.inj (hreg.2.2.2.symm.trans hz)
  have hp0 : (Ly).pinA.toNat = Λ0.pinned.lo := PlaceW.pinA_toNat_ofPlaceW hpw i
  show (Ly).pinA.toNat + 168 ≤ Λ0.pinned.lo + Λ0.pinned.size
  omega

/-- **`hpin2` at wake's certificate** (any layout): its `.zero` after
`scc_rt_pinned` has `131072` bytes. -/
theorem hpin2_outLit (hpc : PlaceW pcfg Λ0 SccCertificate.outLit) :
    (RuntimeLayout.ofPlaceW hpc i).pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceW hpc i).Λ.pinned.lo + (RuntimeLayout.ofPlaceW hpc i).Λ.pinned.size :=
  hpin2_W hpc i (n := 131072) (by decide) (by decide)

/-- Disjoint words differ. -/
private theorem ne_of_sep {a b : BitVec 64} (h : Scc.Cert.Rt.A64.WordSep a b) : a ≠ b := by
  rintro rfl; simp only [Scc.Cert.Rt.A64.WordSep] at h; omega

/-- **`scc_rt_nthreads` at its label** in the loaded thread, given A13's
data part (the symbol decided). -/
theorem ntA_W (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab = Scc.Cert.Rt.A64.rtA (Ly).Λ o.prog o.secs "scc_rt_nthreads" := by
  simp only [Scc.Cert.Spawn.A64.a13data, Bool.and_eq_true] at hA13
  obtain ⟨a0, ha0⟩ := Option.isSome_iff_exists.mp hA13.1.1.1.1.1
  have hs := Scc.Cert.Link.A64.symsAround_of_loadOk (PlaceW.loadOk_link_of_placeW i hpw)
  refine (congrArg Int64.toBitVec
    (Scc.Cert.Rt.A64.label_threadAt_of_symLab (E := Scc.Sem.Entry.linux) hs ha0)).trans ?_
  simp only [Scc.Cert.Rt.A64.rtA, ha0, Option.getD_some]
  rfl

/-- **`hs`**: the words' separation at the thread counter `ntA`: the
counters pairwise and the first TCB's words off them by A8 (`wordsOk`'s
pairwise disjointness, `tcbSep_of_wordsOk`), `ntA` off all of the runtime's
words by A13's data part (`hA13`, a check of the concrete layout: `PlaceW`
has no A13). -/
theorem wsep_W (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    Spike.Lib.A64.WakePh.WSep (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) := by
  have hw := Scc.Cert.Rt.A64.wordsOk_of_rtWordsOk (PlaceW.rtWordsOk_link_of_placeW i hpw)
  have hd := Scc.Cert.Rt.A64.words_disj_of_wordsOk hw
  obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hd
  obtain ⟨h3, h4⟩ := List.pairwise_cons.mp h2
  obtain ⟨h5, h6⟩ := List.pairwise_cons.mp h4
  obtain ⟨h7, -⟩ := List.pairwise_cons.mp h6
  have hnt := ntA_W hpw i hA13
  simp only [Scc.Cert.Spawn.A64.a13data, Bool.and_eq_true, List.all_cons, List.all_eq_true,
    decide_eq_true_eq] at hA13
  have ho : ∀ b ∈ (Ly).rtWords, b ≠ Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab := fun b hb =>
    (ne_of_sep (hnt ▸ hA13.1.1.1.2.1 b hb)).symm
  have m0 {x : BitVec 64} {l : List (BitVec 64)} : x ∈ x :: l := List.mem_cons.2 (.inl rfl)
  have m1 {x y : BitVec 64} {l : List (BitVec 64)} : x ∈ y :: x :: l := List.mem_cons.2 (.inr m0)
  have m2 {x y z : BitVec 64} {l : List (BitVec 64)} : x ∈ z :: y :: x :: l := List.mem_cons.2 (.inr m1)
  refine ⟨ne_of_sep (h1 (Ly).nextA m0), ne_of_sep (h1 (Ly).lockA m1), ne_of_sep (h1 (Ly).freeNA m2),
    ne_of_sep (h3 (Ly).lockA m0), ne_of_sep (h3 (Ly).freeNA m1), ne_of_sep (h5 (Ly).freeNA m0),
    ho _ (Ly).pn_mem, ho _ (Ly).next_mem, ho _ (Ly).lock_mem, ho _ (Ly).freeN_mem,
    Scc.Cert.Rt.A64.tcbSep_of_wordsOk hw, fun j hj => ho _ (Spike.Lib.A64.PhRec.tcb_mem (L := Ly) ⟨j, hj, rfl⟩)⟩

/-- **`hsub1`**: the child's stack (`r1W`, the second stack at
`scc_rt_stacks + 16384`) lies in the stack pool: the pool reaches the
second stack's end by A13's data part (`hA13`), and starts below the first
by A8 (`stacks_sub`). -/
theorem hsub1_W (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    (Spike.Lib.WakeOSide.r1W hpw i).Sub (Ly).Λ.stackPool := by
  have h32 : (Ly).stacksA.toNat + 32768 ≤ (Ly).Λ.stackPool.lo + (Ly).Λ.stackPool.size := by
    simp only [Scc.Cert.Spawn.A64.a13data, Bool.and_eq_true, decide_eq_true_eq] at hA13
    exact hA13.2
  have hs := (Ly).stacks_sub
  have hf := (Ly).pool_fit
  unfold Scc.Sem.Range.Sub Spike.Lib.WakeOSide.r1W Spike.Lib.A64.Rt.PreChild.r1Of RuntimeLayout.lab
  rw [(Ly).lab_stacks, BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [Scc.Sem.Range.Sub, Nat.reducePow, Nat.reduceMod] at hs ⊢
  omega

/-- The premises fit `wake_start_wc_place` at the root's choices. -/
example {asm : String} (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog)
    (hwp : Scc.Sem.A64.textProgram asm = .ok wakeProg) (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (hstat : Λ0.static = fun _ => none) (ls : Spike.Lib.A64Consumer.Lsize)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.WakeGOf2.lim2A (Ly))
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) {E : Scc.Sem.Entry} {ar : Arena} {p : Prog} {Dt Cl : State → Prop}
    {Ctx : FragS isaLSE2} {lbl lbl' : Spike.Lib.A64Consumer.Lbl} {lsize : Spike.Lib.A64Consumer.Lsize}
    {frM : TermRun.Frame} {c0 : Ctl} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {ar' : Arena}
    {I : Spike.Lib.A64ConsumerS.InvS} {pS : Prog} {lblS : Spike.Lib.A64Consumer.Lbl} :=
  StartPlace.wake_start_wc_place hpw i (a := Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (E := E) (ar := ar) (p := p) (Dt := Dt) (Cl := Cl) (Ctx := Ctx)
    (lbl := lbl) (lbl' := lbl') (lsize := lsize) (frM := frM) (c0 := c0) (μ := μ) (rd := rd) (ar' := ar')
    (I := I) (pS := pS) (lblS := lblS) (P := fun _ => True) (hp := hp_W hpa hwp) (hlo := hlo_W hpw i hlo)
    (hro := Spike.Lib.WakeOSide.hro_W hpw i) (hfree := hfree_W hpw i hstat ls) (hcT := hcT_W hpw i)
    (ax := (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (hax := rfl) (hctr2 := hctr2) (hs := wsep_W hpw i hA13)

/-- info: 'Spike.Lib.A64.WakePh.StartPlaceLy.hcT_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hcT_W

/-- info: 'Spike.Lib.A64.WakePh.StartPlaceLy.hfree_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hfree_W

/-- info: 'Spike.Lib.A64.WakePh.StartPlaceLy.hctr2_of_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hctr2_of_data

/-- info: 'Spike.Lib.A64.WakePh.StartPlaceLy.hpin2_outLit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hpin2_outLit

/-- info: 'Spike.Lib.A64.WakePh.StartPlaceLy.wsep_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wsep_W

/-- info: 'Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hsub1_W

end Spike.Lib.A64.WakePh.StartPlaceLy
