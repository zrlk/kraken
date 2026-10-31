/-
**The layout premises of `StartPlace.wake_start_wc_place` at wake's
placed output** (x86-64; twin of `Spike/Lib/A64WakeStartPlaceLy.lean`): at
the runtime's layout `Ly := RuntimeLayout.ofPlaceWX hpw i` of an output with
wake's placement facts, the premises `hp`, `hlo`, `hfree`, `hcT`, `hs`,
`hctr2` (and `wake_start_wc_placeX`'s) from `PlaceWX` and the root's instance
facts (the loader's parses `hpa`/`hwp`, `hlo`, `hstat`, A13's data part
`hA13`), at the root's choices (`L0 := L0T`, `ls0 := ls0T ls`,
`cT := X64WakeHG.cTW`). No pc literal: every address is a label's or a
region's.

- `hp_W`: `o.prog = wakeCells` from the two parses of the certificate.
- `hlo_W`: `(Ly).Λ.code.lo = lo` from the input layout's (`ofPlaceWX`
  changes only the immediates).
- `hfree_W`: `RtFree Ly (L0T Ly.Λ) (ls0T ls)`: with no static label the start
  places only main's `ThreadId` box, which has no cells (`X64WakeLoadT.l0T_some`).
- `hcT_W`: the dummy flag word `cTW` (the heap's base) is not the first
  limit word `pinA + 16`, which A8 keeps off the heap (`rtOffOk`).
- `wsep_W`: `hs : WSep Ly (ntA Ly.lab)`: the counters and the first TCB's
  words by A8, the thread counter off them by A13's data part (`ntA_W`).
- `hsub1_W`: the child's stack `r1W` in the stack pool (A8, A13's data part).
- `hctr2_of_data`: `hctr2` from the counters lying in `.data` and the second
  limit word `pinA + 112` in the pinned region (`hpin2`).
- `hpin2_W`, `hpin2_outLit`: the pinned region reaches `pinA + 168` from
  A1's `regionsTied`, at wake's x86-64 certificate for every layout.

Where x86-64 differs from AArch64: the program is the cell list `wakeCells`
(AArch64 `wakeProg`), read by `Scc.Sem.X64.cellsOf` (as `X64WakeOAb.hlab_W`); the layout,
placement facts and certificate checks are x86-64's (`PlaceWX`,
`Scc.Cert.Rt.X64`, `Scc.Cert.Spawn.X64.a13data`); `ntA_W` is
`WakePh.ntA_W` (`X64WakeOwnSW`), not restated.
-/
import Spike.Lib.X64WakeStartPlace
import Spike.Lib.X64WakeHG
import Spike.Lib.X64WakeLoadT
import Spike.Lib.X64WakeOSide
import Spike.Lib.X64WakeOwnSW
import Spike.Test.Cert.X64WakeCert

namespace Spike.Lib.X64.WakePh.StartPlaceLy

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Arena FragS PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open SccCode (wakeCells)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

omit hpw i in
/-- **`hp`**: the output's program is wake's, from the loader's two parses
of the certificate. -/
theorem hp_W {asm : Scc.Sem.X64.Asm} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hwp : Scc.Sem.X64.cellsOf asm = some wakeCells) : o.prog = wakeCells :=
  Option.some.inj (hpa.symm.trans hwp)

/-- **`hlo`**: the code's base is the input layout's. -/
theorem hlo_W (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) : (Ly).Λ.code.lo = Spike.Lib.X64.WakePh.lo := hlo

/-- **`hfree`** at the start's labels: with no static label, the only
placed label is main's `ThreadId` box, of no cells, so it covers no
runtime word. -/
theorem hfree_W (hstat : Λ0.static = fun _ => none) (ls : Spike.Lib.X64Consumer.Lsize) :
    Spike.Lib.X64.Rt.RtFree (Ly) (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) (Spike.Lib.X64WakeLoadT.ls0T ls) := by
  rintro a - ⟨l, b, hl, hc⟩
  obtain ⟨rfl, rfl⟩ := Spike.Lib.X64WakeLoadT.l0T_some hstat hl
  simp [Scc.Sem.lrange, Spike.Lib.X64WakeLoadT.ls0T, Spike.Lib.X64ConsumerA.updN, Scc.Sem.Range.contains] at hc
  omega

/-- **`hcT`** at the root's dummy flag word: the heap's base is not the
first limit word, which A8 keeps clear of the heap (`rtOffOk`, field `2`). -/
theorem hcT_W : Spike.Lib.X64WakeHG.cTW hpw i ≠ ⟨(Ly).pinA + 16#64, 8⟩ := by
  intro he
  have hc := Scc.Cert.Rt.X64.clear_of_rtOffOk (PlaceWX.rtOff_of_placeWX (PlaceWX.link i hpw)) (j := 2) (by decide)
  have hh := (PlaceWX.wf_link_of_placeWX i hpw).inSpace _
    (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.heap ∈ (Ly).Λ.regions)
  have hin := Spike.Lib.X64WakeHG.cTW_heap hpw i
  change Scc.Cert.Rt.X64.clearB (Ly).Λ.data ((Ly).pinA + 16#64) = true ∧
    Scc.Cert.Rt.X64.clearB (Ly).Λ.heap ((Ly).pinA + 16#64) = true at hc
  simp only [Scc.Cert.Rt.X64.clearB, Bool.or_eq_true, decide_eq_true_eq] at hc
  simp only [Scc.Sem.Range.InSpace, Scc.Sem.Range.contains] at hh hin
  have hb := congrArg (fun l : Loc => l.addr.toNat) he
  simp only [Spike.Lib.X64WakeHG.cTW, Scc.Sem.wordLoc, BitVec.toNat_ofNat] at hb
  have : (Ly).Λ.heap.lo % 2 ^ 64 = (Ly).Λ.heap.lo := Nat.mod_eq_of_lt (by omega)
  omega

/-- **`hctr2`** from the counters in `.data` and the second limit word in
the pinned region (`hpin2`): `.data` and the pinned region are disjoint
(`Layout.WF`), `pinA` the pinned region's base. -/
theorem hctr2_of_data (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hctrD : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], (Ly).Λ.data.contains a.toNat) :
    ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.X64WakeGOf2.lim2A (Ly) := by
  intro a ha he
  have hd : Λ0.data.contains a.toNat := hctrD a ha
  have hpz : (Ly).pinA.toNat + 168 ≤ Λ0.pinned.lo + Λ0.pinned.size := hpin2
  have hp0 : (Ly).pinA.toNat = Λ0.pinned.lo := PlaceWX.pinA_toNat_ofPlaceWX hpw i
  have hdp : Λ0.data.Disjoint Λ0.pinned := (PlaceWX.wf_link_of_placeWX i hpw).disjoint.2.2.2.2.2.2.2.1
  have hs := (Ly).words_small _ (Ly).pin_mem
  have hb : a.toNat = (Ly).pinA.toNat + 112 := by
    rw [he]
    show ((Ly).pinA + Spike.Lib.X64WakeGOf2.lim2Off).toNat = _
    rw [BitVec.toNat_add]
    simp only [Spike.Lib.X64WakeGOf2.lim2Off, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint] at hd hdp
  omega

/-- **`hpin2`**: the pinned region, at `scc_rt_pinned` (`pinA`), is the
`.zero` after that symbol in `.bss`/`.data` (A1's `regionsTied`), so it
reaches `pinA + 168` once that `.zero` has 168 bytes. -/
theorem hpin2_W {n : Nat}
    (hz : Scc.Cert.PlaceOK.zeroAfter (o.secs.bss ++ o.secs.data) Scc.Cert.Link.pinnedSym = some n)
    (hn : 168 ≤ n) : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size := by
  have hreg := PlaceWX.regionsTied_of_placeWX hpw
  simp only [Scc.Cert.PlaceOK.regionsTied, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hreg
  have hsz : Λ0.pinned.size = n := Option.some.inj (hreg.2.2.2.symm.trans hz)
  have hp0 : (Ly).pinA.toNat = Λ0.pinned.lo := PlaceWX.pinA_toNat_ofPlaceWX hpw i
  show (Ly).pinA.toNat + 168 ≤ Λ0.pinned.lo + Λ0.pinned.size
  omega

/-- **`hpin2` at wake's x86-64 certificate** (any layout): its `.zero`
after `scc_rt_pinned` has `131072` bytes. -/
theorem hpin2_outLit (hpc : PlaceWX pcfg Λ0 SccCertificate.outLit) :
    (RuntimeLayout.ofPlaceWX hpc i).pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceWX hpc i).Λ.pinned.lo + (RuntimeLayout.ofPlaceWX hpc i).Λ.pinned.size :=
  hpin2_W hpc i (n := 131072) (by decide) (by decide)

/-- Disjoint words differ. -/
private theorem ne_of_sep {a b : BitVec 64} (h : Scc.Cert.Rt.X64.WordSep a b) : a ≠ b := by
  rintro rfl; simp only [Scc.Cert.Rt.X64.WordSep] at h; omega

/-- **`hs`**: the words' separation at the thread counter `ntA`: the
counters pairwise and the first TCB's words off them by A8 (`wordsOk`'s
pairwise disjointness, `tcbSep_of_wordsOk`), `ntA` off all of the runtime's
words by A13's data part (`hA13`, a check of the concrete layout: `PlaceWX`
has no A13). -/
theorem wsep_W (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    Spike.Lib.X64.WakePh.WSep (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) := by
  have hw := Scc.Cert.Rt.X64.wordsOk_of_rtWordsOk (PlaceWX.rtWordsOk_link_of_placeWX i hpw)
  have hd := Scc.Cert.Rt.X64.words_disj_of_wordsOk hw
  obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hd
  obtain ⟨h3, h4⟩ := List.pairwise_cons.mp h2
  obtain ⟨h5, h6⟩ := List.pairwise_cons.mp h4
  obtain ⟨h7, -⟩ := List.pairwise_cons.mp h6
  have hnt := Spike.Lib.X64.WakePh.ntA_W hpw i hA13
  simp only [Scc.Cert.Spawn.X64.a13data, Bool.and_eq_true, List.all_cons, List.all_eq_true,
    decide_eq_true_eq] at hA13
  have ho : ∀ b ∈ (Ly).rtWords, b ≠ Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab := fun b hb =>
    (ne_of_sep (hnt ▸ hA13.1.1.1.2.1 b hb)).symm
  have m0 {x : BitVec 64} {l : List (BitVec 64)} : x ∈ x :: l := List.mem_cons.2 (.inl rfl)
  have m1 {x y : BitVec 64} {l : List (BitVec 64)} : x ∈ y :: x :: l := List.mem_cons.2 (.inr m0)
  have m2 {x y z : BitVec 64} {l : List (BitVec 64)} : x ∈ z :: y :: x :: l := List.mem_cons.2 (.inr m1)
  refine ⟨ne_of_sep (h1 (Ly).nextA m0), ne_of_sep (h1 (Ly).lockA m1), ne_of_sep (h1 (Ly).freeNA m2),
    ne_of_sep (h3 (Ly).lockA m0), ne_of_sep (h3 (Ly).freeNA m1), ne_of_sep (h5 (Ly).freeNA m0),
    ho _ (Ly).pn_mem, ho _ (Ly).next_mem, ho _ (Ly).lock_mem, ho _ (Ly).freeN_mem,
    Scc.Cert.Rt.X64.tcbSep_of_wordsOk hw, fun j hj => ho _ (Spike.Lib.X64.PhRec.tcb_mem (L := Ly) ⟨j, hj, rfl⟩)⟩

/-- **`hsub1`**: the child's stack (`r1W`, the second stack at
`scc_rt_stacks + 16384`) lies in the stack pool: the pool reaches the
second stack's end by A13's data part (`hA13`), and starts below the first
by A8 (`stacks_sub`). -/
theorem hsub1_W (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    (Spike.Lib.X64WakeOSide.r1W hpw i).Sub (Ly).Λ.stackPool := by
  have h32 : (Ly).stacksA.toNat + 32768 ≤ (Ly).Λ.stackPool.lo + (Ly).Λ.stackPool.size := by
    simp only [Scc.Cert.Spawn.X64.a13data, Bool.and_eq_true, decide_eq_true_eq] at hA13
    exact hA13.2
  have hs := (Ly).stacks_sub
  have hf := (Ly).pool_fit
  unfold Scc.Sem.Range.Sub Spike.Lib.X64WakeOSide.r1W Spike.Lib.X64.Rt.PreChild.r1Of RuntimeLayout.lab
  rw [(Ly).lab_stacks, BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [Scc.Sem.Range.Sub, Nat.reducePow, Nat.reduceMod] at hs ⊢
  omega

end Spike.Lib.X64.WakePh.StartPlaceLy

/-- info: 'Spike.Lib.X64.WakePh.StartPlaceLy.hcT_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartPlaceLy.hcT_W

/-- info: 'Spike.Lib.X64.WakePh.StartPlaceLy.hfree_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartPlaceLy.hfree_W

/-- info: 'Spike.Lib.X64.WakePh.StartPlaceLy.hctr2_of_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartPlaceLy.hctr2_of_data

/-- info: 'Spike.Lib.X64.WakePh.StartPlaceLy.hpin2_outLit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartPlaceLy.hpin2_outLit

/-- info: 'Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W

/-- info: 'Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W
