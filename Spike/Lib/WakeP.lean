/-
**wake.w's location sets**: the `Inv2Params` argument
`P` of `Spike.Lib.WakeA64.WakeRel` (the parameters of the two-thread
relation `Spike.Lib.Inv2Core.Inv2`), ISA-generic, from the layout facts as
data (`WakeLocs`) and the separation facts the core needs as explicit
hypotheses (`WakeLocs.OK`).

- **frozen** (`frz`, `frzS`): every word of a label placed before the
  clone, except the flag `c` (target location `cT`, source address `cS`),
  on each side. The placement is `WakeLocs.lbl`, a fixed parameter: the
  caller instantiates it with the spawn's (`SpawnRec.lbl` at the clone),
  never with a live placement, so a label allocated after the clone is not
  frozen. In wake the placed
  labels are `main`'s `ThreadId` box and the cell `new z` (`c`); `c` is
  the only one written after the spawn (the worker's `store rel c 1`).
- **footprint** (`foot i`): thread `i`'s owned words (`own i`), its other
  words written after the spawn (`priv i`: its stack and private words, the
  protocol words; for the worker its exit word and main's permit word `pT`
  (`swpal`), for main `pT` (`park`'s exchange)), and for the worker `cT`.
- **cover** (`cov i`): thread `i`'s owned words and the frozen words.
- **no promise** (`noProm`): at a `write` or `clone` system call, outside the
  transfer sites (`noProm_prom`: a certified thread there has no promise,
  `Kernel.prom_nil_of_write`, `Handover.prom_nil_of_clone`).

`pT` may be in both `priv 0` and `priv 1`: it is in neither cover set
(`OK.priv_nlab`, `OK.disj`). Then `foot_cov` and `frz_cov` (the static
fields of `Inv2Core`, the `hfoot`/`hfrz` premises of
`Spike.Lib.Inv2Start.inv2_start`) hold (`wakeP_foot_cov`, `wakeP_frz_cov`),
and an owned word in `own i` is in `cov i` (`wakeP_own_cov`).
-/
import Spike.Lib.Inv2Core
import Spike.Lib.Handover

namespace Spike.Lib.WakeP

open Kraken.Promising Scc.Sem Scc.Sem.Kernel Spike.Lib.Inv2Core

/-- **wake's location data**: the spawn's placement (`lbl`, `lsize`: the
labels placed before the clone, `SpawnRec.lbl`/`lsize` at the clone, not a
live placement), the
flag's target location and source address, and each thread's owned words
(`own i`) and other footprint words (`priv i`). -/
structure WakeLocs where
  lbl : WeakMem.AllocLabel → Option Nat
  lsize : WeakMem.AllocLabel → Nat
  cT : Loc
  cS : WeakMem.Address
  /-- Thread `i`'s owned runtime words (its cover set's own part). -/
  own : Nat → Loc → Prop
  /-- Thread `i`'s other words written after the spawn (stack, private
  words, protocol words such as main's permit word and the worker's exit
  word). -/
  priv : Nat → Loc → Prop

/-- **A source address inside a placed label.** -/
def InLabelS (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (a : WeakMem.Address) : Prop :=
  (lbl a.label).isSome ∧ a.offset < lsize a.label

/-- **A system call with no promise**: `write` or `clone`, outside the
transfer sites. -/
def NoPromAt {I : ISA} (K : Abi I) (μ : Marks) (s : I.State) : Prop :=
  siteAt K μ s = none ∧ K.atSys s = true ∧
    ((∃ fd buf n, decode K.nrs (K.nr s) (K.arg s) = some (.write fd buf n)) ∨
      ∃ stack tls, decode K.nrs (K.nr s) (K.arg s) = some (.clone stack tls))

/-- **wake's `Inv2Params`** over the ABI `K` and the code marks `μ`. -/
def wakeP {I : ISA} (K : Abi I) (μ : Marks) (W : WakeLocs) : Inv2Params I where
  frz l := InLabel W.lbl W.lsize l ∧ l ≠ W.cT
  frzS a := InLabelS W.lbl W.lsize a ∧ a ≠ W.cS
  cov i l := W.own i l ∨ (InLabel W.lbl W.lsize l ∧ l ≠ W.cT)
  foot i l := W.own i l ∨ W.priv i l ∨ (i = 1 ∧ l = W.cT)
  noProm := NoPromAt K μ

/-- **The separation facts** `Inv2Core` needs of the location data: one
thread's footprint words are not the other's owned words; no owned or
footprint word is inside a placed label; `cT` is not main's. -/
structure WakeLocs.OK (W : WakeLocs) : Prop where
  disj : ∀ i j l, i < 2 → j < 2 → i ≠ j → (W.own j l ∨ W.priv j l) → ¬ W.own i l
  own_nlab : ∀ i l, i < 2 → W.own i l → ¬ InLabel W.lbl W.lsize l
  priv_nlab : ∀ i l, i < 2 → W.priv i l → ¬ InLabel W.lbl W.lsize l
  c_own : ¬ W.own 0 W.cT

section

variable {I : ISA} {K : Abi I} {μ : Marks} {W : WakeLocs}

/-- (3) The frozen words are in both cover sets. -/
theorem wakeP_frz_cov : ∀ i l, i < 2 → (wakeP K μ W).frz l → (wakeP K μ W).cov i l :=
  fun _ _ _ h => Or.inr h

/-- (O2, O3) One thread's footprint is outside the other's cover set. -/
theorem wakeP_foot_cov (h : W.OK) :
    ∀ i j l, i < 2 → j < 2 → i ≠ j → (wakeP K μ W).foot j l → ¬ (wakeP K μ W).cov i l := by
  intro i j l hi hj hij hf hc
  simp only [wakeP] at hf hc
  rcases hf with hf | hf | ⟨rfl, rfl⟩
  · rcases hc with hc | ⟨hc, -⟩
    · exact h.disj i j l hi hj hij (.inl hf) hc
    · exact h.own_nlab j l hj hf hc
  · rcases hc with hc | ⟨hc, -⟩
    · exact h.disj i j l hi hj hij (.inr hf) hc
    · exact h.priv_nlab j l hj hf hc
  · have hi0 : i = 0 := by omega
    subst hi0
    rcases hc with hc | ⟨-, hc⟩
    · exact h.c_own hc
    · exact hc rfl

/-- (O3) An owned word of thread `i` is in its cover set. -/
theorem wakeP_own_cov {i : Nat} {l : Loc} (h : W.own i l) : (wakeP K μ W).cov i l := Or.inl h

/-- A placed target word other than `cT` is frozen. -/
theorem wakeP_frz_iff {l : Loc} : (wakeP K μ W).frz l ↔ InLabel W.lbl W.lsize l ∧ l ≠ W.cT := Iff.rfl

/-- A footprint word of a thread is not frozen (`cT` by definition, the
others outside every placed label). -/
theorem wakeP_not_frz_of_foot (h : W.OK) {j : Nat} {l : Loc} (hj : j < 2) (hf : (wakeP K μ W).foot j l) :
    ¬ (wakeP K μ W).frz l := by
  rintro ⟨hl, hc⟩
  rcases hf with hf | hf | ⟨-, rfl⟩
  · exact h.own_nlab j l hj hf hl
  · exact h.priv_nlab j l hj hf hl
  · exact hc rfl

/-- The worker's store to `cT` is in its footprint. -/
theorem wakeP_foot_c : (wakeP K μ W).foot 1 W.cT := Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- **The worker's footprint meets the placed labels only at `cT`**
(`WCompat.footLab`). -/
theorem wakeP_footLab (h : W.OK) {l : Loc} (hf : (wakeP K μ W).foot 1 l) (hl : InLabel W.lbl W.lsize l) :
    l = W.cT := by
  rcases hf with hf | hf | ⟨-, rfl⟩
  · exact absurd hl (h.own_nlab 1 l (by decide) hf)
  · exact absurd hl (h.priv_nlab 1 l (by decide) hf)
  · rfl

/-- **`cS` is not frozen** (`WCompat.cSfrz`). -/
theorem wakeP_not_frzS_c : ¬ (wakeP K μ W).frzS W.cS := fun h => h.2 rfl

/-- (7) **A certified thread at a `write` or `clone` has no promise**: the
`noProm0`/`noProm1` fields from the thread's certification. -/
theorem noProm_prom {A : Arch} {x : KState} {tid : Nat} {t : Thread I} {mem : Memory}
    (hn : (wakeP K μ W).noProm t.st) (hcert : CertOkC A (certSem K A μ x tid) tid t mem) : t.prom = [] := by
  obtain ⟨hs, ha, ⟨fd, buf, n, hd⟩ | ⟨stack, tls, hd⟩⟩ := hn
  · exact prom_nil_of_write (K := K) hs ha hd hcert
  · exact Spike.Lib.Handover.prom_nil_of_clone (K := K) hs ha hd hcert

end

end Spike.Lib.WakeP
