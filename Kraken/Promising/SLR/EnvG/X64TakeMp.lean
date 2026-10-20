/-
**Part 4: x64 message passing with a writing
reader — the program, its predicates and its VCs** (on `EnvGTX`,
`EnvG/TakeX64Link.lean`; the x64 copy of `EnvG/TakeMp.lean`).

The writer is x64 MP's (`EnvG/X64MpVCGen.lean`, `mpWriterX`: `movl %eax,
(%rsi)` data `:= 42`, then `movl %ecx, (%rdi)` flag `:= 1`, the planned
release giving all of `Dt` to the slot of the reader's acquire id,
`flagPred`). The reader **takes** the data at its flag load, then writes it
and reads its own write back:
```
 takeReaderX:
 0 spin:
 1   movl (%rdi), %eax
 2   cmpl $0, %eax
 3   je spin
 4   movl $43, (%rsi)
 5   movl (%rsi), %ebx
 6 done_t:
```

**Under `Arch.tso`** the plain `mov` load is an acquire (`plainLoad :=
.acqPc`) and the plain `mov` store a release (`plainStore := .rel`). So:
- the flag load takes (as AArch64's `ldar`);
- the store of `43` is a release *store* to an unplanned location: permitted
  by a positive share and a pure value (`Dt`'s release predicate is pure),
  exactly as an AArch64 plain `str`;
- **the read-back load is an acquire too**, and takes if not forwarded.
  The reader holds all of `Dt`, so whatever it takes adds nothing to `Dt`
  (`takeEff_wr_full`, `EnvG/TakeX64VCGen.lean`); on AArch64 this load was a
  plain `ldr` (`takeEff_of_not_acq`).

**The VCs** (on `ETX P tid = EnvGTX Arch.tso tid rdPlanX (mpS P)`, the empty
plan, the MP layout `[(f, 4), (d, 4)]`):
- `vc_k1` (`movl (%rdi), %eax`): from `K1` (the loop invariant), an outcome
  with a zero low word re-establishes `K1`, one with a non-zero low word gives
  `K2`: all of `Dt`, every write at or below `vwNew` (`takeAll_wr_full`).
  Spurious takes of zero flag messages are handled by `OkPred`, as on
  AArch64.
- `vc_k2` (`movl $43, (%rsi)`): permitted, and afterwards `K3`: all of `Dt`
  with maximal write `(43, tw)`, `tw` at or below the coherence view of `Dt`.
- `vc_k3` (`movl (%rsi), %ebx`): the reader keeps `Own43`, and under the
  clean flag the load returns `43` (`read_max`).
- `K1.fence`, `K2.fence`, `K3.fence`: monotone under fences (`FenceLe`).

Phase-1 limits (single-access trees, releases are stores, takes only at
non-forwarded acquire loads) apply; none is binding here.
-/
import Kraken.Promising.SLR.EnvG.X64MpSmoke
import Kraken.Promising.SLR.EnvG.TakeX64Link
import Kraken.Promising.SLR.EnvG.TakeX64VCGen
import Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.TakeMp

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.X64.Parser

/-! ## The program, the plan, the environment -/

/-- **The writing reader, x64**: spin on the flag at `(%rdi)` until it is
non-zero, then store `43` to the data at `(%rsi)` and load it back into
`ebx`. -/
def takeReaderX : Program := parse("
spin:
  movl (%rdi), %eax
  cmpl $0, %eax
  je spin
  movl $43, (%rsi)
  movl (%rsi), %ebx
done_t:
")

/-- info: 7 -/
#guard_msgs in
#eval takeReaderX.length

/-- The reader's plan: no release. -/
def rdPlanX : Plan := ⟨[]⟩

theorem rdPlanX_valid : rdPlanX.Valid := by decide

/-- The environment of the writing reader `tid` (x64, `Arch.tso`). -/
abbrev ETX (P : Params) (tid : Nat) : SharedEnv := EnvGTX Arch.tso tid rdPlanX (mpS P)

/-! ## The predicates -/

/-- **A usable acquire predicate**: at a non-zero flag value it gives `Good`
(all of `Dt`), unless its timestamp is that of a zero flag message (where a
spurious take relaxed it). -/
def OkPred (P : Params) (c : Config isa) (ψ : Pred) : Prop :=
  ∀ v m V R, ψ.P v m V R → BitVec.setWidth 32 v ≠ 0 →
    Good P.Dt V R ∨ ∃ v0, c.mem.read? P.Fl V = some v0 ∧ BitVec.setWidth 32 v0 = 0

theorem OkPred.snap {P : Params} {tid : Nat} {c c' : Config isa} {ψ : Pred} (h : OkPred P c ψ)
    (hs : SnapLe tid c c') : OkPred P c' ψ := fun v m V R hP hv =>
  (h v m V R hP hv).imp id fun ⟨v0, hr, h0⟩ => ⟨v0, hs.read? hr, h0⟩

theorem OkPred.flag {P : Params} {c : Config isa} : OkPred P c P.φ := fun _ _ _ _ hP hv => .inl (hP hv)

/-- Before the flag load (the loop invariant): the world (the flag's release
predicate `φ`, `Dt` pure), no forwarding item for `Fl`, and an acquire id of
`Fl` with a usable predicate. -/
def K1 (P : Params) (σ : EStateX) : Prop :=
  σ.g.rel P.Fl = P.φ ∧ (∀ v, Pred.Pure (σ.g.rel P.Dt) v) ∧ σ.vs.getFwd P.Fl = none ∧
    ∃ ι, ι < σ.g.acqTab.length ∧ 1 ≤ σ.r.acq P.Fl ι ∧ OkPred P σ.snap (σ.g.acqPred ι)

/-- After the take (before the store): `Dt` pure, all of `Dt`, every write of
`Dt` at or below `vwNew`. -/
def K2 (P : Params) (σ : EStateX) : Prop :=
  (∀ v, Pred.Pure (σ.g.rel P.Dt) v) ∧ (σ.r.wr P.Dt).q = 1 ∧ ∀ p, (σ.r.wr P.Dt).X p → p.2 ≤ σ.vs.vwNew

/-- All of `Dt`, with maximal write `(43, tw)`. -/
def Own43 (P : Params) (r : Res) : Prop :=
  (r.wr P.Dt).q = 1 ∧ ∃ tw, (r.wr P.Dt).X (43#128, tw) ∧ ∀ p, (r.wr P.Dt).X p → p.2 ≤ tw

/-- After the store (before the read-back): `Own43`, with `tw` at or below
the coherence view of `Dt`. -/
def K3 (P : Params) (σ : EStateX) : Prop :=
  (σ.r.wr P.Dt).q = 1 ∧ ∃ tw, (σ.r.wr P.Dt).X (43#128, tw) ∧ (∀ p, (σ.r.wr P.Dt).X p → p.2 ≤ tw) ∧
    tw ≤ σ.vs.getCoh P.Dt

theorem K3.own43 {P : Params} {σ : EStateX} (h : K3 P σ) : Own43 P σ.r :=
  ⟨h.1, h.2.elim fun tw h => ⟨tw, h.1, h.2.1⟩⟩

/-! ## Fences -/

theorem K1.fence {P : Params} {σ σ' : EStateX} (h : K1 P σ) (hf : FenceLe σ σ') : K1 P σ' := by
  unfold K1; rw [hf.g, hf.r, hf.getFwd, hf.snap]; exact h

theorem K2.fence {P : Params} {σ σ' : EStateX} (h : K2 P σ) (hf : FenceLe σ σ') : K2 P σ' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by rw [hf.g]; exact h1, by rw [hf.r]; exact h2,
    fun p hp => Nat.le_trans (h3 p (by rw [← hf.r]; exact hp)) hf.vwNew⟩

theorem K3.fence {P : Params} {σ σ' : EStateX} (h : K3 P σ) (hf : FenceLe σ σ') : K3 P σ' := by
  unfold K3; rw [hf.r, hf.getCoh]; exact h

/-! ## The VCs -/

/-- **VC K1** (`movl (%rdi), %eax`, an acquire under `Arch.tso`, on
`EnvGTX`): a zero flag keeps the loop invariant, a non-zero flag takes all of
`Dt`. -/
theorem vc_k1 {P : Params} (tid : Nat) (σ : EStateX) (h : K1 P σ) :
    ∀ v (σ' : EStateX), (ETX P tid).step (.load .plain false P.f 4) σ v σ' →
      (BitVec.setWidth 32 v = 0 → K1 P σ') ∧ (BitVec.setWidth 32 v ≠ 0 → K2 P σ') := by
  intro v σ' hs
  obtain ⟨ga, hanc, ⟨rF, E⟩, -, tr, hrd, hlv, a, ha, hr, hg, -⟩ := step_loadFactsT (pl := rdPlanX) hs
  obtain ⟨hrel, hpure, hfw, ι, hlt, hacq1, hok⟩ := h
  have hn := hanc.lt
  have hacq : σ.r.acq P.Fl ι = 1 := Nat.le_antisymm (E.thread_acq_le hn _ _) hacq1
  have hc : TakeCond Arch.tso .plain σ.vs P.Fl tr := ⟨by decide, not_fwded_of_none hfw⟩
  have ha' : a = takeAll P.Fl tr σ.r ga := ha.1 hc
  have hrel' : σ'.g.rel = σ.g.rel := by rw [hg, (ha.ghost_le).rel, hanc.rel]
  have hok' : OkPred P σ'.snap (ga.acqPred ι) := by rw [hanc.acqPred hlt]; exact hok.snap hanc.snap
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨ι', h1, h2, hp⟩ := takeAll_held (l := P.Fl) (tr := tr) (r := σ.r) (g := ga) hacq1 (hanc.acqLen hlt)
    refine ⟨by rw [hrel']; exact hrel, fun w => by rw [hrel']; exact hpure w, by rw [hlv.getFwd]; exact hfw, ι',
      by rw [hg, ha']; exact h2, by rw [hr, ha']; exact h1, ?_⟩
    rw [hg, ha']
    rcases hp with hp | hp
    · rw [hp]; exact hok'
    · rw [hp]
      intro v' m V R hP hv'
      rcases hP with ⟨rfl, -⟩ | hP
      · exact .inr ⟨v, hrd.val, hv⟩
      · exact hok' v' m V R hP hv'
  · obtain ⟨s, hs, hkey, hid, hP⟩ := SLR.EnvG.slot_of_seen (k := (P.Fl, tr)) E hn hacq hrd.val
      (by rw [hanc.rel, hrel]; exact flagPred_impure hv)
    obtain ⟨hq, ts, -, hmax, hts⟩ : Good P.Dt tr s.res := by
      rcases hok' v _ tr s.res hP hv with hG | ⟨v0, hr0, h0⟩
      · exact hG
      · rw [hrd.val] at hr0; cases hr0; exact absurd h0 hv
    obtain ⟨hq', hX'⟩ := takeAll_wr_full hn E hs hkey (by rw [hid]; exact hacq) hq
    have hvw : tr ≤ σ'.vs.vwNew := (hlv.acq (by decide) (not_fwded_of_none hfw)).2
    refine ⟨fun w => by rw [hrel']; exact hpure w, by rw [hr, ha']; exact hq', fun p hp => ?_⟩
    rw [hr, ha'] at hp
    exact Nat.le_trans (hmax p ((hX' p).mp hp)) (Nat.le_trans hts hvw)

/-- **VC K2** (`movl $43, (%rsi)`, a release store under `Arch.tso` to the
unplanned `Dt`): permitted, and gives `K3`. -/
theorem vc_k2 {P : Params} (tid : Nat) (σ : EStateX) (h : K2 P σ) :
    (ETX P tid).ok (.store .plain false P.d 4 43#128) σ ∧
      ∀ b (σ' : EStateX), (ETX P tid).step (.store .plain false P.d 4 43#128) σ b σ' → K3 P σ' := by
  obtain ⟨hpure, hq, hmax⟩ := h
  refine ⟨⟨⟨rfl, by rw [hq]; decide, fun _ => hpure _, fun hr => by simp [rdPlanX, Plan.rel, Plan.find?] at hr⟩,
    by simp [SharedEnv.AccessIn]⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, -, -, hwb, hwv, -, hr, -⟩ := step_storeFactsT hs
  have hr' : σ'.r = σ.r.addW P.Dt (43#128, tw) := by
    simpa [Plan.after, rdPlanX, Plan.rel, Plan.find?] using hr
  refine ⟨by rw [hr', Res.addW_q]; exact hq, tw, ?_, fun p hp => ?_, hwv.coh⟩
  · rw [hr', Res.addW_X_self, hq]; exact .inr ⟨by decide, rfl⟩
  · rw [hr', Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hmax p hp) hwb.vwNew)
    · exact Nat.le_refl _

/-- **VC K3** (`movl (%rsi), %ebx`, an acquire under `Arch.tso` that may
take): the reader keeps `Own43` (`takeEff_wr_full`), and under the clean flag
the load returns its own `43`. -/
theorem vc_k3 {P : Params} (tid : Nat) (σ : EStateX) (h : K3 P σ) :
    ∀ v (σ' : EStateX), (ETX P tid).step (.load .plain false P.d 4) σ v σ' →
      Own43 P σ'.r ∧ (σ'.cl → v = 43#128) := by
  intro v σ' hs
  obtain ⟨ga, hanc, ⟨rF₀, E₀⟩, hcl, tr, hrd, -, a, ha, hr, -⟩ := step_loadFactsT (pl := rdPlanX) hs
  obtain ⟨hq, tw, hX, hmax, hcoh⟩ := h
  obtain ⟨hq', hX'⟩ := takeEff_wr_full hanc.lt E₀ ha hq
  refine ⟨⟨by rw [hr]; exact hq', tw, by rw [hr, hX']; exact hX, fun p hp => hmax p (by rw [hr, hX'] at hp; exact hp)⟩,
    fun hc => ?_⟩
  rw [hcl] at hc
  obtain ⟨-, rF, E'⟩ := hc
  obtain ⟨t, ht⟩ : ∃ t, σ'.snap.threads[tid]? = some t :=
    ⟨σ'.snap.threads[tid]'hanc.lt, Array.getElem?_eq_getElem hanc.lt⟩
  have hp : t.prom.contains tr = false := by
    have := hrd.notOwn
    simp only [ownProm, ht, Option.map_some, Option.getD_some] at this
    exact this
  exact (read_max E' ht hq hX hmax hrd.val hp hrd.window (Nat.le_trans hcoh (Nat.le_max_right _ _))).2

end Kraken.Promising.X64.EnvG.TakeMp

#print axioms Kraken.Promising.X64.EnvG.TakeMp.vc_k1
#print axioms Kraken.Promising.X64.EnvG.TakeMp.vc_k2
#print axioms Kraken.Promising.X64.EnvG.TakeMp.vc_k3
