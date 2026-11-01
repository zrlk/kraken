/-
**The counter row at a frame-indexed counter add** (AArch64; the twin of `Spike/Lib/A64WakeCtr.lean`'s `hctr0_of`,
`Spike/Lib/A64WakeCtrTp.lean`'s `hctr0_ofT` and `Spike/Lib/A64WakeNew.lean`'s `ctrAt_wr`/`hnew0_of` at
`A64HelloLand`'s `CtrAtF`): the pieces of `OpenW.hctr0`/`hnew0` per disjunct of a context built from counter adds
at any frames and any allocation site (`CtrOkS`), and the box's store (`StAt`).

At the counter add the frame run stays put (a buffer `newBuf` or a box `new`: `FrameRun.eq_of_site`), and
`ctrRow_allocS_n4` gives the row at the call's memory side, landing at `n4`; the row reads no `xa` (`ctrRow_xa`), so
it holds at any memory side `M fs` that is the reference side `ref fs` but for `xa`, the landing in the fragment `J`
at the start's levels (`hland`, at the frames of the add).

- `FrameRun.eq_of_site`, `site_not_ret`: a frame run from an allocation site is empty; the site is no `ret`.
- `ctrRow_ofF`: the counter row at a `CtrAtF` state.
- `ctrRow_ofFT`: as `ctrRow_ofF` under the thread pointer `t`, kept by the add (no `MSR`) into `hland`.
- `ctrAtF_wr`: the counter add writes the counter (`hnew0`'s dismissal of the `CtrAtF` disjuncts).
- `newStM_ofSt`: `hnew0` at a `StAt` state (`WakeCtr.hnew0_of`'s store case at any target side `M`).
-/
import Spike.Lib.A64HelloLand
import Spike.Lib.A64WakeCtrTp
import Spike.Lib.A64WakeNew

namespace Spike.Lib.A64.HelloPh.CtrF

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib (Region FrameRun MemSide Arena FragS Frag AllocSite Pend)
open Spike.Lib.A64ConsumerA (CtrRow PendA WrAt)
open Spike.Lib.A64ConsumerS (InvS)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Flow (At)
open Spike.Lib.A64.Alloc (Call Code N)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.WakeCtr (StAt ctrRow_allocS_n4 ctrRow_xa)
open Spike.Lib.A64.HelloPh.Land (CtrAtF CtrOkS)

variable {p : Prog}

/-- **A frame run from an allocation site is empty** (a buffer: `FrameRun.eq_of_newBuf`; a box:
`FrameRun.eq_of_new`). -/
theorem FrameRun.eq_of_site {N : Prop} {c : Ctl} {fs : List TermRun.Frame} {q' : Ctl × List TermRun.Frame}
    {x : String} {n : Nat} {τ : Ty} {e : Expr} (hr : FrameRun p (c, fs) q') (h : AllocSite N c x n τ e) :
    q' = (c, fs) := by
  rcases h with ⟨a, ta, ws, ht, hea, hk⟩ | ⟨-, a, ws, ht, -, -⟩
  · exact Spike.Lib.A64ConsumerA.FrameRun.eq_of_newBuf hr ht hea hk
  · obtain ⟨_, ht⟩ := ht
    exact Spike.Lib.FrameNew.FrameRun.eq_of_new hr ht

/-- **An allocation site is no `ret`.** -/
theorem site_not_ret {N : Prop} {c : Ctl} {x : String} {n : Nat} {τ : Ty} {e : Expr} (h : AllocSite N c x n τ e) :
    ∀ a, c.term ≠ .ret a := by
  intro b hb
  rcases h with ⟨a, ta, ws, ht, -, -⟩ | ⟨-, a, ws, ⟨_, ht⟩, -, -⟩ <;> rw [ht] at hb <;> cases hb

variable {exe : _root_.Executable} {endPc : Int64}
  {ref : List TermRun.Frame → MemSide isaLSE2}
  {Gc : List TermRun.Frame → MemSide isaLSE2 → Region → (MachineData → Prop) → Call → Prop}
  {M : List TermRun.Frame → MemSide isaLSE2} {J : InvS} {L0 : Lbl} {ls0 : Lsize}

/-- The call's control is the add node's (`N … .rmw`'s invariant). -/
private theorem c_eq {ms0 : MemSide isaLSE2} {R : Region} {F : MachineData → Prop} {q : Call} {s : State}
    {c : Ctl} (hAt : At exe endPc R F (N (_root_.Executable.labels exe).label ms0 q .rmw) s c) : c = q.c0 := by
  obtain ⟨-, -, -, -, σ, -, -, ⟨h, -⟩, -⟩ := hAt; exact h

/-- The row at the call's side, moved to `M fs` (`ctrRow_xa`), its landing at `n4` in `J`. -/
private theorem ctrRow_land {ms0 : MemSide isaLSE2} {R : Region} {F : MachineData → Prop} {q : Call}
    {fs : List TermRun.Frame} {s : State} (hM : M fs = { ref fs with xa := (M fs).xa })
    (hms : ms0 = { ref fs with xa := ms0.xa }) (hsite : ∀ a, q.c0.term ≠ .ret a)
    (hrow : CtrRow ms0 (Spike.Lib.A64.Flow.Next exe endPc R F
      (fun _ : Unit => N (_root_.Executable.labels exe).label ms0 q .n4) (fun x : Empty => x.elim)) s q.c0)
    (hland : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label ms0 q .n4) s c → J L0 ls0 s c fs) :
    CtrRow (M fs) (fun s' c'' => PendA p J L0 ls0 s' c'' fs) s q.c0 := by
  refine ctrRow_xa ?_ (show M fs = { ms0 with xa := (M fs).xa } by rw [hM, hms])
  obtain ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, h7⟩ := hrow
  refine ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, fun old hG hown hle hlo => ?_⟩
  obtain ⟨hG', hL⟩ := h7 old hG hown hle hlo
  refine ⟨hG', fun _ a h => hsite a h, _, _, .refl _, ?_⟩
  rcases hL with ⟨_, hj⟩ | ⟨y, _⟩
  · exact hland _ _ hj
  · exact y.elim

/-- **The counter row at a `CtrAtF` state** (`WakeCtr.hctr0_of`'s counter-add case at any frames and site): the
frame run stays put, the row holds at `M fs` (the reference side `ref fs` but for `xa`, `hM`), its landing at `n4`
in `J` at `L0`, `ls0` (`hland`, for the calls `Gc fs` admits). -/
theorem ctrRow_ofF (hcode : ∀ ms0 q, Code ms0 q exe endPc) (hM : ∀ fs, M fs = { ref fs with xa := (M fs).xa })
    (hland : ∀ fs (ms0 : MemSide isaLSE2) R F q, ms0 = { ref fs with xa := ms0.xa } → Gc fs ms0 R F q →
      CtrOkS ms0 (_root_.Executable.labels exe).label R F q →
      ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label ms0 q .n4) s c → J L0 ls0 s c fs)
    {s : State} {c : Ctl} {fs : List TermRun.Frame} (hC : CtrAtF ref exe endPc Gc s c fs)
    {c' : Ctl} {fs' : List TermRun.Frame} (hr : FrameRun p (c, fs) (c', fs')) :
    CtrRow (M fs') (fun s' c'' => PendA p J L0 ls0 s' c'' fs') s c' := by
  obtain ⟨ms0, R, F, q, hms, hGc, hok, hAt⟩ := hC
  obtain rfl := c_eq hAt
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (FrameRun.eq_of_site hr hok.oks.site)
  exact ctrRow_land (hM fs') hms (site_not_ret hok.oks.site)
    (ctrRow_allocS_n4 hok.fst hok.oks (hcode ms0 q) hok.mem hAt) (hland fs' ms0 R F q hms hGc hok)

/-- **`ctrRow_ofF` under the thread pointer** `t` (`WakeCtr.hctr0_ofT`'s counter-add case): the add (`ldadd`, no
`MSR`) keeps `TP t` into the landing (`KeepTP.exec_tp`), so `hland` may assume it. -/
theorem ctrRow_ofFT {t : UInt64} (hcode : ∀ ms0 q, Code ms0 q exe endPc)
    (hM : ∀ fs, M fs = { ref fs with xa := (M fs).xa })
    (hland : ∀ fs (ms0 : MemSide isaLSE2) R F q, ms0 = { ref fs with xa := ms0.xa } → Gc fs ms0 R F q →
      CtrOkS ms0 (_root_.Executable.labels exe).label R F q →
      ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label ms0 q .n4) s c → TP t s → J L0 ls0 s c fs)
    {s : State} {c : Ctl} {fs : List TermRun.Frame} (hC : CtrAtF ref exe endPc Gc s c fs) (htp : TP t s)
    {c' : Ctl} {fs' : List TermRun.Frame} (hr : FrameRun p (c, fs) (c', fs')) :
    CtrRow (M fs') (fun s' c'' => PendA p J L0 ls0 s' c'' fs') s c' := by
  obtain ⟨ms0, R, F, q, hms, hGc, hok, hAt⟩ := hC
  obtain rfl := c_eq hAt
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (FrameRun.eq_of_site hr hok.oks.site)
  have hnm : Spike.Lib.A64.KeepTP.NoMsrAt s := by
    obtain ⟨he, hn, -, hpc, -⟩ := id hAt
    exact Spike.Lib.A64.Flow.noMsrAt_of_code ((hcode ms0 q).rmw s he hn) (by decide) (j := 0) (by simp) rfl rfl
      (by rw [hpc]; simp)
  have hrow := ctrRow_allocS_n4 hok.fst hok.oks (hcode ms0 q) hok.mem hAt
  refine ctrRow_xa ?_ (show M fs' = { ms0 with xa := (M fs').xa } by rw [hM fs', hms])
  obtain ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, h7⟩ := hrow
  have hT := Spike.Lib.A64.KeepTP.exec_tp hnm htp h1
  refine ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, fun old hG hown hle hlo => ?_⟩
  obtain ⟨hG', hL⟩ := h7 old hG hown hle hlo
  refine ⟨hG', fun _ a h => site_not_ret hok.oks.site a h, _, _, .refl _, ?_⟩
  rcases hL with ⟨_, hj⟩ | ⟨y, _⟩
  · exact hland fs' ms0 R F q hms hGc hok _ _ hj (hT old)
  · exact y.elim

/-- **The counter add writes the counter** (`WakeCtr.ctrAt_wr` at `CtrAtF`), at reference sides whose counter is
the arena's (`hc`). -/
theorem ctrAtF_wr {ar : Arena} (hcode : ∀ ms0 q, Code ms0 q exe endPc) (hc : ∀ fs, (ref fs).ctr = ar.ctr) :
    ∀ s c fs, CtrAtF ref exe endPc Gc s c fs → WrAt s ar.ctrLoc := by
  rintro s c fs ⟨ms0, R, F, q, hms, -, hok, hAt⟩
  obtain ⟨k, op, g, -, -, -, -, h1, -⟩ := ctrRow_allocS_n4 hok.fst hok.oks (hcode ms0 q) hok.mem hAt
  have e : ms0.ctr = ar.ctr := (congrArg MemSide.ctr hms).trans (hc fs)
  refine .inr ⟨k, op, g, ?_⟩
  rw [h1, e]; rfl

/-- **`hnew0` at the box's store** (`WakeCtr.hnew0_of`'s store case, at a target side `M` that is `ref0` but for
`xa`, `hM`): the frame run stays put (a box `new`), the store's `NewStM` holds at `M []`, its landings `Lnd` in
`M []`'s fragment (`hland1`, for the landings `Gs` admits). -/
theorem newStM_ofSt {ref0 : MemSide isaLSE2} {Gs : (WeakMem.AllocLabel → Nat → Nat → Frag isaLSE2) → Prop}
    (hM : M [] = { ref0 with xa := (M []).xa })
    (hland1 : ∀ Lnd, Gs Lnd → ∀ l A s' c', L0 l = none → Lnd l A 1 s' c' → (M []).xa l A 1 s' c')
    {s : State} {c : Ctl} {fs : List TermRun.Frame} (hS : StAt ref0 p L0 Gs s c fs)
    {c' : Ctl} {fs' : List TermRun.Frame} (hr : FrameRun p (c, fs) (c', fs')) :
    NewStM p L0 (M fs') s c' := by
  obtain ⟨rfl, Lnd, hG, kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hacc, hv, hh, hold, hA, hcl,
    hX⟩ := hS
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Spike.Lib.FrameNew.FrameRun.eq_of_new hr ht.choose_spec)
  rw [hM]
  exact ⟨kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hacc, hv, hh, hold, hA, hcl,
    fun l hl => hland1 Lnd hG l _ _ _ hl (hX l hl)⟩

end Spike.Lib.A64.HelloPh.CtrF

/-- info: 'Spike.Lib.A64.HelloPh.CtrF.FrameRun.eq_of_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CtrF.FrameRun.eq_of_site

/-- info: 'Spike.Lib.A64.HelloPh.CtrF.site_not_ret' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CtrF.site_not_ret

/-- info: 'Spike.Lib.A64.HelloPh.CtrF.ctrRow_ofF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CtrF.ctrRow_ofF

/-- info: 'Spike.Lib.A64.HelloPh.CtrF.ctrRow_ofFT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CtrF.ctrRow_ofFT

/-- info: 'Spike.Lib.A64.HelloPh.CtrF.ctrAtF_wr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CtrF.ctrAtF_wr

/-- info: 'Spike.Lib.A64.HelloPh.CtrF.newStM_ofSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CtrF.newStM_ofSt
