/-
**`MainWcPS.hq` at `Level1I`'s choices** (x86-64; the twin of `Spike/Lib/A64HelloMainWcL1Hq.lean`): at any
`PlaceWX` output's runtime layout `Ly := RuntimeLayout.ofPlaceWX hpw i`, the arena `X64.WakeOD.arW hpw i` (its
counter zero-initialised, `CtrZ`), hello's value invariant `X64HelloGOf2H.gWH hpw i (X64WakeHG.cTW hpw i)` (its
second limit word pinned), any marks `μ` (so no certificate text), and the level's labels `upd (L0T Ly.Λ) l b` /
`updN (ls0T ls) l n` at an allocation `AllocLand` of rodata's.

- `rtC_L1`: the counter word is the runtime's at the level's labels: in `.data` (`ctr_item_of_placeW`), off the
  arena that holds `l`'s words (A1, `ArenaW.arOf_sub`), and `L0T` covers no word (`StartH0.rt_L0T`).
- `hq_L1`: `hq` at any `Jr1` whose controls are `c0H`'s (`Land.Jr1LH`'s), by `ArWCall.okb_arW`.

## Differences from the AArch64 version

- Over x86-64's `PlaceWX`, `RuntimeLayout.ofPlaceWX`, `X64.WakeOD.arW`, `X64ConsumerA.msOfA`; `rt_L0T` is wake
  x86-64's (`X64.WakePh.StartH0`). The proofs are AArch64's.
-/
import Spike.Lib.X64HelloMainWcL1Q
import Spike.Lib.X64HelloArWCall

namespace Spike.Lib.X64.HelloPh.MainWcL1Hq

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (lrange)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib (PlaceWX)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64WakeLoadT (L0T ls0T)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw i

set_option hygiene false in
/-- The memory side at hello's choices and the level's labels, any marks, fragment and frames. -/
local notation "MS1" => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ μ rd
  (Spike.Lib.X64HelloGOf2H.gWH hpw i (Spike.Lib.X64WakeHG.cTW hpw i)) own (AR) I
  (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) fs

variable {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {own : Spike.Lib.X64ConsumerS.OwnS}
  {I : Spike.Lib.X64ConsumerS.InvS} {fs : List TermRun.Frame} {ls : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}

/-- **The counter word is the runtime's at the level's labels** (module doc). -/
theorem rtC_L1 (hstat : Λ0.static = fun _ => none) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hb : AllocLand (AR).heap (AR).cells b n) : (MS1).rt (BitVec.ofNat 64 (MS1).ctr).toNat := by
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 :=
    Spike.Lib.X64.Rt.ArenaW.data_below_of_placeW (Spike.Lib.PlaceWX.link i hpw)
  obtain ⟨hc1, hc2, -⟩ : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ ∧
      Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size ∧ _ :=
    Spike.Lib.X64.Rt.ArenaW.ctr_item_of_placeW (Spike.Lib.PlaceWX.link i hpw) hc
  have hct : (MS1).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  have hs : (Scc.Sem.Range.mk (Spike.Lib.X64.Rt.arOf (Ly).Λ).heap (16 * (Spike.Lib.X64.Rt.arOf (Ly).Λ).cells)).Sub
      (Ly).Λ.heap := Spike.Lib.X64.Rt.ArenaW.arOf_sub (Spike.Lib.PlaceWX.link i hpw)
  have hwf : (Ly).Λ.WF := Spike.Lib.PlaceWX.wf_link_of_placeWX i hpw
  have hD : (Ly).Λ.data.Disjoint (Ly).Λ.heap := hwf.disjoint.2.2.2.1
  rw [hct, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rintro ⟨l', b', h1, h2⟩
  by_cases e : l' = l
  · subst e
    simp only [Spike.Lib.X64ConsumerA.upd, Spike.Lib.X64ConsumerA.updN, ite_true, Option.some.injEq, lrange,
      Scc.Sem.Range.contains] at h1 h2
    obtain ⟨hb1, hb2, -⟩ := hb
    change (Spike.Lib.X64.Rt.arOf (Ly).Λ).heap + 8 ≤ b at hb1
    change b + 8 * n ≤ (Spike.Lib.X64.Rt.arOf (Ly).Λ).heap + 16 * (Spike.Lib.X64.Rt.arOf (Ly).Λ).cells at hb2
    simp only [Scc.Sem.Range.Sub, Scc.Sem.Range.Disjoint] at hs hD
    omega
  · simp only [Spike.Lib.X64ConsumerA.upd, e, ite_false] at h1
    simp only [lrange, Spike.Lib.X64ConsumerA.updN, e, ite_false] at h2
    exact Spike.Lib.X64.WakePh.StartH0.rt_L0T (Λ := (Ly).Λ) hstat ls _
      ⟨l', b', h1, h2⟩

/-- **`hq` at `c0H`'s controls** (`MainWcPS.hq`): the box call at a `c0H` control (a `C0Box`) meets `Call.OKB` at
the level's memory side (`ArWCall.okb_arW`), its counter word the runtime's (`rtC_L1`). -/
theorem hq_L1 (hstat : Λ0.static = fun _ => none) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hb : AllocLand (AR).heap (AR).cells b n) {Jr1 : FAS → Spike.Lib.Ctl → Prop}
    (hJ : ∀ σ c, Jr1 σ c → ∃ w0 w1 w2 mw, c = Spike.Lib.X64HelloMainPreSrc.c0H w0 w1 w2 mw) :
    ∀ σ c, Jr1 σ c → ∃ q : Call, q.OKB (MS1) (Ly).lab ∧ q.c0 = c ∧
      q.h = 256#64 ∧ q.k = 1#64 ∧ q.u (MS1) = 2#64 := by
  intro σ c h
  obtain ⟨w0, w1, w2, mw, rfl⟩ := hJ σ c h
  exact Spike.Lib.X64.ArWCall.okb_arW hpw i hc
    (Spike.Lib.X64HelloGOf2H.hGpl_gWH hpw i (Spike.Lib.X64WakeHG.cTW hpw i) hpin2) (rtC_L1 hpw i hstat hc hb)
    ⟨⟨_, rfl⟩, ⟨_, rfl, rfl⟩, rfl⟩

end Spike.Lib.X64.HelloPh.MainWcL1Hq

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Hq.rtC_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Hq.rtC_L1

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Hq.hq_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Hq.hq_L1
