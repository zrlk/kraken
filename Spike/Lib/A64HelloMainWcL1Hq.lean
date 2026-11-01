/-
**`MainWcPS.hq` at `Level1I`'s choices** (AArch64; `Level1I.hP`'s field, stage 3): at any `PlaceW`
output's runtime layout `Ly := RuntimeLayout.ofPlaceW hpw i`, the arena `WakeOD.arW hpw i` (its counter
zero-initialised, `CtrZ`), hello's value invariant `HelloGOf2H.gWH hpw i (WakeHG.cTW hpw i)` (its second limit word
pinned), any marks `μ` (so no certificate text), and the level's labels `upd (L0T Ly.Λ) l b` / `updN (ls0T ls) l n`
at an allocation `AllocLand` of rodata's.

- `rtC_L1`: the counter word is the runtime's at the level's labels: in `.data` (`ctr_item_of_placeW`), off the
  arena that holds `l`'s words (A1, `ArenaW.arOf_sub`), and `L0T` covers no word (`StartH0.rt_L0T`).
- `hq_L1`: `hq` at any `Jr1` whose controls are `c0H`'s (`Land.Jr1LH`'s), by `ArWCall.okb_arW`.
-/
import Spike.Lib.A64HelloMainWcL1Q
import Spike.Lib.A64HelloArWCall

namespace Spike.Lib.A64.HelloPh.MainWcL1Hq

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (lrange)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.WakeLoadT (L0T ls0T)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw i

set_option hygiene false in
/-- The memory side at hello's choices and the level's labels, any marks, fragment and frames. -/
local notation "MS1" => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ μ rd
  (Spike.Lib.HelloGOf2H.gWH hpw i (Spike.Lib.WakeHG.cTW hpw i)) own (AR) I
  (Spike.Lib.A64ConsumerA.upd (L0T (Ly).Λ) l b) (Spike.Lib.A64ConsumerA.updN (ls0T ls) l n) fs

variable {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {own : Spike.Lib.A64ConsumerS.OwnS}
  {I : Spike.Lib.A64ConsumerS.InvS} {fs : List TermRun.Frame} {ls : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}

/-- **The counter word is the runtime's at the level's labels** (module doc). -/
theorem rtC_L1 (hstat : Λ0.static = fun _ => none) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hb : AllocLand (AR).heap (AR).cells b n) : (MS1).rt (BitVec.ofNat 64 (MS1).ctr).toNat := by
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 :=
    Spike.Lib.A64.Rt.ArenaW.data_below_of_placeW (Spike.Lib.PlaceW.link i hpw)
  obtain ⟨hc1, hc2, -⟩ : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ ∧
      Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size ∧ _ :=
    Spike.Lib.A64.Rt.ArenaW.ctr_item_of_placeW (Spike.Lib.PlaceW.link i hpw) hc
  have hct : (MS1).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  have hs : (Scc.Sem.Range.mk (Spike.Lib.A64.Rt.arOf (Ly).Λ).heap (16 * (Spike.Lib.A64.Rt.arOf (Ly).Λ).cells)).Sub
      (Ly).Λ.heap := Spike.Lib.A64.Rt.ArenaW.arOf_sub (Spike.Lib.PlaceW.link i hpw)
  have hwf : (Ly).Λ.WF := Spike.Lib.PlaceW.wf_link_of_placeW i hpw
  have hD : (Ly).Λ.data.Disjoint (Ly).Λ.heap := hwf.disjoint.2.2.2.1
  rw [hct, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rintro ⟨l', b', h1, h2⟩
  by_cases e : l' = l
  · subst e
    simp only [Spike.Lib.A64ConsumerA.upd, Spike.Lib.A64ConsumerA.updN, ite_true, Option.some.injEq, lrange,
      Scc.Sem.Range.contains] at h1 h2
    obtain ⟨hb1, hb2, -⟩ := hb
    change (Spike.Lib.A64.Rt.arOf (Ly).Λ).heap + 8 ≤ b at hb1
    change b + 8 * n ≤ (Spike.Lib.A64.Rt.arOf (Ly).Λ).heap + 16 * (Spike.Lib.A64.Rt.arOf (Ly).Λ).cells at hb2
    simp only [Scc.Sem.Range.Sub, Scc.Sem.Range.Disjoint] at hs hD
    omega
  · simp only [Spike.Lib.A64ConsumerA.upd, e, ite_false] at h1
    simp only [lrange, Spike.Lib.A64ConsumerA.updN, e, ite_false] at h2
    exact Spike.Lib.A64.WakePh.StartH0.rt_L0T (Λ := (Ly).Λ) hstat ls _
      ⟨l', b', h1, h2⟩

/-- **`hq` at `c0H`'s controls** (`MainWcPS.hq`): the box call at a `c0H` control (a `C0Box`) meets `Call.OKB` at
the level's memory side (`ArWCall.okb_arW`), its counter word the runtime's (`rtC_L1`). -/
theorem hq_L1 (hstat : Λ0.static = fun _ => none) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hb : AllocLand (AR).heap (AR).cells b n) {Jr1 : FAS → Spike.Lib.Ctl → Prop}
    (hJ : ∀ σ c, Jr1 σ c → ∃ w0 w1 w2 mw, c = Spike.Lib.HelloMainPreSrc.c0H w0 w1 w2 mw) :
    ∀ σ c, Jr1 σ c → ∃ q : Call, q.OKB (MS1) (Ly).lab ∧ q.c0 = c ∧
      q.h = 256#64 ∧ q.k = 1#64 ∧ q.u (MS1) = 2#64 := by
  intro σ c h
  obtain ⟨w0, w1, w2, mw, rfl⟩ := hJ σ c h
  exact Spike.Lib.A64.ArWCall.okb_arW hpw i hc
    (Spike.Lib.HelloGOf2H.hGpl_gWH hpw i (Spike.Lib.WakeHG.cTW hpw i) hpin2) (rtC_L1 hpw i hstat hc hb)
    ⟨⟨_, rfl⟩, ⟨_, rfl, rfl⟩, rfl⟩

end Spike.Lib.A64.HelloPh.MainWcL1Hq

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Hq.rtC_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Hq.rtC_L1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Hq.hq_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Hq.hq_L1
