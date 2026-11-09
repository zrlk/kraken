/-
**hello's `wc_main` fields of the root's open premise at the instance: the layout facts** (x86-64; the twin of
`Spike/Lib/A64HelloWcRootI.lean`, its layout part): the band and spawn-word facts the instance's `wcWf` and `wcl`
discharge their premises from.

- `bandTiH_of`: `scc_rt_thread_init`'s frame band on the first stack, from `BoxPureH`'s `R.base + 96`.
- `spw_mem`: `pinA + 112 + 8 j` is a spawn word for `j < 16`.
- `tid_eq`: the second TCB's id word is spawn word `11`.
- `htid3_H`: the second TCB's id word is none of `own2aH`'s words.

The instance's `wcWf` and `wcl` themselves are `CalRootI.wcWf_IX` and `wcl_IX` (at the self words `ownGHXW`).

## Differences from the AArch64 version

- `BandTiH` is `wc_main`'s `%rsp` past the `call` and the callee's `pushq` (`R.addr (-136)`, `R.addr (-144)`;
  AArch64 `[-192, -144]`), and `BoxPureH`'s region is based `96` below the first stack's top (AArch64 `80`), as
  `X64HelloRootHPD` (the same statement as `StackB.bandTiH_of`, as on AArch64).
- AArch64's `wcWf_I` and `wcl_I` (at `ownGH`) have no twins here; the root's `wcWf` and `wcl` are at `ownGHXW`
  (`CalRootI.wcWf_IX`, `wcl_IX`).
-/
import Spike.Lib.X64HelloWcSp4W
import Spike.Lib.X64HelloWcSp3
import Spike.Lib.X64HelloOwn2
import Spike.Lib.X64WakeLdFacts
import Spike.Lib.X64HelloImms
import Spike.Lib.X64HelloRootInst
import Spike.Lib.X64HelloBoxM
import Spike.Lib.X64HelloH2Rt
import Spike.Lib.X64HelloWcl2
import Spike.Lib.X64HelloStackW
import Spike.Lib.X64HelloWcPl2
import Spike.Lib.X64HelloBoxRF
import Spike.Lib.X64WakeH1Rt
import Spike.Lib.X64WakeWfCalOff

namespace Spike.Lib.X64.HelloPh.WcRootI

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64.Flow.HelloWc (tH)

/-- **`scc_rt_thread_init`'s frame band on the first stack** (`WcSp4W.BandTiH`) from `BoxPureH`'s `R.base + 96`
the first stack's top: `R.addr (-144) … R.addr (-136)` lies in the stack pool. -/
theorem bandTiH_of {L : RuntimeLayout} {R : Spike.Lib.Region} (hb : R.base.toNat + 96 = L.stacksA.toNat + 16384) :
    Spike.Lib.X64.HelloPh.WcSp4W.BandTiH L R := by
  intro k h1 h2
  have hB := R.base.isLt
  have he : R.addr k = BitVec.ofInt 64 ((R.base.toNat : Int) + k) := by
    rw [Spike.Lib.Region.addr, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have ha : ((R.addr k).toNat : Int) = R.base.toNat + k := by
    rw [he, BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
      Int.emod_eq_of_lt (by omega) (by omega)]
  have hs := L.stacks_sub
  simp only [Scc.Sem.Range.Sub] at hs
  omega

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : Spike.Lib.PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

/-- `pinA + 112 + 8 j` is a spawn word for `j < 16`. -/
theorem spw_mem {j : Nat} (hj : j < 16) :
    (Ly).pinA + BitVec.ofNat 64 (112 + 8 * j) ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA :=
  List.mem_map.2 ⟨j, List.mem_range.2 (by simp only [Scc.IR.Tcb.size, Scc.IR.maxSpawnArgs]; omega), rfl⟩

/-- The second TCB's id word is spawn word `11`. -/
theorem tid_eq : tH (Ly).lab + 56#64 = (Ly).pinA + BitVec.ofNat 64 (112 + 8 * 11) := by
  show Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 144#64 + 56#64 = _
  rw [(Ly).lab_pin, BitVec.add_assoc]; rfl

/-- **The second TCB's id word is none of `own2aH`'s words** (wake's `LdFacts.htid3_W`). -/
theorem htid3_H (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ w, (⟨tH (Ly).lab + 56#64, 8⟩, w) ∉ Spike.Lib.X64.HelloPh.own2aH (Ly) (ntA (Ly).lab) 0 := by
  intro w hw
  have h := (Spike.Lib.X64.WakePh.LdFacts.spawn_fact hpw IH hA13 (spw_mem hpw i0 (j := 11) (by decide)) true).1
  rw [← tid_eq] at h
  simp only [Spike.Lib.X64.HelloPh.own2aH, Spike.Lib.X64.WakePh.ownV, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq, Loc.mk.injEq] at hw h
  rcases hw with ⟨⟨e, -⟩, -⟩ | ⟨⟨e, -⟩, -⟩ | ⟨⟨e, -⟩, -⟩ | ⟨⟨e, -⟩, -⟩ | ⟨⟨e, -⟩, -⟩ <;> exact h (by simp [e])

end Inst

end Spike.Lib.X64.HelloPh.WcRootI

/-- info: 'Spike.Lib.X64.HelloPh.WcRootI.bandTiH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcRootI.bandTiH_of

/-- info: 'Spike.Lib.X64.HelloPh.WcRootI.htid3_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcRootI.htid3_H
