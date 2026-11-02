/-
**hello's `wc_main` fields of the root's open premise at the instance: the layout facts** (x86-64; the twin of
`Spike/Lib/A64HelloWcRootI.lean`, its layout part): the band and spawn-word facts the instance's `wcWf` and `wcl`
discharge their premises from.

- `bandTiH_of`: `scc_rt_thread_init`'s frame band on the first stack, from `BoxPureH`'s `R.base + 96`.
- `spw_mem`: `pinA + 80 + 8 j` is a spawn word for `j < 16`.
- `tid_eq`: the second TCB's id word is spawn word `11`.
- `htid3_H`: the second TCB's id word is none of `own2aH`'s words.
- `wcl_I`: `H1GAH0V.wcl` at the instance.
- `wcWf_I`: `H1GAH0V.wcWf` at the instance.

`wcl_I` and `wcWf_I` are generic in `h2`'s memory side family `ms2` (the base's parameter; `H2Rt.ms2H` at the
root's `ownGH` instance, `H2RtX.ms2HX` at `ownGHXW`): their proofs read only the base's other fields.

## Differences from the AArch64 version

- `BandTiH` is `wc_main`'s `%rsp` past the `call` and the callee's `pushq` (`R.addr (-136)`, `R.addr (-144)`;
  AArch64 `[-192, -144]`), and `BoxPureH`'s region is based `96` below the first stack's top (AArch64 `80`), as
  `X64HelloRootHPD` (the same statement as `StackB.bandTiH_of`, as on AArch64).
- `wcWf_I`'s placement `WcPl2.wcMainW_plGJ1H` is at the box's source facts `QBH` and past the publication (AArch64
  at `SBH`), asking `R.lo ≤ -48`; its band comes from `BoxPureH`'s base through `StackW.wcWf_W2Hb`.
- `wcl_I` asks `Wcl2.wcl_W2GJ1H`'s `R.lo ≤ -48` (AArch64 `-144`), from `BoxPureH`'s `R.lo ≤ -384`.
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

/-- `pinA + 80 + 8 j` is a spawn word for `j < 16`. -/
theorem spw_mem {j : Nat} (hj : j < 16) :
    (Ly).pinA + BitVec.ofNat 64 (80 + 8 * j) ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA :=
  List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩

/-- The second TCB's id word is spawn word `11`. -/
theorem tid_eq : tH (Ly).lab + 56#64 = (Ly).pinA + BitVec.ofNat 64 (80 + 8 * 11) := by
  show Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 112#64 + 56#64 = _
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

section Wcl

variable {ms2 : Spike.Lib.X64Consumer.Lsize → WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat →
    List TermRun.Frame → Spike.Lib.MemSide isa}
variable {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {t : UInt64}

set_option hygiene false in
local notation "LB" => Spike.Lib.X64WakeLoadT.L0T (Ly).Λ

set_option hygiene false in
local notation "AW" => Spike.Lib.X64.WakeOD.arW hpw IH

/-- **`H1GAH0V.wcl` at the root instance**: at the clone's `syscall`, the level `W2I` and the clone fact `WcI`, at
every box ghost, from `Wcl2.wcl_W2GJ1H` at the empty context, `lbl2H` and the twice extended sizes. -/
theorem wcl_I (B : Spike.Lib.X64.HelloPh.HelloRootBase (Ly) (LB) (AW)
      ms2)
    (hf : Spike.Lib.X64.HelloPh.Fresh2H (AW) (LB) l b n l' b' n')
    (hB : Spike.Lib.X64HelloHMid.BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.X64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l R F J1 t) :
    ∀ s c sl me cA fr, Spike.Lib.X64.At (Ly).exe (Ly).endPc R F
      (Spike.Lib.X64.HelloPh.WcSp6.wcNSH (Ly).lab c (tH (Ly).lab) (Spike.Lib.X64.Flow.WakeWc.kOf (Ly).lab) sl me
        cA fr) s c →
      Spike.Lib.X64HelloMainPreSrc.SpawnSrcH l' (Spike.Lib.X64HelloHMid.slWsH l) c → cA.toNat = b' →
      Spike.Lib.X64.Flow.HelloWc.FrMGH J1 fr sl me →
      Spike.Lib.X64.Flow.Ret0.StackM (Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab) s.st.1 →
      Spike.Lib.X64.HelloPh.W2I (Ly) (AW) B.Dt B.Ctx (LB) (Spike.Lib.X64WakeLoadT.ls0T B.ls) l b n l' b' n' s c [] ∧
        Spike.Lib.X64.HelloPh.WcI (Ly) s c := by
  obtain ⟨-, -, -, hRlo, hhi, -⟩ := hB
  exact Spike.Lib.X64.HelloPh.Wcl2.wcl_W2GJ1H (ar := AW) (Dt := B.Dt) (Ctx := fun _ _ _ => False)
    (lsize := Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T B.ls) l n) l' n')
    B.hp B.hlo B.hΛ B.hlab B.hsite (by omega) (by omega) hf.2.2.1 (Spike.Lib.X64.HelloPh.Box.hmt_H hpw i0 hf.1)
    hG.1

/-- **`H1GAH0V.wcWf` at the root instance**: `wc_main`'s own nodes inside the level `W2I` at every box ghost
(`Fresh2H`, `BoxPureH`, `GJ1RH`), from `WcW2.wcWf_W2Hb` at the empty context, `lbl2H` and the twice extended
sizes: its word premises from the layout and A13 (the counters' and the second TCB's words unmapped under the box
ghost's frame condition, `HelloRootBase.wn_GJ1RH`), its placement `WcPl2.wcMainW_plGJ1H`. -/
theorem wcWf_I (B : Spike.Lib.X64.HelloPh.HelloRootBase (Ly) (LB) (AW)
      ms2)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hf : Spike.Lib.X64.HelloPh.Fresh2H (AW) (LB) l b n l' b' n')
    (hB : Spike.Lib.X64HelloHMid.BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.X64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l R F J1 t) :
    Spike.Lib.X64.Flow.HelloWc.WcMainWH
      (fun s c => Spike.Lib.X64.HelloPh.W2I (Ly) (AW) B.Dt B.Ctx (LB) (Spike.Lib.X64WakeLoadT.ls0T B.ls) l b n l'
        b' n' s c [])
      (fun _ _ => False) (Ly).exe (Ly).endPc R F F
      (Spike.Lib.X64.KeepTP.tpXa (ms2 B.ls l b n l' b' n' []) t) J1
      (Spike.Lib.X64HelloHMid.QBH l' b' (Spike.Lib.X64HelloHMid.slWsH l)) := by
  obtain ⟨hR, hal, -, hRlo, hhi, hb, -⟩ := hB
  have hwn := Spike.Lib.X64.HelloPh.HelloRootBase.wn_GJ1RH hpw i0 hG
  have hA := Spike.Lib.X64.WakePh.H1Rt.a13_facts hpw IH hA13
  have hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none :=
    fun m h => hwn m h _ fun j hj => (hA.1 j hj).elim (fun h => .inr (.inl h)) fun h => .inr (.inr h)
  have hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m :=
    fun m h => Spike.Lib.X64.HelloPh.BoxRF.rtF_of_wn _ (hwn m h)
  have hS : ∀ m, F m → ∀ x ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA, Mem.loadInt m.dmem x 8 = none :=
    fun m h x hx => hwn m h x fun j hj => (hA.2.1 x hx j hj).elim (fun h => .inr (.inl h)) fun h => .inr (.inr h)
  have hun := Spike.Lib.X64.HelloPh.H2Rt.hunSp_H hpw IH hS
  have sp3 := Spike.Lib.X64.WakePh.LdFacts.spawn_fact hpw IH hA13 (spw_mem hpw i0 (j := 3) (by decide)) true
  have sp11 := Spike.Lib.X64.WakePh.LdFacts.spawn_fact hpw IH hA13 (spw_mem hpw i0 (j := 11) (by decide)) true
  have e3 : (Ly).pinA + BitVec.ofNat 64 (80 + 8 * 3) = (Ly).pinA + 80#64 + 24#64 := by
    rw [BitVec.add_assoc]; rfl
  have e3' : (Ly).pinA + BitVec.ofNat 64 (80 + 8 * 3) = (Ly).pinA + 104#64 := rfl
  have hs := B.hs
  exact Spike.Lib.X64.HelloPh.WcW2.wcWf_W2Hb (L := Ly) (ar := AW) (Dt := B.Dt) (Ctx := fun _ _ _ => False)
    (lbl := Spike.Lib.X64.HelloPh.lbl2H (LB) l b l' b')
    (lsize := Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T B.ls) l n) l' n')
    B.hp B.hlo B.hΛ B.hlab B.hsite hR (by omega) (by omega) hhi
    (Spike.Lib.X64.WakePh.CalWf.sepN_W hpw IH hA13) (Spike.Lib.X64.WakePh.CalWf.hmN_W hpw IH hA13 true) hunN
    (Spike.Lib.X64.HelloPh.H2Rt.bandSp3H_of hb) ⟨hs.pn_lock, hs.pn_freeN, hs.pn_next, hs.pn_a⟩ (e3 ▸ sp3.1)
    (Spike.Lib.X64.WakePh.LdFacts.hmP_W hpw IH) (e3' ▸ sp3.2) (fun m h => hFr m h _ (Ly).pn_mem) hun.1
    hb ⟨tid_eq hpw i0 ▸ sp11.2, hun.2.1, htid3_H hpw i0 hA13⟩
    (Spike.Lib.X64.HelloPh.WcPl2.wcMainW_plGJ1H (by omega) (by omega) hf.2.2.1
      (Spike.Lib.X64.HelloPh.Box.hmt_H hpw i0 hf.1) hG.1)
    (Spike.Lib.X64.HelloPh.H2Rt.hoff56_H hpw IH hA13)

end Wcl

end Inst

end Spike.Lib.X64.HelloPh.WcRootI

/-- info: 'Spike.Lib.X64.HelloPh.WcRootI.bandTiH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcRootI.bandTiH_of

/-- info: 'Spike.Lib.X64.HelloPh.WcRootI.htid3_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcRootI.htid3_H

/-- info: 'Spike.Lib.X64.HelloPh.WcRootI.wcl_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcRootI.wcl_I

/-- info: 'Spike.Lib.X64.HelloPh.WcRootI.wcWf_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcRootI.wcWf_I
