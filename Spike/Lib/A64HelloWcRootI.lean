/-
**hello's `wc_main` fields of the root's open premise at the instance** (AArch64; rows hP-wcWf, hP-wcl):
`RootHP.H1GAH0V`'s `wcWf` and `wcl` at the root instance's choices (`HelloRootBase` at `PlaceW`'s layout,
the start's labels `L0T`, the arena `arW`, `h2`'s side `H2Rt.ms2H`), at every box ghost `h0` quantifies over.

The level `W2I … l b n l' b' n'` is `RootWX.W2H` at the empty context, the twice extended placement
`lbl2H L0 l b l' b'` and the sizes `updN (updN ls0 l n) l' n'` (`A64HelloW2H.w2H_def`, B8-W2H), so the
generic `WcW2.wcWf_W2Hb` and `Wcl2.wcl_W2GJ1H` apply there. Their premises are discharged from the layout: the
counters' separations (`HelloRootBase.hs`, `CalWf.sepN_W`), the words mapped (`CalWf.hmN_W`, `LdFacts.hmP_W`,
A13's spawn words by `LdFacts.spawn_fact`), the box ghost's frame condition leaving them unmapped (`wn_GJ1RH`,
`H2Rt.hunSp_H`, `BoxRF.rtF_of_wn`), `BoxPureH`'s `R.base + 80` the first stack's top (`H2Rt.bandSp3H_of`;
`wcWf_W2Hb`'s `hbase` as is), the placement past the box (`WcPl2.wcMainW_plGJ1H` at `Box.hmt_H`, `Fresh2H`).

- `spw_mem`: `pinA + 80 + 8 j` is a spawn word for `j < 16`.
- `bandTiH_of`: `scc_rt_thread_init`'s frame band on the first stack, from `R.base + 80`.
- `htid3_H`: the second TCB's id word is none of `own2aH`'s words.
- `wcWf_I`: `H1GAH0V.wcWf` at the instance (row hP-wcWf).
- `wcl_I`: `H1GAH0V.wcl` at the instance (row hP-wcl).
-/
import Spike.Lib.A64HelloRootInst
import Spike.Lib.A64HelloWcl2
import Spike.Lib.A64HelloStackW
import Spike.Lib.A64WakeLdFacts

namespace Spike.Lib.A64.HelloPh.WcRootI

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64.Flow.HelloWc (tH)
open Spike.Lib.HelloHMid (BoxPureH SBH QBH slWsH)
open Spike.Lib.WakeLoadT (ls0T)

/-- **`scc_rt_thread_init`'s frame band on the first stack** (`WcSp4W.BandTiH`) from `BoxPureH`'s `R.base + 80`
the first stack's top: `R.addr (-192) … R.addr (-144)` lies in the stack pool. -/
theorem bandTiH_of {L : RuntimeLayout} {R : Spike.Lib.Region} (hb : R.base.toNat + 80 = L.stacksA.toNat + 16384) :
    Spike.Lib.A64.HelloPh.WcSp4W.BandTiH L R := by
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

variable {asm : String}
variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : Spike.Lib.PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat) (E : Scc.Sem.Entry)

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "LB" => Spike.Lib.WakeLoadT.L0T (Ly).Λ

set_option hygiene false in
local notation "AW" => Spike.Lib.WakeOD.arW hpw IH

/-- `pinA + 80 + 8 j` is a spawn word for `j < 16`. -/
theorem spw_mem {j : Nat} (hj : j < 16) :
    (Ly).pinA + BitVec.ofNat 64 (80 + 8 * j) ∈ Scc.Cert.Spawn.A64.spawnWords (Ly).pinA :=
  List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩

/-- The second TCB's id word is spawn word `11`. -/
theorem tid_eq : tH (Ly).lab + 56#64 = (Ly).pinA + BitVec.ofNat 64 (80 + 8 * 11) := by
  show Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 112#64 + 56#64 = _
  rw [(Ly).lab_pin, BitVec.add_assoc]; rfl

/-- **The second TCB's id word is none of `own2aH`'s words** (wake's `LdFacts.htid3_W`). -/
theorem htid3_H (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ w, (⟨tH (Ly).lab + 56#64, 8⟩, w) ∉ Spike.Lib.A64.HelloPh.own2aH (Ly) (ntA (Ly).lab) 0 := by
  intro w hw
  have h := (Spike.Lib.A64.WakePh.LdFacts.spawn_fact hpw IH hA13 (spw_mem hpw i0 (j := 11) (by decide)) true).1
  rw [← tid_eq] at h
  simp only [Spike.Lib.A64.HelloPh.own2aH, Spike.Lib.A64.WakePh.ownV, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq, Loc.mk.injEq] at hw h
  rcases hw with ⟨⟨e, -⟩, -⟩ | ⟨⟨e, -⟩, -⟩ | ⟨⟨e, -⟩, -⟩ | ⟨⟨e, -⟩, -⟩ | ⟨⟨e, -⟩, -⟩ <;> exact h (by simp [e])

variable {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {t : UInt64}

/-- (row hP-wcWf) **`H1GAH0V.wcWf` at the root instance**: `wc_main`'s own nodes inside the level `W2I` at every
box ghost (`Fresh2H`, `BoxPureH`, `GJ1RH`), from `WcW2.wcWf_W2Hb` at the empty context, `lbl2H` and the twice
extended sizes; its word premises from the layout and the ghost's frame condition (see the module doc). -/
theorem wcWf_I (B : HelloRootBase (Ly) (LB) (AW) (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E))
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) (hf : Fresh2H (AW) (LB) l b n l' b' n')
    (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.A64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l R F J1 t) :
    Spike.Lib.A64.Flow.HelloWc.WcMainWH (fun s c => W2I (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls) l b n l' b' n' s c [])
      (fun _ _ => False) (Ly).exe (Ly).endPc R F F
      (Spike.Lib.A64.KeepTP.tpXa (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E B.ls l b n l' b' n' [])
        t) J1 (SBH l' b' (slWsH l)) (QBH l' b' (slWsH l)) := by
  obtain ⟨hR, hal, -, hRlo, hhi, hb, -⟩ := hB
  have hwn := Spike.Lib.A64.HelloPh.HelloRootBase.wn_GJ1RH hpw i0 hG
  have hA := Spike.Lib.A64.WakePh.H1Rt.a13_facts hpw IH hA13
  have hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none :=
    fun m h => hwn m h _ fun j hj => (hA.1 j hj).elim (fun h => .inr (.inl h)) fun h => .inr (.inr h)
  have hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly) m :=
    fun m h => Spike.Lib.A64.HelloPh.BoxRF.rtF_of_wn _ (hwn m h)
  have hS : ∀ m, F m → ∀ x ∈ Scc.Cert.Spawn.A64.spawnWords (Ly).pinA, Mem.loadInt m.dmem x 8 = none :=
    fun m h x hx => hwn m h x fun j hj => (hA.2.1 x hx j hj).elim (fun h => .inr (.inl h)) fun h => .inr (.inr h)
  have hun := Spike.Lib.A64.HelloPh.H2Rt.hunSp_H hpw IH hS
  have sp3 := Spike.Lib.A64.WakePh.LdFacts.spawn_fact hpw IH hA13 (spw_mem hpw i0 (j := 3) (by decide)) true
  have sp11 := Spike.Lib.A64.WakePh.LdFacts.spawn_fact hpw IH hA13 (spw_mem hpw i0 (j := 11) (by decide)) true
  have e3 : (Ly).pinA + BitVec.ofNat 64 (80 + 8 * 3) = (Ly).pinA + 80#64 + 24#64 := by
    rw [BitVec.add_assoc]; rfl
  have e3' : (Ly).pinA + BitVec.ofNat 64 (80 + 8 * 3) = (Ly).pinA + 104#64 := rfl
  have hs := B.hs
  exact Spike.Lib.A64.HelloPh.WcW2.wcWf_W2Hb (L := Ly) (ar := AW) (Dt := B.Dt) (Ctx := fun _ _ _ => False)
    (lbl := lbl2H (LB) l b l' b')
    (lsize := Spike.Lib.A64ConsumerA.updN (Spike.Lib.A64ConsumerA.updN (ls0T B.ls) l n) l' n')
    B.hp B.hlo B.hΛ B.hlab B.hsite hR hal (by omega) hhi
    (Spike.Lib.A64.WakePh.CalWf.sepN_W hpw IH hA13) (Spike.Lib.A64.WakePh.CalWf.hmN_W hpw IH hA13 true) hunN
    (Spike.Lib.A64.HelloPh.H2Rt.bandSp3H_of hb) ⟨hs.pn_lock, hs.pn_freeN, hs.pn_next, hs.pn_a⟩ (e3 ▸ sp3.1)
    (Spike.Lib.A64.WakePh.LdFacts.hmP_W hpw IH) (e3' ▸ sp3.2) (fun m h => hFr m h _ (Ly).pn_mem) hun.1
    hb ⟨tid_eq hpw i0 ▸ sp11.2, hun.2.1, htid3_H hpw i0 hA13⟩
    (Spike.Lib.A64.HelloPh.WcPl2.wcMainW_plGJ1H (by omega) hhi hf.2.2.1
      (Spike.Lib.A64.HelloPh.Box.hmt_H hpw i0 hf.1) hG.1)
    (Spike.Lib.A64.HelloPh.H2Rt.hoff56_H hpw IH hA13)

/-- (row hP-wcl) **`H1GAH0V.wcl` at the root instance**: at the clone's `svc`, the level `W2I` and the clone fact
`WcI`, at every box ghost, from `Wcl2.wcl_W2GJ1H` at the empty context, `lbl2H` and the twice extended sizes. -/
theorem wcl_I (B : HelloRootBase (Ly) (LB) (AW) (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E))
    (hf : Fresh2H (AW) (LB) l b n l' b' n') (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.A64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l R F J1 t) :
    ∀ s c sl me cA fr, Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc R F
      (Spike.Lib.A64.HelloPh.WcSp6.wcNSH (Ly).lab c (tH (Ly).lab) (Spike.Lib.A64.Flow.WakeWc.kOf (Ly).lab) sl me cA fr)
      s c →
      Spike.Lib.HelloMainPreSrc.SpawnSrcH l' (slWsH l) c → cA.toNat = b' →
      Spike.Lib.A64.Flow.HelloWc.FrMGH J1 fr sl me →
      Spike.Lib.A64.Flow.Ret0.StackM (Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab) s.st.1 →
      W2I (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls) l b n l' b' n' s c [] ∧ WcI (Ly) s c := by
  obtain ⟨-, -, -, hRlo, hhi, -⟩ := hB
  exact Spike.Lib.A64.HelloPh.Wcl2.wcl_W2GJ1H (ar := AW) (Dt := B.Dt) (Ctx := fun _ _ _ => False)
    (lsize := Spike.Lib.A64ConsumerA.updN (Spike.Lib.A64ConsumerA.updN (ls0T B.ls) l n) l' n')
    B.hp B.hlo B.hΛ B.hlab B.hsite (by omega) hhi hf.2.2.1 (Spike.Lib.A64.HelloPh.Box.hmt_H hpw i0 hf.1) hG.1

end Inst

end Spike.Lib.A64.HelloPh.WcRootI

/-- info: 'Spike.Lib.A64.HelloPh.WcRootI.bandTiH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcRootI.bandTiH_of

/-- info: 'Spike.Lib.A64.HelloPh.WcRootI.wcWf_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcRootI.wcWf_I

/-- info: 'Spike.Lib.A64.HelloPh.WcRootI.wcl_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcRootI.wcl_I
