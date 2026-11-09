/-
**hello's root premises from their base, with `wc_main`'s fields** (AArch64; row: the RootPrem instance builder):
`HelloRootBase.toPrem` and the root's `H1GAH0V` at the box's ghosts, assembled from `CalRootI.h0V_I`
(`WcRootI.wcWf_I`/`wcl_I`, `CalRootI.res_I`/`tcb_I`; rows hP-wcWf, hP-wcl, hP-res, hP-tcb). Moved
out of `A64HelloRootInst` because `WcRootI` imports it.

- `h0V_I`: `H1GAH0V` at the instance: `CalRootI.h0V_I` (`⟨wcWf_I …, res_I …, tcb_I …, wcl_I …⟩`).
- `h0W_I`: `H1GAH0W` from `h0V_I` with `H2Rt`'s runtime fields at `ms2H` (arg `hstat`; the arena is `arW`, the
  base's parameter at `toPrem`).
- `HelloRootBase.toPrem`: the premises at `PlaceW`'s layout and the start's labels `L0T`: `x2_off` by
  `HelloH2Inv.x2H_off`, `hXr` by `X2H`'s take clause, `hP` by `RootHP.hP_of` (its `hl` `Fresh2H`'s, its `hmt`
  `Box.hmt_H`).
- `toPrem_X2`, `toPrem_G`, `toPrem_Wc`: `h2Stmt_root`'s `hX2`, `hG`, `hWc` at `toPrem`.
-/
import Spike.Lib.A64HelloCalRootI

namespace Spike.Lib.A64.HelloPh

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.HelloHMid (BoxPureH slWsH)
open Spike.Lib.A64.Rt.PreChild (r1Of)

namespace HelloRootBase

variable {asm : String}

section ToPrem

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

open Spike.Lib.WakeLoadT (ls0T)

/-- **The root's `H1GAH0V` at a box ghost**: `CalRootI.h0V_I` (`wc_main`'s fields by `WcRootI.wcWf_I`/
`wcl_I`, the reserve's and the TCB's by `CalRootI.res_I`/`tcb_I`; rows hP-wcWf, hP-wcl, hP-res, hP-tcb). -/
theorem h0V_I (B : HelloRootBase (Ly) (LB) (AW) (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E))
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel}
    {b' n' : Nat} (hf : Fresh2H (AW) (LB) l b n l' b' n') {R : Spike.Lib.Region} {F : MachineData → Prop}
    {J1} {t : UInt64} (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.A64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l R F J1 t) :
    Spike.Lib.A64.HelloPh.RootHP.H1GAH0V (Ly) (W2I (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls) l b n l' b' n') (WcI (Ly))
      (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E B.ls l b n l' b' n') l' b' (slWsH l) R F J1 t :=
  Spike.Lib.A64.HelloPh.CalRootI.h0V_I hpw i0 E B hA13 hf hB hG

/-- **`H1GAH0W` from `h0V_I`** at a box ghost: the runtime fields by `H2Rt` at `h2`'s side `ms2H`,
the arena `arW` (the base's parameter), their words unmapped under the pinned ghost's frame condition (`wn_GJ1RH`:
`scc_rt_nthreads` and the spawn words by A13's bytes, the runtime's words by `BoxRF.rtF_of_wn`), the frame on the
first stack by `BoxPureH`'s `R.base + 80`. -/
theorem h0W_I (B : HelloRootBase (Ly) (LB) (AW) (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E))
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) (hstat : Λ0.static = fun _ => none)
    {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel}
    {b' n' : Nat} (hf : Fresh2H (AW) (LB) l b n l' b' n') {R : Spike.Lib.Region} {F : MachineData → Prop}
    {J1} {t : UInt64} (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.A64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l R F J1 t) :
    Spike.Lib.A64.HelloPh.RootHP.H1GAH0W (Ly) (W2I (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls) l b n l' b' n')
      (X2I (Ly) (LB) (ls0T B.ls) l b n l' b' n') (WcI (Ly))
      (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E B.ls l b n l' b' n') Spike.Lib.HelloSrc.helloSrc
      (lbl2H (LB) l b l' b') l' b' (slWsH l) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (AW) B.Dt (ClH (Ly)) B.Ctx
      (ls0T B.ls) (fun _ => B.frM) R F J1 t := by
  have hf' := hf
  have hwn := wn_GJ1RH hpw i0 hG
  have hA := Spike.Lib.A64.WakePh.H1Rt.a13_facts hpw IH hA13
  have hunN : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) 8 = none :=
    fun m h => hwn m h _ fun j hj => (hA.1 j hj).elim (fun h => .inr (.inl h)) fun h => .inr (.inr h)
  have hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly) m :=
    fun m h => Spike.Lib.A64.HelloPh.BoxRF.rtF_of_wn _ (hwn m h)
  have hS : ∀ m, F m → ∀ x ∈ Scc.Cert.Spawn.A64.spawnWords (Ly).pinA, Mem.loadInt m.dmem x 8 = none :=
    fun m h x hx => hwn m h x fun j hj => (hA.2.1 x hx j hj).elim (fun h => .inr (.inl h)) fun h => .inr (.inr h)
  have hb : R.base.toNat + 80 = (Ly).stacksA.toNat + 16384 := hB.2.2.2.2.2.1
  have hun := Spike.Lib.A64.HelloPh.H2Rt.hunSp_H hpw IH hS
  exact (h0V_I hpw i0 E B hA13 hf hB hG).toW
    (Spike.Lib.A64.HelloPh.H2Rt.resA_H2 hpw IH E B.ls B.hlab hstat hA13 hf' hunN)
    (Spike.Lib.A64.HelloPh.H2Rt.hdrA_H hpw IH E B.ls hstat hA13 hf' hun.1)
    (Spike.Lib.A64.HelloPh.H2Rt.tcbA_H hpw IH E B.ls B.hlab hstat hA13 hf'
      (Spike.Lib.A64.HelloPh.H2Rt.bandSp3H_of hb) fun m h => hFr m h _ (Ly).pn_mem)
    (Spike.Lib.A64.HelloPh.H2Rt.tid_H hpw IH E B.ls hstat hA13 hf' hun.2.1)
    (Spike.Lib.A64.HelloPh.H2Rt.hfld_H hpw IH E B.ls hstat hA13 hf' hun.2.2)
    (Spike.Lib.A64.HelloPh.H2Rt.htk_H hpw IH E B.ls B.hlab hstat hA13 hf' hb hFr)

/-- **The root premises from their base** at `PlaceW`'s layout and the start's labels (see the module doc;
`hA13`, `hpin2`: `RootHP.hP_of`'s layout facts; `hstat`: no static label, by `rfl` at both layouts a root can
bind, `hstat_tablesOf` and `hstat_elf`; the arena is `arW`, the base's parameter, its `har` by `har_W`). -/
noncomputable def toPrem (B : HelloRootBase (Ly) (LB) (AW) (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E))
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hstat : Λ0.static = fun _ => none) :
    HelloRootPrem (Ly) (LB) where
    hp := B.hp
    hlo := B.hlo
    hΛ := B.hΛ
    hlab := B.hlab
    hsite := B.hsite
    hro := B.hro
    W1 := B.W1
    ar := AW
    har := B.har
    msB := B.msB
    F0 := B.F0
    ms2 := Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E B.ls
    hK2 := B.hK2
    hpub2 := B.hpub2
    hokb := B.hokb
    hg := B.hg
    Dt := B.Dt
    Ctx := B.Ctx
    lsize := ls0T B.ls
    frM := fun _ => B.frM
    hs := B.hs
    hsub := B.hsub
    hmF := B.hmF
    hnoF := B.hnoF
    hoffT := B.hoffT
    hoffL := B.hoffL
    hoffX := B.hoffX
    W2 := W2I (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls)
    X2 := X2I (Ly) (LB) (ls0T B.ls)
    G := fun l b _ _ _ _ => Spike.Lib.A64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l
    Wc := fun _ _ _ _ _ _ => WcI (Ly)
    x2_off := fun _ _ _ _ _ _ _ _ _ hc ha => Spike.Lib.HelloH2Inv.x2H_off hc ha
    hXr := fun _ _ _ _ _ _ _ s _ _ hX he => (hX.2 (by unfold Scc.Sem.A64.pcOf; rw [he])).1
    hP := fun l b n l' b' n' hf R F J1 t hB hG =>
      Spike.Lib.A64.HelloPh.RootHP.hP_of hpw IH hA13 hpin2 hf.2.2.1 (Spike.Lib.A64.HelloPh.Box.hmt_H hpw i0 hf.1)
        hG ((h0W_I hpw i0 E B hA13 hstat hf hB hG).toH0 hWX_I)

variable {hpw i0 E} (B : HelloRootBase (Ly) (LB) (AW) (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E))
  (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
  (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hstat : Λ0.static = fun _ => none)

/-- `h2Stmt_root`'s `hX2` at `toPrem` (`ls0 := ls0T B.ls`). -/
theorem toPrem_X2 : (B.toPrem hpw i0 E hA13 hpin2 hstat).X2 = fun l b n l' b' n' =>
    Spike.Lib.HelloH2Inv.X2H (Ly) ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (Ly).endPc
      (lbl2H (LB) l b l' b')
      (Spike.Lib.A64ConsumerA.updN (Spike.Lib.A64ConsumerA.updN (ls0T B.ls) l n) l' n') := rfl

/-- `h2Stmt_root`'s `hG` at `toPrem`. -/
theorem toPrem_G : (B.toPrem hpw i0 E hA13 hpin2 hstat).G =
    fun l b _ _ _ _ => Spike.Lib.A64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l := rfl

/-- `h2Stmt_root`'s `hWc` at `toPrem`. -/
theorem toPrem_Wc : ∀ l b n l' b' n' s c, (B.toPrem hpw i0 E hA13 hpin2 hstat).Wc l b n l' b' n' s c →
    Spike.Lib.A64.Flow.Ret0.StackM (r1Of (Ly).lab) s.st.1 :=
  fun _ _ _ _ _ _ _ _ h => h

end ToPrem

end HelloRootBase

end Spike.Lib.A64.HelloPh

/-- info: 'Spike.Lib.A64.HelloPh.HelloRootBase.h0V_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HelloRootBase.h0V_I

/-- info: 'Spike.Lib.A64.HelloPh.HelloRootBase.toPrem_X2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HelloRootBase.toPrem_X2

/-- info: 'Spike.Lib.A64.HelloPh.HelloRootBase.toPrem_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HelloRootBase.toPrem_G

/-- info: 'Spike.Lib.A64.HelloPh.HelloRootBase.toPrem_Wc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HelloRootBase.toPrem_Wc

/-- info: 'Spike.Lib.A64.HelloPh.HelloRootBase.h0W_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HelloRootBase.h0W_I
