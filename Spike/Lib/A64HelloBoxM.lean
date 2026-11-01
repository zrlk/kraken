/-
**hello.w's box landing with its ghosts** (AArch64; `hCI` part 2): a landing
of the box's store at level 1 with `wc_main`'s entry pinned as `Land.GsH1` pins it (`Jr1LH l b`, the caller's slot
`-80` main's TCB) is `HelloHMid.BoxMH` (`hmid`'s pre) at the ghost facts `HelloH2G.GJ1H` at the level's labels
`upd LB l b` and rodata's label `l`, and the slice `slWsH l`.

The region facts are `Box.box_regH`'s; `GJ1H` is the pin itself; `QBH` is read off `bXH`'s control: the entry
control is `Jr1LH`'s `c0H (loc l) 2 13 mwH`, so the allocator's call is `let o = new z in boxTermH` at `.int`
(`Call.OKB`'s `term`/`ev`, as `Hxa.box_landing`), and past it `o` is the box's locative, `me` main's and `sl`
rodata's slice.

- `boxMH_landingH`: the landing is `BoxMH … (GJ1H (Ly) (upd LB l b) l) l' A (slWsH l) 1`.
- `hmt_H`, `hCI_H`: main's id at its TCB at `upd LB l b`; `HelloH2CP.hCP_of`'s `hCI` at these ghosts.
-/
import Spike.Lib.A64HelloBox
import Spike.Lib.A64HelloH2G
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.A64.HelloPh.Box

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib (Region MemSide FragS)
open Spike.Lib.A64.Flow (swR At FStable)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.A64.Flow.HelloWc (bXH)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.Land (ref1H Jr1LH)
open Spike.Lib.HelloHMid (BoxMH slWsH)
open Spike.Lib.HelloH2G (GJ1H)
open Spike.Lib.WakeLoadT (L0T)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

/-- **A pinned box store's landing is `BoxMH`** at `ref1H l b n []`, the ghost facts `GJ1H (Ly) (upd LB l b) l`
and rodata's slice `slWsH l` (see the module doc), given `wc_main`'s frame condition inside `F0` (`hF0`). -/
theorem boxMH_landingH {F0 : MachineData → Prop}
    (hF0 : ∀ v m1 σ1 m, wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1 m → F0 m)
    {l : WeakMem.AllocLabel} {b n : Nat} {v : BitVec 64} {σC : FAS} {m1 : MachineData} {σ1 : FAS}
    {l' : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Spike.Lib.Ctl}
    (hslot : σC.slot (-80) = pinA (Ly).lab + 0#64 + 8#64)
    (hA : At (Ly).exe (Ly).endPc (wcR (swR v (-helloLsw) 0) helloD)
      (wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1)
      (bXH (ref1H (asm := asm) hpw i0 E rd ls l b n []) (Ly).lab (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) l'
          A) s c)
    (htp : TP (TV) s) :
    BoxMH (Ly) (ref1H (asm := asm) hpw i0 E rd ls l b n []) F0 (GJ1H (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l) l' A
      (slWsH l) 1 s c := by
  obtain ⟨R, F, ⟨hR, hRal, hRF, hlo, hhi, hbase⟩, hF, hA'⟩ := box_regH hpw i0 E rd ls hF0 hA
  have hA0 := hA'
  obtain ⟨-, -, -, -, σ, -, -, q, ⟨σe, ⟨-, σx, ⟨hq0, -⟩, -⟩, -⟩, -, hc, -⟩ := hA'
  obtain ⟨T, ht⟩ := q.2.term
  rw [hq0] at ht
  obtain ⟨hx, ha, hee⟩ := Expr.let_.inj ht
  have ha' := (Op.new.inj ha).1
  have hev := q.2.ev
  rw [hq0, ← ha'] at hev
  have hτ : q.1.τ = .int := (Prod.mk.inj (Option.some.inj hev)).1.symm
  rw [← hx, ← hee, hτ, hq0] at hc
  subst hc
  refine ⟨R, F, _, TV, ⟨hR, hRal, hRF, hlo, hhi, hbase, tv_toNat hpw i0, rfl, hF⟩,
    ⟨σC, σ1, Jr1LH hpw i0 l b, hslot, fun _ _ h => h.2, rfl⟩, ⟨hA0, htp⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **main's id at its TCB** at the level's labels `upd LB l b` (`WakeHClW.hme_W`'s twin; `l` fresh at `LB`, so not
main's id label). -/
theorem hmt_H {l : WeakMem.AllocLabel} {b : Nat} (hl : (LB) l = none) :
    Spike.Lib.A64ConsumerA.upd (LB) l b (Spike.Lib.WakeT1.mainTidLbl 2) = some ((Ly).pinA.toNat + 8) := by
  have hp0 := Spike.Lib.PlaceW.pinA_toNat_ofPlaceW hpw IH
  have hsm := (Ly).words_small _ (Ly).pin_mem
  have hme : (LB) (Spike.Lib.WakeT1.mainTidLbl 2) = some ((Ly).pinA.toNat + 8) := by
    simp only [Spike.Lib.WakeLoadT.L0T, Spike.Lib.A64ConsumerA.upd, ↓reduceIte, Spike.Lib.WakeLoadT.tcb0,
      Option.some.injEq]
    omega
  have hne : Spike.Lib.WakeT1.mainTidLbl 2 ≠ l := by intro h; rw [h, hl] at hme; cases hme
  show (if _ = l then _ else _) = _
  split
  · exact absurd ‹_› hne
  · exact hme

/-- **`hCP_of`'s `hCI` at the root's ghosts** (`cloneInvH_of_mid` with `HelloH2G.hG_of`): at a `CloneMidH` state at
`G := GJ1H (Ly) (upd LB l b) l` and rodata's slice `slWsH l`, main is `CloneInvH` at the twice extended placement
`upd (upd LB l b) l' b'`, for `l` fresh at `LB` and the box `l'` fresh at `upd LB l b`. -/
theorem hCI_H {F0 : MachineData → Prop} {W : FragS isaLSE2} {Wc : Spike.Lib.Frag isaLSE2}
    {l : WeakMem.AllocLabel} {b : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}
    (hl : (LB) l = none) (hl' : Spike.Lib.A64ConsumerA.upd (LB) l b l' = none) :
    ∀ s c fs, Spike.Lib.HelloHMid.CloneMidH (Ly) F0 (GJ1H (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l) W Wc l' b'
        (slWsH l) n' s c fs →
      Spike.Lib.HelloPreA.CloneInvH (Ly) (Ly).endPc
        (Spike.Lib.A64ConsumerA.upd (Spike.Lib.A64ConsumerA.upd (LB) l b) l' b') s c [] :=
  Spike.Lib.HelloH2CP.cloneInvH_of_mid (by simp [Spike.Lib.A64ConsumerA.upd])
    (Spike.Lib.HelloH2G.hG_of hl' (hmt_H hpw i0 hl))

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw IH

set_option hygiene false in
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

end Spike.Lib.A64.HelloPh.Box

/-- info: 'Spike.Lib.A64.HelloPh.Box.boxMH_landingH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Box.boxMH_landingH

/-- info: 'Spike.Lib.A64.HelloPh.Box.hCI_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Box.hCI_H
