/-
**hello's `wc_main` callee fields of the root's open premise at the instance** (x86-64; the twin of
`Spike/Lib/A64HelloCalRootI.lean`): `RootHP.H1GAH0V`'s `res` and `tcb` (`RootHP.ResV`, `RootHP.TcbV`) at the root
instance's choices (`HelloRootBase` at `PlaceWX`'s layout, the start's labels `L0T`, the arena `arW`, `h2`'s side
`H2Rt.ms2H`), at every box ghost `h0` quantifies over, at the level `W2I … l b n l' b' n'`.

The callees' nodes are `CalW2.reserveW_W2H` / `tcbWG_W2H` inside `RootWX.W2H` at the empty context, `lbl2H` and the
twice extended sizes: their `SFactsSt2` at `ownGH` from `WcMidWG.wcMidW_wcGH` (`res`, `sp3`'s `tcb`), their
placement from `CalPl.reserveW_placedH` / `tcbWG_placedH` at `SpawnPl.hplQ_GJ1H`, the controls from the box's
source facts (`WcW2.ctlH`; the reserve's frame condition is empty at a control off them, `CalWf.reserveW_vac`), the
counters' and the header's words unmapped under the box ghost's frame condition (`HelloRootBase.wn_GJ1RH`) and off
the arena (`CalWf.hoffN_W`, `CalWf.hoffP_W`, `H2Rt.hoffSp_H` at spawn word `3`).

- `mid_I`: `wcMidW_wcGH` at the instance and the three words unmapped.
- `mid_IX`: the same at `ownGHXW` (`OwnMid.wcMidW_wcGHX`), so `res_Ig`/`tcb_Ig` hold at the self words.
- `res_Ig`, `tcb_Ig`: `H1GAH0V.res`, `.tcb` at the instance at any owned words `own` (level `W2Ig own`), given
  `mid_I`'s statement at `own`.
- `res_I`: `H1GAH0V.res` at the instance (`res_Ig` at `ownGH`).
- `tcb_I`: `H1GAH0V.tcb` at the instance (`tcb_Ig` at `ownGH`).
- `h0V_I`: `H1GAH0V` at the instance (with `WcRootI.wcWf_I`, `wcl_I`).
- `wcWf_IX`, `wcl_IX`, `h0V_IX`: `H1GAH0V.wcWf`, `.wcl` and `H1GAH0V` at the self words (level `W2Ig ownGHXW`;
  `WcW2.wcMainW_W2H` at `mid_IX`, `Wcl2X.wcl_W2GJ1HX`).

Every lemma is generic in `h2`'s memory side family `ms2` (the base's parameter; `H2Rt.ms2H` at the root's
`ownGH` instance, `H2RtX.ms2HX` at `ownGHXW`): the proofs read only the base's other fields.

## Unlike AArch64

- The callees' source facts are the box's (`QBH`, at the fence) rather than the clone's (`SBH`): the controls come
  from `WcW2.ctlH` (A64's `HelloH1A.spawnSrcH_ctl` and `WcW2.ctl_of_mid`), the placement from
  `SpawnPl.hplQ_GJ1H` (A64's `hpl_GJ1H`).
- The reserve returns to `.Lwc_main.x23` in `rARH R = R.callee (-136) (-40) 8` (A64's `.sp3`, `[-48, 0]` at
  `-144`), the second `scc_rt_alloc_tcb` to `.Lwc_main.x24` in `R.callee (-136) (-184) 8` (A64's `.sp4`,
  `[-192, 0]`); there is no alignment premise, the callee regions' bounds are `Region.callee_ok`'s.
- `res`/`tcb` are generic in the owned words (`res_Ig`, `tcb_Ig`; AArch64: at `ownGH`), their `SFactsSt2` a
  premise.
-/
import Spike.Lib.X64HelloWcRootI
import Spike.Lib.X64HelloWcMidWG
import Spike.Lib.X64HelloCalW2
import Spike.Lib.X64HelloCalPl
import Spike.Lib.X64HelloRootInst
import Spike.Lib.X64HelloRootHP
import Spike.Lib.X64HelloH2Rt
import Spike.Lib.X64WakeH1Rt
import Spike.Lib.X64WakeWfCalW1
import Spike.Lib.X64HelloOwnWcMidX
import Spike.Lib.X64HelloOwnBandX
import Spike.Lib.X64WakeOwnSW
import Spike.Lib.X64HelloWcl2X

namespace Spike.Lib.X64.HelloPh.CalRootI

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64.Flow.HelloWc (tH)
open Spike.Lib.X64HelloHMid (BoxPureH QBH slWsH)
open Spike.Lib.X64WakeLoadT (ls0T)
open Spike.Lib.X64.HelloPh.WcRootI (spw_mem tid_eq htid3_H bandTiH_of)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : Spike.Lib.PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "LB" => Spike.Lib.X64WakeLoadT.L0T (Ly).Λ

set_option hygiene false in
local notation "AW" => Spike.Lib.X64.WakeOD.arW hpw IH

variable {ms2 : Spike.Lib.X64Consumer.Lsize → WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat →
  List TermRun.Frame → Spike.Lib.MemSide isa}

set_option hygiene false in
/-- `h2`'s memory side family (the base's parameter). -/
local notation "MS2" => ms2

variable {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {t : UInt64}

set_option hygiene false in
/-- `h2`'s side at the box's labels, with main's thread pointer kept. -/
local notation "MS" => fun (B : HelloRootBase (Ly) (LB) (AW) (MS2)) =>
  Spike.Lib.X64.KeepTP.tpXa (MS2 B.ls l b n l' b' n' []) t

/-- **`wcMidW_wcGH` at the root instance** (its word premises from the layout and A13), with
`scc_rt_nthreads`, `scc_rt_pinned_next` and the second TCB's header `pinA + 104` unmapped under `F`. -/
theorem mid_I (B : HelloRootBase (Ly) (LB) (AW) (MS2))
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.X64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l R F J1 t) :
    Spike.Lib.X64.Flow.HelloWc.WcMidWH
        (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly))
          (ownGH (Ly) (ntA (Ly).lab)) s)
        (Spike.Lib.X64.PhRec.K (Ly) ⟨0, 0⟩) (Ly).exe (Ly).endPc R F F (MS B) J1 (QBH l' b' (slWsH l)) ∧
      (∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none) ∧
      (∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none) ∧
      (∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 104#64) 8 = none) := by
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
  have hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none := fun m h => hFr m h _ (Ly).pn_mem
  exact ⟨Spike.Lib.X64.HelloPh.WcMidWG.wcMidW_wcGH (Λ := (Ly).Λ) B.hp B.hlo B.hΛ B.hlab B.hsite hR
    (by omega) (by omega) hhi ⟨0, 0⟩ (Spike.Lib.X64.WakePh.CalWf.sepN_W hpw IH hA13)
    (Spike.Lib.X64.WakePh.CalWf.hmN_W hpw IH hA13 true) hunN (Spike.Lib.X64.HelloPh.H2Rt.bandSp3H_of hb)
    ⟨hs.pn_lock, hs.pn_freeN, hs.pn_next, hs.pn_a⟩ (e3 ▸ sp3.1) (Spike.Lib.X64.WakePh.LdFacts.hmP_W hpw IH)
    (e3' ▸ sp3.2) hunP hun.1 (bandTiH_of hb) ⟨tid_eq hpw i0 ▸ sp11.2, hun.2.1, htid3_H hpw i0 hA13⟩,
    hunN, hunP, hun.1⟩

/-- **`mid_I` at the self words** (`OwnMid.wcMidW_wcGHX` at the root instance): `WcMidWH` at
`ownGHXW (Ly) (ntA (Ly).lab)`, its word premises as `mid_I`'s, main's TCB word apart from the runtime's words
(`tcbSep_W`, `tcbM_ne_ntA_W`), the worker's (`tcbWH_notG_W`), wc_main's frames on the pool (`band320_of_boxH`). -/
theorem mid_IX (B : HelloRootBase (Ly) (LB) (AW) (MS2))
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.X64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l R F J1 t) :
    Spike.Lib.X64.Flow.HelloWc.WcMidWH
        (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly))
          (ownGHXW (Ly) (ntA (Ly).lab)) s)
        (Spike.Lib.X64.PhRec.K (Ly) ⟨0, 0⟩) (Ly).exe (Ly).endPc R F F (MS B) J1 (QBH l' b' (slWsH l)) ∧
      (∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none) ∧
      (∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none) ∧
      (∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 104#64) 8 = none) := by
  have hband := Spike.Lib.X64.HelloPh.OwnBand.band320_of_boxH hB
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
  have hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none := fun m h => hFr m h _ (Ly).pn_mem
  exact ⟨Spike.Lib.X64.HelloPh.OwnMid.wcMidW_wcGHX (Λ := (Ly).Λ) B.hp B.hlo B.hΛ B.hlab B.hsite
    (Spike.Lib.X64.WakePh.tcbSep_W hpw IH) (Spike.Lib.X64.WakePh.tcbM_ne_ntA_W hpw IH hA13)
    (Spike.Lib.X64.HelloPh.tcbWH_notG_W hpw IH hA13) hband hR (by omega) (by omega) hhi ⟨0, 0⟩
    (Spike.Lib.X64.WakePh.CalWf.sepN_W hpw IH hA13) (Spike.Lib.X64.WakePh.CalWf.hmN_W hpw IH hA13 true) hunN
    ⟨hs.pn_lock, hs.pn_freeN, hs.pn_next, hs.pn_a⟩ (e3 ▸ sp3.1) (Spike.Lib.X64.WakePh.LdFacts.hmP_W hpw IH)
    (e3' ▸ sp3.2) hunP hun.1 ⟨tid_eq hpw i0 ▸ sp11.2, hun.2.1, htid3_H hpw i0 hA13⟩,
    hunN, hunP, hun.1⟩

/-- **`H1GAH0V.res` at the root instance, at any owned words `own`**: `scc_rt_thread_reserve`'s nodes inside the
level `W2Ig own` at every box ghost (`Fresh2H`, `BoxPureH`, `GJ1RH`), from `CalW2.reserveW_W2H` at the empty
context, `lbl2H` and the twice extended sizes (see the module doc), given `mid_I`'s statement at `own` (`hmid`). -/
theorem res_Ig {own : Spike.Lib.X64Consumer.Own} (B : HelloRootBase (Ly) (LB) (AW) (MS2))
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hf : Fresh2H (AW) (LB) l b n l' b' n')
    (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.X64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l R F J1 t)
    (hmid : Spike.Lib.X64.Flow.HelloWc.WcMidWH
        (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) own s)
        (Spike.Lib.X64.PhRec.K (Ly) ⟨0, 0⟩) (Ly).exe (Ly).endPc R F F (MS B) J1 (QBH l' b' (slWsH l)) ∧
      (∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none) ∧
      (∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none) ∧
      (∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 104#64) 8 = none)) :
    Spike.Lib.X64.HelloPh.RootHP.ResV (Ly) (W2Ig own (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls) l b n l' b' n')
      (MS2 B.ls l b n l' b' n') l' b' (slWsH l) R F J1 t := by
  intro g hra nd
  have hM := hmid.1
  have hunN := hmid.2.1
  obtain ⟨hR, -, -, hRlo, hhi, -, -⟩ := hB
  by_cases hS : ∃ l1 A1, QBH l' b' (slWsH l) l1 A1 g.2
  · obtain ⟨l1, A1, hq⟩ := hS
    exact Spike.Lib.X64.HelloPh.CalW2.reserveW_W2H (ar := AW) (Dt := B.Dt) (Ctx := fun _ _ _ => False)
      (lbl := lbl2H (LB) l b l' b')
      (lsize := Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN (ls0T B.ls) l n) l' n')
      B.hp B.hlo B.hΛ B.hlab B.hsite
      (Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega))
      (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee]) ⟨g.1, 0#64, g.2⟩ hra
      (Spike.Lib.X64.HelloPh.WcW2.ctlH (p := Spike.Lib.X64HelloSrc.helloSrc) (.inl hq.2.2.1))
      (fun m h => hunN m h.1) (Spike.Lib.X64.WakePh.CalWf.hoffN_W hpw IH hA13)
      ((Spike.Lib.X64.Flow.HelloWc.WcMidWH.res hM).res g hra)
      (Spike.Lib.X64.HelloPh.CalPl.reserveW_placedH hR (by omega) (by omega)
        (Spike.Lib.X64.HelloPh.SpawnPl.hplQ_GJ1H hf.2.2.1 (Spike.Lib.X64.HelloPh.Box.hmt_H hpw i0 hf.1) hG.1)) nd
  · refine Spike.Lib.X64.WakePh.CalWf.reserveW_vac (fun m hm => hS ?_) nd
    obtain ⟨_, _, _, _, c, _, ⟨⟨l1, A1, _, hq⟩, _⟩, hE, _⟩ := hm
    exact ⟨l1, A1, by rw [← show c = g.2 from hE.1]; exact hq⟩

/-- **`H1GAH0V.res` at the root instance**: `res_Ig` at `ownGH` (`mid_I`). -/
theorem res_I (B : HelloRootBase (Ly) (LB) (AW) (MS2))
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hf : Fresh2H (AW) (LB) l b n l' b' n')
    (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.X64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l R F J1 t) :
    Spike.Lib.X64.HelloPh.RootHP.ResV (Ly) (W2I (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls) l b n l' b' n')
      (MS2 B.ls l b n l' b' n') l' b' (slWsH l) R F J1 t :=
  res_Ig hpw i0 B hA13 hf hB hG (mid_I hpw i0 (n := n) (l' := l') (b' := b') B hA13 hB hG)

/-- **`H1GAH0V.tcb` at the root instance, at any owned words `own`**: the second `scc_rt_alloc_tcb`'s nodes inside
the level `W2Ig own` at every box ghost and every ghost of `MidG`, `FrMGH`, from `CalW2.tcbWG_W2H` at the empty
context, `lbl2H` and the twice extended sizes (see the module doc), given `mid_I`'s statement at `own` (`hmid`). -/
theorem tcb_Ig {own : Spike.Lib.X64Consumer.Own} (B : HelloRootBase (Ly) (LB) (AW) (MS2))
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hf : Fresh2H (AW) (LB) l b n l' b' n')
    (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.X64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l R F J1 t)
    (hmid : Spike.Lib.X64.Flow.HelloWc.WcMidWH
        (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) own s)
        (Spike.Lib.X64.PhRec.K (Ly) ⟨0, 0⟩) (Ly).exe (Ly).endPc R F F (MS B) J1 (QBH l' b' (slWsH l)) ∧
      (∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none) ∧
      (∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none) ∧
      (∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 104#64) 8 = none)) :
    Spike.Lib.X64.HelloPh.RootHP.TcbV (Ly) (W2Ig own (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls) l b n l' b' n') l' b'
      (slWsH l) R F J1 := by
  intro c0 sl me cA fr hMG g hra
  have hM := hmid.1
  obtain ⟨-, hunP, hunH⟩ := hmid.2
  obtain ⟨hR, -, -, hRlo, hhi, -, -⟩ := hB
  have e3' : (Ly).pinA + BitVec.ofNat 64 (80 + 8 * 3) = (Ly).pinA + 104#64 := rfl
  obtain ⟨_, _, hq, -⟩ := hMG.1
  exact Spike.Lib.X64.HelloPh.CalW2.tcbWG_W2H (ar := AW) (Dt := B.Dt) (Ctx := fun _ _ _ => False)
    (lbl := lbl2H (LB) l b l' b')
    (lsize := Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN (ls0T B.ls) l n) l' n')
    B.hp B.hlo B.hΛ B.hlab B.hsite (Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega))
    (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee]) g c0 hra
    (Spike.Lib.X64.HelloPh.WcW2.ctlH (p := Spike.Lib.X64HelloSrc.helloSrc) (.inl hq.2.2.1))
    (fun m h => hunP m h.1) (Spike.Lib.X64.WakePh.CalWf.hoffP_W hpw IH) (fun m h => hunH m h.1)
    (e3' ▸ Spike.Lib.X64.HelloPh.H2Rt.hoffSp_H hpw IH hA13 (spw_mem hpw i0 (j := 3) (by decide)))
    ((Spike.Lib.X64.Flow.HelloWc.WcMidWH.sp3 hM c0 sl me cA fr hMG).tcb g hra)
    (fun nd => Spike.Lib.X64.HelloPh.CalPl.tcbWG_placedH hR (by omega) (by omega)
      (Spike.Lib.X64.HelloPh.SpawnPl.hplQ_GJ1H hf.2.2.1 (Spike.Lib.X64.HelloPh.Box.hmt_H hpw i0 hf.1) hG.1) hMG nd)

/-- **`H1GAH0V.tcb` at the root instance**: `tcb_Ig` at `ownGH` (`mid_I`). -/
theorem tcb_I (B : HelloRootBase (Ly) (LB) (AW) (MS2))
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hf : Fresh2H (AW) (LB) l b n l' b' n')
    (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.X64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l R F J1 t) :
    Spike.Lib.X64.HelloPh.RootHP.TcbV (Ly) (W2I (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls) l b n l' b' n') l' b'
      (slWsH l) R F J1 :=
  tcb_Ig hpw i0 B hA13 hf hB hG (mid_I hpw i0 (n := n) (l' := l') (b' := b') B hA13 hB hG)

/-- **`H1GAH0V` at the root instance, inhabited**: the root's open premise at every box ghost, from
`WcRootI.wcWf_I`, `res_I`, `tcb_I`, `WcRootI.wcl_I`; its residual premises are the instance's (`HelloRootBase`, A13's
data part) and the box ghost's (`Fresh2H`, `BoxPureH`, `GJ1RH`). -/
theorem h0V_I (B : HelloRootBase (Ly) (LB) (AW) (MS2))
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hf : Fresh2H (AW) (LB) l b n l' b' n')
    (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.X64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l R F J1 t) :
    Spike.Lib.X64.HelloPh.RootHP.H1GAH0V (Ly) (W2I (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls) l b n l' b' n') (WcI (Ly))
      (MS2 B.ls l b n l' b' n') l' b' (slWsH l) R F J1 t :=
  ⟨Spike.Lib.X64.HelloPh.WcRootI.wcWf_I hpw i0 B hA13 hf hB hG, res_I hpw i0 B hA13 hf hB hG,
    tcb_I hpw i0 B hA13 hf hB hG, Spike.Lib.X64.HelloPh.WcRootI.wcl_I hpw i0 B hf hB hG⟩

set_option hygiene false in
/-- main's owned words with the self words. -/
local notation "OX" => ownGHXW (Ly) (ntA (Ly).lab)

/-- **`H1GAH0V.wcWf` at the root instance at the self words**: `WcW2.wcMainW_W2H` at `ownGHXW` from `mid_IX`'s
`WcMidWH`, the placement `WcPl2.wcMainW_plGJ1H` as `WcRootI.wcWf_I`'s. -/
theorem wcWf_IX (B : HelloRootBase (Ly) (LB) (AW) (MS2))
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hf : Fresh2H (AW) (LB) l b n l' b' n')
    (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.X64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l R F J1 t) :
    Spike.Lib.X64.Flow.HelloWc.WcMainWH
      (fun s c => W2Ig (OX) (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls) l b n l' b' n' s c [])
      (fun _ _ => False) (Ly).exe (Ly).endPc R F F (MS B) J1 (QBH l' b' (slWsH l)) := by
  have hmid := mid_IX hpw i0 (n := n) (l' := l') (b' := b') B hA13 hB hG
  obtain ⟨hR, -, -, hRlo, hhi, hb, -⟩ := hB
  have hwn := Spike.Lib.X64.HelloPh.HelloRootBase.wn_GJ1RH hpw i0 hG
  have hA := Spike.Lib.X64.WakePh.H1Rt.a13_facts hpw IH hA13
  have hS : ∀ m, F m → ∀ x ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA, Mem.loadInt m.dmem x 8 = none :=
    fun m h x hx => hwn m h x fun j hj => (hA.2.1 x hx j hj).elim (fun h => .inr (.inl h)) fun h => .inr (.inr h)
  have hun := Spike.Lib.X64.HelloPh.H2Rt.hunSp_H hpw IH hS
  exact Spike.Lib.X64.HelloPh.WcW2.wcMainW_W2H (own := OX) (ar := AW) (Dt := B.Dt) (Ctx := fun _ _ _ => False)
    (lbl := lbl2H (LB) l b l' b')
    (lsize := Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN (ls0T B.ls) l n) l' n')
    B.hp B.hlo B.hΛ B.hlab B.hsite hR (by omega) hhi hmid.1
    (Spike.Lib.X64.HelloPh.WcPl2.wcMainW_plGJ1H (by omega) (by omega) hf.2.2.1
      (Spike.Lib.X64.HelloPh.Box.hmt_H hpw i0 hf.1) hG.1)
    hun.2.1 (Spike.Lib.X64.HelloPh.H2Rt.hoff56_H hpw IH hA13)

/-- **`H1GAH0V.wcl` at the root instance at the self words**: `Wcl2X.wcl_W2GJ1HX` as `WcRootI.wcl_I`'s
`wcl_W2GJ1H`, main's TCB word apart from the runtime's words (`tcbSep_W`, `tcbM_ne_ntA_W`), the worker's
(`tcbWH_notG_W`), the frames on the pool (`band320_of_boxH`). -/
theorem wcl_IX (B : HelloRootBase (Ly) (LB) (AW) (MS2))
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hf : Fresh2H (AW) (LB) l b n l' b' n')
    (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.X64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l R F J1 t) :
    ∀ s c sl me cA fr, Spike.Lib.X64.At (Ly).exe (Ly).endPc R F
      (Spike.Lib.X64.HelloPh.WcSp6.wcNSH (Ly).lab c (tH (Ly).lab) (Spike.Lib.X64.Flow.WakeWc.kOf (Ly).lab) sl me
        cA fr) s c →
      Spike.Lib.X64HelloMainPreSrc.SpawnSrcH l' (slWsH l) c → cA.toNat = b' →
      Spike.Lib.X64.Flow.HelloWc.FrMGH J1 fr sl me →
      Spike.Lib.X64.Flow.Ret0.StackM (Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab) s.st.1 →
      W2Ig (OX) (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls) l b n l' b' n' s c [] ∧ WcI (Ly) s c := by
  have hband := Spike.Lib.X64.HelloPh.OwnBand.band320_of_boxH hB
  obtain ⟨-, -, -, hRlo, hhi, -⟩ := hB
  exact Spike.Lib.X64.HelloPh.Wcl2X.wcl_W2GJ1HX (ar := AW) (Dt := B.Dt) (Ctx := fun _ _ _ => False)
    (lsize := Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN (ls0T B.ls) l n) l' n')
    B.hp B.hlo B.hΛ B.hlab B.hsite (Spike.Lib.X64.WakePh.tcbSep_W hpw IH)
    (Spike.Lib.X64.WakePh.tcbM_ne_ntA_W hpw IH hA13) (Spike.Lib.X64.HelloPh.tcbWH_notG_W hpw IH hA13)
    (Spike.Lib.X64.WakePh.OwnMid.bandOnP_mono hband (by omega) (by omega)) (by omega) (by omega) hf.2.2.1
    (Spike.Lib.X64.HelloPh.Box.hmt_H hpw i0 hf.1) hG.1

/-- **`H1GAH0V` at the root instance at the self words** (level `W2Ig ownGHXW`): `wcWf_IX`, `res_Ig`/`tcb_Ig`
at `mid_IX`, `wcl_IX`. -/
theorem h0V_IX (B : HelloRootBase (Ly) (LB) (AW) (MS2))
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hf : Fresh2H (AW) (LB) l b n l' b' n')
    (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.X64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l R F J1 t) :
    Spike.Lib.X64.HelloPh.RootHP.H1GAH0V (Ly) (W2Ig (OX) (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls) l b n l' b' n')
      (WcI (Ly)) (MS2 B.ls l b n l' b' n') l' b' (slWsH l) R F J1 t :=
  ⟨wcWf_IX hpw i0 B hA13 hf hB hG,
    res_Ig hpw i0 B hA13 hf hB hG (mid_IX hpw i0 (n := n) (l' := l') (b' := b') B hA13 hB hG),
    tcb_Ig hpw i0 B hA13 hf hB hG (mid_IX hpw i0 (n := n) (l' := l') (b' := b') B hA13 hB hG),
    wcl_IX hpw i0 B hA13 hf hB hG⟩

end Inst

end Spike.Lib.X64.HelloPh.CalRootI

/-- info: 'Spike.Lib.X64.HelloPh.CalRootI.mid_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalRootI.mid_I

/-- info: 'Spike.Lib.X64.HelloPh.CalRootI.mid_IX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalRootI.mid_IX

/-- info: 'Spike.Lib.X64.HelloPh.CalRootI.res_Ig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalRootI.res_Ig

/-- info: 'Spike.Lib.X64.HelloPh.CalRootI.tcb_Ig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalRootI.tcb_Ig

/-- info: 'Spike.Lib.X64.HelloPh.CalRootI.res_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalRootI.res_I

/-- info: 'Spike.Lib.X64.HelloPh.CalRootI.tcb_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalRootI.tcb_I

/-- info: 'Spike.Lib.X64.HelloPh.CalRootI.h0V_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalRootI.h0V_I

/-- info: 'Spike.Lib.X64.HelloPh.CalRootI.wcWf_IX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalRootI.wcWf_IX

/-- info: 'Spike.Lib.X64.HelloPh.CalRootI.wcl_IX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalRootI.wcl_IX

/-- info: 'Spike.Lib.X64.HelloPh.CalRootI.h0V_IX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalRootI.h0V_IX
