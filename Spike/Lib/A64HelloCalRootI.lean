/-
**hello's `wc_main` callee fields of the root's open premise at the instance** (AArch64; rows hP-res, hP-tcb):
`RootHP.H1GAH0V`'s `res` and `tcb` at the root instance's choices (`HelloRootBase` at `PlaceW`'s
layout, the start's labels `L0T`, the arena `arW`, `h2`'s side `H2Rt.ms2H`), at every box ghost `h0` quantifies
over, at the level `W2I … l b n l' b' n'` (as `WcRootI.wcWf_I`, `wcl_I`).

The callees' nodes are `CalW2.reserveW_W2H` / `tcbWG_W2H` inside `RootWX.W2H` at the empty context, `lbl2H` and the
twice extended sizes: their `SFactsSt2` at `ownGH` from `WcMidWG.wcMidW_wcGH` (`res`, `sp3`'s `tcb`), their
placement from `CalPl.reserveW_placedH` / `tcbWG_placedH` at `SpawnPl.hpl_GJ1H`, the controls from main's source
(`HelloH1A.spawnSrcH_ctl`; the reserve's frame condition is empty at a control off the source,
`CalWf.reserveW_vac`), the counters' and the header's words unmapped under the box ghost's frame condition
(`HelloRootBase.wn_GJ1RH`, as in `wcWf_I`) and off the arena (`CalWf.hoffN_W`, `CalWf.hoffP_W`, `H2Rt.hoffSp_H`
at spawn word `3`).

- `mid_I`: `wcMidW_wcGH` at the instance and the three words unmapped.
- `res_I`: `H1GAH0V.res` at the instance (row hP-res).
- `tcb_I`: `H1GAH0V.tcb` at the instance (row hP-tcb).
- `h0V_I`: `H1GAH0V` at the instance (with `WcRootI.wcWf_I`, `wcl_I`).
-/
import Spike.Lib.A64HelloWcRootI
import Spike.Lib.A64HelloCalW2
import Spike.Lib.A64HelloCalPl
import Spike.Lib.A64WakeWfCalW1

namespace Spike.Lib.A64.HelloPh.CalRootI

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Spike.Lib.A64.Flow.HelloWc (tH tcb2QH rNH rARH ResCtxH TcbCtxH wcNCH FrMGH)
open Spike.Lib.A64.Flow.WakeWc (MidG)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.HelloHMid (BoxPureH SBH QBH slWsH)
open Spike.Lib.WakeLoadT (ls0T)
open Spike.Lib.A64.HelloPh.WcRootI (spw_mem tid_eq htid3_H bandTiH_of)

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

variable {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} {t : UInt64}

set_option hygiene false in
/-- `h2`'s side at the box's labels, with main's thread pointer kept. -/
local notation "MS" => fun (B : HelloRootBase (Ly) (LB) (AW) (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E))
  => Spike.Lib.A64.KeepTP.tpXa (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E B.ls l b n l' b' n' []) t

/-- **`wcMidW_wcGH` at the root instance** (its word premises from the layout, as in `wcWf_I`), with
`scc_rt_nthreads`, `scc_rt_pinned_next` and the second TCB's header `pinA + 136` unmapped under `F`. -/
theorem mid_I (B : HelloRootBase (Ly) (LB) (AW) (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E))
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.A64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l R F J1 t) :
    Spike.Lib.A64.Flow.HelloWc.WcMidWH
        (fun s _ => Spike.Lib.A64ConsumerA.SFactsSt2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) (ownGH (Ly) (ntA (Ly).lab)) s)
        (Spike.Lib.A64.PhRec.K (Ly) ⟨0, 0⟩) (Ly).exe (Ly).endPc R F F (MS B) J1 (SBH l' b' (slWsH l))
        (QBH l' b' (slWsH l)) ∧
      (∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none) ∧
      (∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none) ∧
      (∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 136#64) 8 = none) := by
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
  have e3 : (Ly).pinA + BitVec.ofNat 64 (112 + 8 * 3) = (Ly).pinA + 112#64 + 24#64 := by
    rw [BitVec.add_assoc]; rfl
  have e3' : (Ly).pinA + BitVec.ofNat 64 (112 + 8 * 3) = (Ly).pinA + 136#64 := rfl
  have hs := B.hs
  have hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none := fun m h => hFr m h _ (Ly).pn_mem
  exact ⟨Spike.Lib.A64.HelloPh.WcMidWG.wcMidW_wcGH (Λ := (Ly).Λ) B.hp B.hlo B.hΛ B.hlab B.hsite hR hal (by omega)
    hhi ⟨0, 0⟩ (Spike.Lib.A64.WakePh.CalWf.sepN_W hpw IH hA13) (Spike.Lib.A64.WakePh.CalWf.hmN_W hpw IH hA13 true)
    hunN (Spike.Lib.A64.HelloPh.H2Rt.bandSp3H_of hb) ⟨hs.pn_lock, hs.pn_freeN, hs.pn_next, hs.pn_a⟩ (e3 ▸ sp3.1)
    (Spike.Lib.A64.WakePh.LdFacts.hmP_W hpw IH) (e3' ▸ sp3.2) hunP hun.1 (bandTiH_of hb)
    ⟨tid_eq hpw i0 ▸ sp11.2, hun.2.1, htid3_H hpw i0 hA13⟩, hunN, hunP, hun.1⟩

/-- (row hP-res) **`H1GAH0V.res` at the root instance**: `scc_rt_thread_reserve`'s nodes inside the level `W2I`
at every box ghost (`Fresh2H`, `BoxPureH`, `GJ1RH`), from `CalW2.reserveW_W2H` at the empty context, `lbl2H` and
the twice extended sizes (see the module doc). -/
theorem res_I (B : HelloRootBase (Ly) (LB) (AW) (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E))
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) (hf : Fresh2H (AW) (LB) l b n l' b' n')
    (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.A64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l R F J1 t) :
    ∀ g : Spike.Lib.A64.Flow.Reserve.G × Spike.Lib.Ctl, g.1.ra = ((Ly).lab ".L22_wc_main.sp3").toBitVec →
      ∀ nd, Spike.Lib.A64.Rt.Reserve.ReserveW
        (fun s c => W2I (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls) l b n l' b' n' s c []) (fun _ _ => False)
        (Ly).exe (Ly).endPc (rARH R)
        (fun m => F m ∧ CallerCells R (-144) (-48) 0 m ∧ ResCtxH (Ly).lab R
          (rNH (MS B) (Ly).lab J1 (SBH l' b' (slWsH l)) (QBH l' b' (slWsH l)) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd := by
  intro g hra nd
  have hmid := mid_I hpw i0 E (n := n) (l' := l') (b' := b') B hA13 hB hG
  have hM := hmid.1
  have hunN := hmid.2.1
  obtain ⟨hR, hal, -, hRlo, hhi, -, -⟩ := hB
  by_cases hS : ∃ l1 A1, SBH l' b' (slWsH l) l1 A1 g.2
  · obtain ⟨l1, A1, hs1⟩ := hS
    obtain ⟨hR', hal'⟩ := Spike.Lib.A64.Rt.StartU.callee_facts (kc := -144) (lo' := -48) hR hal
      (by omega) (by decide) (by omega) (by decide)
    exact Spike.Lib.A64.HelloPh.CalW2.reserveW_W2H (ar := AW) (Dt := B.Dt) (Ctx := fun _ _ _ => False)
      (lbl := lbl2H (LB) l b l' b')
      (lsize := Spike.Lib.A64ConsumerA.updN (Spike.Lib.A64ConsumerA.updN (ls0T B.ls) l n) l' n')
      B.hp B.hlo B.hΛ B.hlab B.hsite hR' hal' (by simp [Spike.Lib.Region.callee])
      (by simp [Spike.Lib.Region.callee]) ⟨g.1, 0#64, g.2⟩ hra (Spike.Lib.HelloH1A.spawnSrcH_ctl hs1.2.2)
      (fun m h => hunN m h.1) (Spike.Lib.A64.WakePh.CalWf.hoffN_W hpw IH hA13)
      ((Spike.Lib.A64.Flow.HelloWc.WcMidWH.res hM).res g hra)
      (Spike.Lib.A64.HelloPh.CalPl.reserveW_placedH hR (by omega) hhi
        (Spike.Lib.A64.HelloPh.SpawnPl.hpl_GJ1H hf.2.2.1 (Spike.Lib.A64.HelloPh.Box.hmt_H hpw i0 hf.1) hG.1)) nd
  · refine Spike.Lib.A64.WakePh.CalWf.reserveW_vac (fun m hm => hS ?_) nd
    obtain ⟨_, _, _, _, c, _, ⟨⟨l1, A1, hs1, _⟩, _⟩, hE, _⟩ := hm
    exact ⟨l1, A1, by rw [← show c = g.2 from hE.1]; exact hs1⟩

/-- (row hP-tcb) **`H1GAH0V.tcb` at the root instance**: the second `scc_rt_alloc_tcb`'s nodes inside the level
`W2I` at every box ghost and every ghost of `MidG`, `FrMGH`, from `CalW2.tcbWG_W2H` at the empty context, `lbl2H`
and the twice extended sizes (see the module doc). -/
theorem tcb_I (B : HelloRootBase (Ly) (LB) (AW) (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E))
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) (hf : Fresh2H (AW) (LB) l b n l' b' n')
    (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.A64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l R F J1 t) :
    ∀ c0 sl me cA fr, MidG (SBH l' b' (slWsH l)) c0 cA ∧ FrMGH J1 fr sl me →
      ∀ g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G, g.ra = ((Ly).lab ".L22_wc_main.sp4").toBitVec →
      ∀ nd, Spike.Lib.A64.Rt.TcbWG
        (fun s c => W2I (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls) l b n l' b' n' s c []) (fun _ _ => False)
        (Ly).exe (Ly).endPc (R.callee (-144) (-192) 0)
        (fun mm => F mm ∧ CallerCells R (-144) (-192) 0 mm ∧
          TcbCtxH (Ly).lab R (wcNCH (Ly).lab c0 sl me cA fr).J c0 g mm)
        (tcb2QH g c0) nd := by
  intro c0 sl me cA fr hMG g hra
  have hmid := mid_I hpw i0 E (n := n) (l' := l') (b' := b') B hA13 hB hG
  have hM := hmid.1
  obtain ⟨-, hunP, hunH⟩ := hmid.2
  obtain ⟨hR, hal, -, hRlo, hhi, -, -⟩ := hB
  obtain ⟨hR', hal'⟩ := Spike.Lib.A64.Rt.StartU.callee_facts (kc := -144) (lo' := -192) hR hal
    (by omega) (by decide) (by omega) (by decide)
  have e3' : (Ly).pinA + BitVec.ofNat 64 (112 + 8 * 3) = (Ly).pinA + 136#64 := rfl
  exact Spike.Lib.A64.HelloPh.CalW2.tcbWG_W2H (ar := AW) (Dt := B.Dt) (Ctx := fun _ _ _ => False)
    (lbl := lbl2H (LB) l b l' b')
    (lsize := Spike.Lib.A64ConsumerA.updN (Spike.Lib.A64ConsumerA.updN (ls0T B.ls) l n) l' n')
    B.hp B.hlo B.hΛ B.hlab B.hsite hR' hal' (by show (-192 : Int) ≤ -192; omega) (by show (0 : Int) ≤ 0; omega)
    g c0 hra (Spike.Lib.A64.HelloPh.WcW2.ctl_of_mid hMG.1 c0 rfl) (fun m h => hunP m h.1)
    (Spike.Lib.A64.WakePh.CalWf.hoffP_W hpw IH) (fun m h => hunH m h.1)
    (e3' ▸ Spike.Lib.A64.HelloPh.H2Rt.hoffSp_H hpw IH hA13 (spw_mem hpw i0 (j := 3) (by decide)))
    ((Spike.Lib.A64.Flow.HelloWc.WcMidWH.sp3 hM c0 sl me cA fr hMG).tcb g hra)
    (fun nd => Spike.Lib.A64.HelloPh.CalPl.tcbWG_placedH hR (by omega) hhi
      (Spike.Lib.A64.HelloPh.SpawnPl.hpl_GJ1H hf.2.2.1 (Spike.Lib.A64.HelloPh.Box.hmt_H hpw i0 hf.1) hG.1) hMG nd)

/-- **`H1GAH0V` at the root instance, inhabited** (rows hP-wcWf, hP-wcl, hP-res, hP-tcb together): the root's open
premise at every box ghost, from `WcRootI.wcWf_I`, `res_I`, `tcb_I`, `WcRootI.wcl_I`; its residual premises are
the instance's (`HelloRootBase`, A13's data part) and the box ghost's (`Fresh2H`, `BoxPureH`, `GJ1RH`). -/
theorem h0V_I (B : HelloRootBase (Ly) (LB) (AW) (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E))
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) (hf : Fresh2H (AW) (LB) l b n l' b' n')
    (hB : BoxPureH (Ly) B.F0 n' R F J1 t)
    (hG : Spike.Lib.A64.HelloPh.RootHP.GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l R F J1 t) :
    Spike.Lib.A64.HelloPh.RootHP.H1GAH0V (Ly) (W2I (Ly) (AW) B.Dt B.Ctx (LB) (ls0T B.ls) l b n l' b' n') (WcI (Ly))
      (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hpw IH E B.ls l b n l' b' n') l' b' (slWsH l) R F J1 t :=
  ⟨Spike.Lib.A64.HelloPh.WcRootI.wcWf_I hpw i0 E B hA13 hf hB hG, res_I hpw i0 E B hA13 hf hB hG,
    tcb_I hpw i0 E B hA13 hf hB hG, Spike.Lib.A64.HelloPh.WcRootI.wcl_I hpw i0 E B hf hB hG⟩

end Inst

end Spike.Lib.A64.HelloPh.CalRootI

/-- info: 'Spike.Lib.A64.HelloPh.CalRootI.mid_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CalRootI.mid_I

/-- info: 'Spike.Lib.A64.HelloPh.CalRootI.res_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CalRootI.res_I

/-- info: 'Spike.Lib.A64.HelloPh.CalRootI.tcb_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CalRootI.tcb_I

/-- info: 'Spike.Lib.A64.HelloPh.CalRootI.h0V_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CalRootI.h0V_I
